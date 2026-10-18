import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceStagingFrames

/-! Full native staging preserves uniqueness and residency of physical TX
occurrences. It derives fresh allocation separation from the packet frontier
and uses the actual createData disposition, including rejection cleanup. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do
open Queues.RxCredits StagingOccurrences

private theorem staging_read_key (kid : KeypairId) : Preserves (Ready locals) (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a k v b before run
  exact (KeyTimes.getKeypair_return kid w v k a b run).1 ▸ before

private theorem staging_set_key (kid : KeypairId) (key : Keypair) :
    Preserves (Ready locals) (setKeypair kid key) := by
  apply frame_ready
  · intro initial
    apply hoare_modify
    intro w before
    cases hd : w.dev <;>
      simpa only [geometry,Packets.snapshot,Packets.deviceStore,Queues.TxDisposition.txPackets,
        hd,Option.map_none,Option.map_some,Option.bind_none,Option.bind_some] using before
  · apply key_frame
    intro initial
    unfold setKeypair
    repeat' holder_prepare_step initial

theorem TxInventory.staged_submit (inventory : TxInventory locals w)
    (bounded : Packets.Inv w) (pid kid : Nat) (packets : List DataPacket)
    (a b : Ambient)
    (run : ((stagedSubmit pid kid packets).run w).run a = .ok (((),v),b)) :
    TxInventory locals v := by
  simp only [stagedSubmit,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,acquireRun,tail⟩ := run
  obtain ⟨d,k,owner,p,device,_,_,_,_,borrow⟩ :=
    Affiliation.sendAcquire_certificate kid w u a c acquireRun
  obtain ⟨d',p',device',_,_,same⟩ := borrow
  have devices : d' = d := Option.some.inj (device'.symm.trans device)
  subst d'
  have after : u.dev = some {d with peers := d.peers.insert owner {p' with refcount := p'.refcount + 1}} :=
    congrArg WGStoreView.dev same
  have frame : SameView ownershipPointView (Affiliation.sendAcquire kid) := by
    intro initial
    change Preserves (fun w => ownershipPointView w = initial) _
    unfold Affiliation.sendAcquire
    repeat' first
      | (rx_retention_head peerGet; exact (peerGet_ownership _).wp (· = initial))
      | ownership_source_step initial
  have hu := inventory.points ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a () u c acquireRun)
  have bu : Packets.Inv u := by
    simpa only [Packets.Inv,Packets.snapshot,Packets.deviceStore,after,device] using bounded
  exact hu.allocate_create bu after pid packets c b (by
    simpa only [MaterialOrigin.bind_ok_ambient] using tail)

/-- Original key checks and nonce loop precede the physical allocation cut.
Existing occurrences remain distinct through every normal refusal arm. -/
theorem staged_key_occurrences (locals : List TxLocalBatch) (pid kid : Nat)
    (packets : List WG.Packet) :
    Hoare (stagedKeySource pid kid packets) (Ready locals) (fun _ => TxInventory locals) := by
  let P := Ready locals
  have getter := staging_read_key (locals := locals) kid
  have setter := staging_set_key (locals := locals)
  have expired := fun date =>
    (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp P
  have ecn := fun pkt => (ipTunnelEcnEncap_sameWGWorld pkt).wp P
  have out := no_key_ready (locals := locals) pid packets (some kid)
  have submit (data : List DataPacket) :
      Hoare (stagedSubmit pid kid data) P (fun _ => TxInventory locals) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact before.2.staged_submit before.1 pid kid data a b run
  have weaken {α : Type} (action : WG.M α) (h : Preserves P action) :
      Hoare action P (fun _ => TxInventory locals) :=
    hoare_consequence h (fun _ h => h) (fun _ _ h => h.2)
  have step {α β : Type} (action : WG.M α) (f : α → WG.M β)
      (Q : β → WGWorld → Prop) (ha : Preserves P action)
      (hf : ∀ x, Hoare (f x) P Q) : Hoare (action >>= f) P Q := hoare_bind action f ha hf
  unfold stagedKeySource
  change Hoare _ P (fun _ => TxInventory locals)
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getKeypair; exact getter)
    | (index_material_head setKeypair; exact setter _ _)
    | (index_material_head branchExpired; exact expired _)
    | (index_material_head ipTunnelEcnEncap; exact ecn _)
    | (index_material_head stagedOutNokey; first | exact out _ | exact weaken _ (out _))
    | (index_material_head stagedSubmit; exact submit _)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | (index_material_head Pure.pure; first | exact preserves_pure _ | exact weaken _ (preserves_pure _))
    | (index_material_head Bind.bind; apply step)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem TxInventory.staged (inventory : TxInventory locals w) (bounded : Packets.Inv w)
    (pid : PeerId) (a b : Ambient)
    (run : ((sendStagedPackets pid).run w).run a = .ok (((),v),b)) : TxInventory locals v := by
  rw [← stagedFullSource_eq] at run
  simp only [stagedFullSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,empty,t,e,branchRun,tail⟩ := run
  obtain ⟨same,clock,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  have same : t = w := by cases branchRun; rfl
  subst t
  cases empty with
  | true => simp only [ite_true] at tail; cases tail; exact inventory
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,u,c,setRun,kp,t,f,getRun,missing,s,g,branchRun,tail⟩ := tail
    have after : u = replacePeer w d pid {p with staged := []} := by
      have equal : replacePeer w d pid {p with staged := []} = u ∧ e = c := by
        simpa [setPeer,modifyDev,replacePeer,device] using setRun
      exact equal.1.symm
    have hu : Ready locals u := by
      rw [after]
      exact ⟨by simpa [Packets.Inv,Packets.snapshot,Packets.deviceStore,replacePeer,device] using bounded,
        inventory.exchange device stored _ (List.Perm.refl _)⟩
    have ht := (hoare_iff_run_ambient _ _ _).mp (key_get_ready (locals := locals) p.keypairCurrent)
      u c kp t f hu getRun
    have same : s = t := by cases branchRun; rfl
    subst s
    cases missing with
    | true =>
      simp only [ite_true] at tail
      exact ((hoare_iff_run_ambient _ _ _).mp (no_key_ready pid p.staged kp false)
        t g () v b ht tail).2
    | false =>
      simp only [Bool.false_eq_true,ite_false] at tail
      cases kp with
      | none => cases tail
      | some kid =>
        exact (hoare_iff_run_ambient _ _ _).mp (staged_key_occurrences locals pid kid p.staged)
          t g () v b ht tail

end Leanux.Proofs.WG.RetirementSecurity
