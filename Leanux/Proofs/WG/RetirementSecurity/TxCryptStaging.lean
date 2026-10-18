import Leanux.Proofs.WG.RetirementSecurity.TxCryptStagingFrames

/-! Full original staged send transports physical and encryption-phase
inventories together. The actual nonce loop is passive for these projections;
fresh allocation and original creation perform the owning/alias transfers. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do Queues
open Queues.RxCredits

namespace CryptStaging
abbrev Ready (locals : List TxLocalBatch) (active : List (List SkbId)) (w : WGWorld) :=
  StagingOccurrences.Ready locals w ∧ TxCryptInventory active w
abbrev Kept (locals : List TxLocalBatch) (active : List (List SkbId)) (w : WGWorld) :=
  TxInventory locals w ∧ TxCryptInventory active w

private theorem join {action : WG.M α} (physical : Preserves (StagingOccurrences.Ready locals) action)
    (phase : Preserves (TxCryptInventory active) action) : Preserves (Ready locals active) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp physical w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp phase w a result v b before.2 run⟩

private theorem read_key (kid : KeypairId) : Preserves (Ready locals active) (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a k v b before run
  exact (KeyTimes.getKeypair_return kid w v k a b run).1 ▸ before

private theorem set_key (kid : KeypairId) (key : Keypair) :
    Preserves (Ready locals active) (setKeypair kid key) := by
  apply join
  · apply StagingOccurrences.frame_ready
    · intro initial
      apply hoare_modify
      intro w before
      cases hd : w.dev <;>
        simpa only [StagingOccurrences.geometry,Packets.snapshot,Packets.deviceStore,TxDisposition.txPackets,
          hd,Option.map_none,Option.map_some,Option.bind_none,Option.bind_some] using before
    · apply StagingOccurrences.key_frame
      intro initial
      unfold setKeypair
      repeat' holder_prepare_step initial
  · apply crypt_passive
    · intro initial
      change Preserves (fun w => txCryptWire w = initial) _
      unfold setKeypair
      repeat' crypt_wire_step initial
    · intro initial
      change Preserves (fun w => handoffTxView w = initial) _
      unfold setKeypair
      repeat' crypt_queue_step initial

private theorem no_key (pid : PeerId) (packets : List WG.Packet)
    (key : Option KeypairId) (invalid : Bool) :
    Preserves (Ready locals active) (stagedOutNokey pid packets key invalid) :=
  join (StagingOccurrences.no_key_ready pid packets key invalid) (crypt_no_key pid packets key invalid)

private theorem key_get (key : Option KeypairId) : Preserves (Ready locals active) (keypairGet key) :=
  join (StagingOccurrences.key_get_ready key) (crypt_key_get key)

theorem submit (before : Ready locals active w) (pid kid : Nat) (packets : List DataPacket)
    (a b : Ambient)
    (run : ((stagedSubmit pid kid packets).run w).run a = .ok (((),v),b)) :
    Kept locals active v := by
  have physical := before.1.2.staged_submit before.1.1 pid kid packets a b run
  simp only [stagedSubmit,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,acquireRun,tail⟩ := run
  obtain ⟨d,k,owner,p,device,_,_,_,_,borrow⟩ :=
    Affiliation.sendAcquire_certificate kid w u a c acquireRun
  obtain ⟨d',p',device',stored',_,same⟩ := borrow
  have devices : d' = d := Option.some.inj (device'.symm.trans device)
  subst d'
  have after : u.dev = some {d with peers := d.peers.insert owner {p' with refcount := p'.refcount + 1}} :=
    congrArg WGStoreView.dev same
  have phase : TxCryptInventory active u := by
    apply before.2.frame_packets
    · simp [TxRing.nativeCell,after,device]
    · intro items owned
      apply owned.queues
      funext other
      by_cases equal : owner = other
      · subst other; simp [handoffTxView,after,device,stored']
      · simp [handoffTxView,after,device,Std.TreeMap.getElem?_insert,equal]
    · funext id
      simp [TxDisposition.txPackets,after,device]
  have bounded : Packets.Inv u := by
    simpa only [Packets.Inv,Packets.snapshot,Packets.deviceStore,after,device] using before.1.1
  have shape : SameView ownershipPointView (Affiliation.sendAcquire kid) := by
    intro initial
    change Preserves (fun w => ownershipPointView w = initial) _
    unfold Affiliation.sendAcquire
    repeat' first
      | (rx_retention_head peerGet; exact (peerGet_ownership _).wp (· = initial))
      | ownership_source_step initial
  have inventory := before.1.2.points
    ((ProjectedAction.iff_run_ambient _ _ _).mp shape w a () u c acquireRun)
  exact ⟨physical,(allocate_create_occurrences inventory phase bounded after pid packets c b
    (by simpa only [MaterialOrigin.bind_ok_ambient] using tail)).2⟩

theorem key_source (locals : List TxLocalBatch) (active : List (List SkbId))
    (pid kid : Nat) (packets : List WG.Packet) :
    Hoare (stagedKeySource pid kid packets) (Ready locals active) (fun _ => Kept locals active) := by
  let P := Ready locals active
  let Q := Kept locals active
  have getter := read_key (locals := locals) (active := active) kid
  have setter := set_key (locals := locals) (active := active)
  have expired := fun date =>
    (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp P
  have ecn := fun pkt => (ipTunnelEcnEncap_sameWGWorld pkt).wp P
  have out := no_key (locals := locals) (active := active) pid packets (some kid)
  have submitSpec (data : List DataPacket) : Hoare (stagedSubmit pid kid data) P (fun _ => Q) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact submit before pid kid data a b run
  have weaken {α : Type} (action : WG.M α) (h : Preserves P action) : Hoare action P (fun _ => Q) :=
    hoare_consequence h (fun _ h => h) (fun _ _ h => ⟨h.1.2,h.2⟩)
  have step {α β : Type} (action : WG.M α) (f : α → WG.M β)
      (R : β → WGWorld → Prop) (ha : Preserves P action)
      (hf : ∀ x, Hoare (f x) P R) : Hoare (action >>= f) P R := hoare_bind action f ha hf
  unfold stagedKeySource
  change Hoare _ P (fun _ => Q)
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
    | (index_material_head stagedSubmit; exact submitSpec _)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | (index_material_head Pure.pure; first | exact preserves_pure _ | exact weaken _ (preserves_pure _))
    | (index_material_head Bind.bind; apply step)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem staged (before : Ready locals active w) (pid : PeerId) (a b : Ambient)
    (run : ((sendStagedPackets pid).run w).run a = .ok (((),v),b)) : Kept locals active v := by
  rw [← stagedFullSource_eq] at run
  simp only [stagedFullSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,empty,t,e,branchRun,tail⟩ := run
  obtain ⟨same,clock,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  have same : t = w := by cases branchRun; rfl
  subst t
  cases empty with
  | true => simp only [ite_true] at tail; cases tail; exact ⟨before.1.2,before.2⟩
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,u,c,setRun,kp,t,f,getRun,missing,s,g,branchRun,tail⟩ := tail
    have after : u = replacePeer w d pid {p with staged := []} := by
      have equal : replacePeer w d pid {p with staged := []} = u ∧ e = c := by
        simpa [setPeer,modifyDev,replacePeer,device] using setRun
      exact equal.1.symm
    have ready : Ready locals active u := by
      refine ⟨?_,?_⟩
      · rw [after]
        exact ⟨by simpa [Packets.Inv,Packets.snapshot,Packets.deviceStore,replacePeer,device] using before.1.1,
          before.1.2.exchange device stored _ (List.Perm.refl _)⟩
      · apply before.2.frame_packets
        · simp [TxRing.nativeCell,after,replacePeer,device]
        · intro items owned
          exact owned.queues (ownership_points_queues (after ▸ ownershipPoint_replace device stored rfl))
        · funext id
          simp [TxDisposition.txPackets,after,replacePeer,device]
    have acquired := (hoare_iff_run_ambient _ _ _).mp (key_get (locals := locals) (active := active) p.keypairCurrent)
      u c kp t f ready getRun
    have same : s = t := by cases branchRun; rfl
    subst s
    cases missing with
    | true =>
      simp only [ite_true] at tail
      have kept := (hoare_iff_run_ambient _ _ _).mp (no_key pid p.staged kp false)
        t g () v b acquired tail
      exact ⟨kept.1.2,kept.2⟩
    | false =>
      simp only [Bool.false_eq_true,ite_false] at tail
      cases kp with
      | none => cases tail
      | some kid =>
        exact (hoare_iff_run_ambient _ _ _).mp (key_source locals active pid kid p.staged)
          t g () v b acquired tail

end CryptStaging
end Leanux.Proofs.WG.RetirementSecurity
