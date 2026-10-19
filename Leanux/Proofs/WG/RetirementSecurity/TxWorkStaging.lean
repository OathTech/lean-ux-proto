import Leanux.Proofs.WG.RetirementSecurity.TxWorkStagingFrames

/-! Original staging preserves service for existing packets and obtains service
for newly allocated batches from the actual createData disposition. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem stage_submit (before : StageReady locals crypt tx w) (pid kid : Nat)
    (packets : List DataPacket) (a b : Ambient)
    (run : ((stagedSubmit pid kid packets).run w).run a=.ok (((),v),b)) :
    Obligations crypt tx v := by
  simp only [stagedSubmit,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,acquireRun,tail⟩:=run
  obtain ⟨d,k,owner,p,device,_,_,_,_,borrow⟩:=
    Affiliation.sendAcquire_certificate kid w u a c acquireRun
  obtain ⟨d',p',device',stored',_,same⟩:=borrow
  have devices:d'=d := Option.some.inj (device'.symm.trans device)
  subst d'
  have after:u.dev=some {d with peers:=d.peers.insert owner {p' with refcount:=p'.refcount+1}} :=
    congrArg WGStoreView.dev same
  have queues:handoffTxView u=handoffTxView w := by
    funext other
    by_cases equal:owner=other
    · subst other; simp [handoffTxView,after,device,stored']
    · simp [handoffTxView,after,device,Std.TreeMap.getElem?_insert,equal]
  have wire:TxRing.nativeCell u=TxRing.nativeCell w := by simp [TxRing.nativeCell,after,device]
  have service:Obligations crypt tx u := before.1.frame queues
    (by funext id; simp [TxDisposition.txPackets,after,device]) (crypt_items_eq wire)
    (by simp [queued,after,device])
  have bound:Packets.Inv u := by
    simpa only [Packets.Inv,Packets.snapshot,Packets.deviceStore,after,device] using before.2.1.1
  have shape:SameView ownershipPointView (Affiliation.sendAcquire kid) := by
    intro initial
    change Preserves (fun w=>ownershipPointView w=initial) _
    unfold Affiliation.sendAcquire
    repeat' first
      | (rx_retention_head peerGet; exact (peerGet_ownership _).wp (·=initial))
      | ownership_source_step initial
  have inventory:=before.2.1.2.points
    ((ProjectedAction.iff_run_ambient _ _ _).mp shape w a () u c acquireRun)
  exact service.allocate_create inventory bound
    (TxDisposition.LiveFrontier.physical_transport wire before.2.2.physical) after pid packets c b
    (by simpa only [MaterialOrigin.bind_ok_ambient] using tail)

theorem stage_key_source (locals : List TxLocalBatch) (crypt : List (List SkbId))
    (tx : List PeerId) (pid kid : Nat) (packets : List WG.Packet) :
    Hoare (stagedKeySource pid kid packets) (StageReady locals crypt tx)
      (fun _=>Obligations crypt tx) := by
  let P:=StageReady locals crypt tx
  let Q:=Obligations crypt tx
  have getter:Preserves P (getKeypair kid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a key v b before run
    exact (KeyTimes.getKeypair_return kid w v key a b run).1 ▸ before
  have setter:=stage_set_key (locals:=locals) (crypt:=crypt) (tx:=tx)
  have expired:=fun date=>(branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp P
  have ecn:=fun pkt=>(ipTunnelEcnEncap_sameWGWorld pkt).wp P
  have out:=stage_no_key (locals:=locals) (crypt:=crypt) (tx:=tx) pid packets (some kid)
  have submitSpec (data : List DataPacket) : Hoare (stagedSubmit pid kid data) P (fun _=>Q) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact stage_submit before pid kid data a b run
  have weaken {α : Type} (action : WG.M α) (h : Preserves P action) : Hoare action P (fun _=>Q) :=
    hoare_consequence h (fun _ h=>h) (fun _ _ h=>h.1)
  have step {α β : Type} (action : WG.M α) (f : α→WG.M β)
      (R : β→WGWorld→Prop) (ha : Preserves P action)
      (hf : ∀x,Hoare (f x) P R) : Hoare (action>>=f) P R := hoare_bind action f ha hf
  unfold stagedKeySource
  change Hoare _ P (fun _=>Q)
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

theorem staged_service (before : StageReady locals crypt tx w) (pid : PeerId) (a b : Ambient)
    (run : ((sendStagedPackets pid).run w).run a=.ok (((),v),b)) : Obligations crypt tx v := by
  rw [←stagedFullSource_eq] at run
  simp only [stagedFullSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,empty,t,e,branchRun,tail⟩:=run
  obtain ⟨same,clock,d,device,stored⟩:=Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  have same:t=w := by cases branchRun; rfl
  subst t
  cases empty with
  | true=>simp only [ite_true] at tail; cases tail; exact before.1
  | false=>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,u,c,setRun,kp,t,f,getRun,missing,s,g,branchRun,tail⟩:=tail
    have after:u=replacePeer w d pid {p with staged:=[]} := by
      have equal:replacePeer w d pid {p with staged:=[]}=u ∧ e=c := by
        simpa [setPeer,modifyDev,replacePeer,device] using setRun
      exact equal.1.symm
    have queues:handoffTxView u=handoffTxView w :=
      ownership_points_queues (after ▸ ownershipPoint_replace device stored rfl)
    have wire:TxRing.nativeCell u=TxRing.nativeCell w := by simp [TxRing.nativeCell,after,replacePeer,device]
    have packets:TxDisposition.txPackets u=TxDisposition.txPackets w := by
      funext id; simp [TxDisposition.txPackets,after,replacePeer,device]
    have ready:StageReady locals crypt tx u := by
      refine ⟨before.1.frame queues packets (crypt_items_eq wire) ?_,?_,?_⟩
      · simp [queued,after,replacePeer,device]
      · rw [after]
        exact ⟨by simpa [Packets.Inv,Packets.snapshot,Packets.deviceStore,replacePeer,device] using before.2.1.1,
          before.2.1.2.exchange device stored _ (List.Perm.refl _)⟩
      · exact before.2.2.frame_packets wire (fun _ owned=>owned.queues queues) packets
    have acquired:=(hoare_iff_run_ambient _ _ _).mp
      (stage_key_get (locals:=locals) (crypt:=crypt) (tx:=tx) p.keypairCurrent) u c kp t f ready getRun
    have same:s=t := by cases branchRun; rfl
    subst s
    cases missing with
    | true=>
      simp only [ite_true] at tail
      exact ((hoare_iff_run_ambient _ _ _).mp (stage_no_key pid p.staged kp false) t g () v b acquired tail).1
    | false=>
      simp only [Bool.false_eq_true,ite_false] at tail
      cases kp with
      | none=>cases tail
      | some kid=>
        exact (hoare_iff_run_ambient _ _ _).mp (stage_key_source locals crypt tx pid kid p.staged)
          t g () v b acquired tail

end Leanux.Proofs.WG.RetirementSecurity.TxWork
