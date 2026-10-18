import Leanux.Proofs.WG.RetirementSecurity.TxQueuedRetention

/-! Retirement and refusal frames retain the actual queued owners of live
or active encryption. Only packet IDs outside those aliases may be freed or
published by a different batch. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem crypt_items_eq (same : TxRing.nativeCell v = TxRing.nativeCell w) :
    txCryptItems v = txCryptItems w := by
  have mapped := congrArg (fun cell : Option (Nat × PtrRing (List SkbId)) =>
    (cell.map fun pair => pair.2.items).getD []) same
  simpa only [txCryptItems,TxRing.nativeCell,Option.map_map,Function.comp_def] using mapped

theorem TxQueuedBatch.queues (owned : TxQueuedBatch w items)
    (same : handoffTxView v = handoffTxView w) : TxQueuedBatch v items := by
  obtain ⟨pid,p,found,member⟩ := owned
  have point : handoffTxView w pid = some p.txQueue.all := by
    simpa [handoffTxView,peerAt] using congrArg (Option.map (fun p => p.txQueue.all)) found
  rw [← same] at point
  obtain ⟨q,resident,queue⟩ := Option.map_eq_some_iff.mp point
  exact ⟨pid,q,resident,queue.symm ▸ member⟩

theorem TxCryptInventory.frame (crypt : TxCryptInventory active w)
    (ring : TxRing.nativeCell v = TxRing.nativeCell w)
    (owners : ∀ items, TxQueuedBatch w items → TxQueuedBatch v items)
    (marks : ∀ items ∈ txCryptItems w ++ active, ∃ first,
      items.head? = some first ∧ TxDisposition.HeadState first .uncrypted v) :
    TxCryptInventory active v := by
  have live := crypt_items_eq ring
  refine ⟨TxDisposition.LiveFrontier.physical_transport ring crypt.physical,?_,?_,?_⟩
  · simpa only [live] using crypt.unique
  · intro items member
    rw [live] at member
    exact owners items (crypt.owners items member)
  · simpa only [live] using marks

theorem TxCryptInventory.frame_packets (crypt : TxCryptInventory active w)
    (ring : TxRing.nativeCell v = TxRing.nativeCell w)
    (owners : ∀ items, TxQueuedBatch w items → TxQueuedBatch v items)
    (packets : TxDisposition.txPackets v = TxDisposition.txPackets w) :
    TxCryptInventory active v := by
  apply crypt.frame ring owners
  intro items member
  simpa only [TxDisposition.HeadState,packets] using crypt.uncrypted items member

theorem TxCryptInventory.key_put (crypt : TxCryptInventory active w) (key : Option KeypairId)
    (now : Bool) (a b : Ambient)
    (run : ((keypairPut key now).run w).run a = .ok (((),v),b)) : TxCryptInventory active v := by
  apply crypt.frame_packets
    ((ProjectedAction.iff_run_ambient _ _ _).mp (TxRing.keypairPut_frame key now) w a () v b run)
  · intro items owned
    apply owned.queues
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp (keypairPut_protect key now) w a () v b run
    exact congrArg (fun fields => fields.2.2.1) same
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp (TxDisposition.keyPut_packets key now) w a () v b run

theorem TxCryptInventory.peer_put (crypt : TxCryptInventory active w) (pid : Option PeerId)
    (a b : Ambient)
    (run : ((peerPut pid).run w).run a = .ok (((),v),b)) : TxCryptInventory active v :=
  crypt.frame_packets
    ((ProjectedAction.iff_run_ambient _ _ _).mp (TxRing.peerPut_frame pid) w a () v b run)
    (fun _ owned => owned.peer_put pid a b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (TxDisposition.peerPut_packets pid) w a () v b run)

def CryptOutside (items : List SkbId) (active : List (List SkbId)) (w : WGWorld) : Prop :=
  ∀ id ∈ items, id ∉ (txCryptItems w ++ active).flatten

theorem CryptOutside.ring (outside : CryptOutside items active w)
    (same : TxRing.nativeCell v = TxRing.nativeCell w) : CryptOutside items active v := by
  simpa only [CryptOutside,crypt_items_eq same] using outside

theorem TxCryptInventory.local_outside (crypt : TxCryptInventory active w)
    (inventory : TxInventory (held :: locals) w) : CryptOutside held.items active w := by
  intro id member old
  obtain ⟨batch,aliased,contains⟩ := List.mem_flatten.mp old
  obtain ⟨pid,p,found,queued⟩ := crypt.owners batch aliased
  exact inventory.localsSeparate pid p found id (by simp [txLocalItems,member])
    (List.mem_flatten.mpr ⟨batch,queued,contains⟩)

theorem free_list_ring (items : List SkbId) : SameView TxRing.nativeCell (TxDisposition.freeList items) := by
  intro initial
  change Preserves (fun w => TxRing.nativeCell w = initial) _
  unfold TxDisposition.freeList
  apply preserves_bind
  · apply list_view_spec id (fun w => TxRing.nativeCell w = initial)
    intro packet state
    apply preserves_bind
    · unfold freeTxSkb
      apply hoare_liftSkb
      intro w d store before device
      simpa only [id_eq,TxRing.nativeCell,device,Option.map_some] using before
    · intro _
      exact preserves_pure _
  · intro _
    exact preserves_pure _

theorem TxCryptInventory.free_list (crypt : TxCryptInventory active w)
    (outside : CryptOutside items active w) (a b : Ambient)
    (run : ((TxDisposition.freeList items).run w).run a = .ok (((),v),b)) :
    TxCryptInventory active v := by
  apply crypt.frame ((ProjectedAction.iff_run_ambient _ _ _).mp (free_list_ring items) w a () v b run)
  · intro batch owned
    apply owned.queues
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp (freeTxList_protect items) w a () v b run
    exact congrArg (fun fields => fields.2.2.1) same
  · intro batch member
    obtain ⟨first,head,packet,resident,state⟩ := crypt.uncrypted batch member
    have apart : first ∉ items := fun fresh => outside first fresh
      (List.mem_flatten.mpr ⟨batch,member,List.mem_of_head? head⟩)
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (TxDisposition.MarkTransport.free_other first items apart) w a () v b run
    exact ⟨first,head,packet,same.trans resident,state⟩

theorem TxCryptInventory.publish_outside (crypt : TxCryptInventory active w)
    (outside : CryptOutside items active w) (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerTx items state).run w).run a = .ok (((),v),b)) :
    TxCryptInventory active v := by
  apply crypt.frame ((ProjectedAction.iff_run_ambient _ _ _).mp (TxRing.enqueuePeer_frame items state) w a () v b run)
  · intro batch owned
    apply owned.queues
    exact congrArg (fun fields => fields.2.2.1)
      ((ProjectedAction.iff_run_ambient _ _ _).mp (publication_protect items state) w a () v b run)
  · intro batch member
    obtain ⟨first,head,packet,resident,mark⟩ := crypt.uncrypted batch member
    have apart : first ∉ items := fun fresh => outside first fresh
      (List.mem_flatten.mpr ⟨batch,member,List.mem_of_head? head⟩)
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (TxDisposition.MarkTransport.publish_other first items state apart) w a () v b run
    exact ⟨first,head,packet,same.trans resident,mark⟩

theorem TxCryptInventory.cleanup (crypt : TxCryptInventory active w)
    (outside : CryptOutside items active w) (pid : PeerId) (first : SkbId) (a b : Ambient)
    (run : ((TxDisposition.cleanupSource pid items first).run w).run a = .ok (((),v),b)) :
    TxCryptInventory active v := by
  simp only [TxDisposition.cleanupSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨packet,u,c,readRun,_,t,e,keyRun,_,s,f,peerRun,freeRun⟩ := run
  obtain ⟨same,clock,_,_,_⟩ := Packets.getTxSkb_current first w u packet a c readRun
  subst u
  subst c
  have ht := crypt.key_put (some packet.keypair) false a e keyRun
  have outsideT := outside.ring ((ProjectedAction.iff_run_ambient _ _ _).mp
    (TxRing.keypairPut_frame (some packet.keypair) false) w a () t e keyRun)
  have hs := ht.peer_put (some pid) e f peerRun
  have outsideS := outsideT.ring ((ProjectedAction.iff_run_ambient _ _ _).mp
    (TxRing.peerPut_frame (some pid)) t e () s f peerRun)
  exact hs.free_list outsideS f b freeRun

end Leanux.Proofs.WG.RetirementSecurity
