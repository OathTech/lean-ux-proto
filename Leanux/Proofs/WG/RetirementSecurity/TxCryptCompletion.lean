import Leanux.Proofs.WG.RetirementSecurity.TxEncryptHolders

/-! Completion consumes an active encryption alias while retaining the
peer-owned packet occurrence until TX disposal. Other live/active batches
keep their UNCRYPTED heads through the selected bytes and state writes. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

def txCryptContext (w : WGWorld) := (TxRing.nativeCell w,fun pid => TxDisposition.txQueues w pid)

private theorem crypt_context_store {action : WG.M α} (same : SameWGStore action) :
    SameView txCryptContext action :=
  same.of_factor (fun store => txCryptContext {dev := store.dev}) txCryptContext (fun _ => rfl)

private theorem crypt_context_skb (action : SkbM α) : SameView txCryptContext (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro w d store before device
  simpa only [txCryptContext,TxRing.nativeCell,TxDisposition.txQueues,PeerBorrow.resident,
    PeerBorrow.view,PeerBorrow.outsidePeers,wgStoreView,device,Option.map_some,Option.bind_some] using before

theorem encrypt_tail_context (items : Option (List SkbId)) :
    SameView (fun w : World => txCryptContext w.wg) (RxWorkers.encryptStepTailSource items) := by
  intro initial
  let P := fun w : World => txCryptContext w.wg = initial
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : Leanux.M α) :=
    productAmbient_spec action P (fun _ _ hi => hi)
  have native {α : Type} (action : WG.M α) (same : SameView txCryptContext action) :
      Preserves P (monadLift action : Leanux.M α) :=
    (sameView_liftWG (fun w : World => txCryptContext w.wg) txCryptContext action same
      (fun _ _ _ hi => hi)).wp (· = initial)
  have readNative (id : SkbId) : SameWGStore (getTxSkb id) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg wgStoreView (Packets.getTxSkb_current id w v p a b run).1
  have read := fun id => native (getTxSkb id) (crypt_context_store (readNative id))
  have write (id : SkbId) (f : DataPacket → DataPacket) :
      Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) :=
    native (setTxSkb id f) (crypt_context_skb _)
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) :=
    ((encrypt_packet_store key pkt).of_factor (fun store => txCryptContext {dev := store.dev})
      (fun w : World => txCryptContext w.wg) (fun _ => rfl)).wp (· = initial)
  have publish (batch : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx batch state) : Leanux.M Unit) :=
    native _ ((TxRing.enqueuePeer_frame batch state).product (TxDisposition.publication_queues batch state))
  change Preserves P _
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]

/-- The complete selected native encryption continuation consumes only its
active alias. Its peer queue still owns the batch, and each other live or
active batch remains exclusively available to its own encryption selection. -/
theorem TxCryptInventory.complete (crypt : TxCryptInventory (items :: active) w.wg)
    (run : (RxWorkers.encryptStepTailSource (some items)).run w = .ok (result,v)) :
    TxCryptInventory active v.wg := by
  have context := (ProjectedAction.iff_run _ _ _).mp (encrypt_tail_context (some items)) w result v run
  have ring : TxRing.nativeCell v.wg = TxRing.nativeCell w.wg := congrArg Prod.fst context
  have queues : TxDisposition.txQueues v.wg = TxDisposition.txQueues w.wg := congrArg Prod.snd context
  have mapped := congrArg (fun cell : Option (Nat × PtrRing (List SkbId)) =>
    (cell.map fun pair => pair.2.items).getD []) ring
  have live : txCryptItems v.wg = txCryptItems w.wg := by
    simpa only [txCryptItems,TxRing.nativeCell,Option.map_map,Function.comp_def] using mapped
  have remainingMember : ∀ batch ∈ txCryptItems w.wg ++ active,
      batch ∈ txCryptItems w.wg ++ items :: active := by
    intro batch member
    rcases List.mem_append.mp member with before | after
    · exact List.mem_append_left _ before
    · exact List.mem_append_right _ (List.mem_cons_of_mem items after)
  have remainingUnique : (txCryptItems w.wg ++ active).flatten.Nodup := by
    have perm : (txCryptItems w.wg ++ items :: active).Perm (items :: (txCryptItems w.wg ++ active)) := by
      simpa only [List.singleton_append,List.append_assoc,List.cons_append,List.nil_append] using
        (show (txCryptItems w.wg ++ [items]).Perm ([items] ++ txCryptItems w.wg) from List.perm_append_comm).append_right active
    exact (List.nodup_append.mp (perm.flatten.nodup_iff.mp crypt.unique)).2.1
  refine ⟨TxDisposition.LiveFrontier.physical_transport ring crypt.physical,?_,?_,?_⟩
  · simpa only [live] using remainingUnique
  · intro batch member
    rw [live] at member
    obtain ⟨pid,p,found,queued⟩ := crypt.owners batch (remainingMember batch member)
    have old : TxDisposition.txQueues w.wg pid = some p.txQueue := by
      simpa only [TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,peerAt,Option.map_some] using
        congrArg (Option.map (·.txQueue)) found
    rw [← queues] at old
    obtain ⟨q,resident,queue⟩ := Option.map_eq_some_iff.mp old
    exact ⟨pid,q,resident,queue.symm ▸ queued⟩
  · intro batch member
    rw [live] at member
    obtain ⟨first,head,packet,resident,state⟩ := crypt.uncrypted batch (remainingMember batch member)
    have outside : first ∉ items := by
      intro selected
      exact crypt.selected_disjoint first selected (List.mem_flatten.mpr ⟨batch,member,List.mem_of_head? head⟩)
    have same := (ProjectedAction.iff_run _ _ _).mp
      (TxDisposition.SelectedEncrypt.step_other first items outside) w result v run
    exact ⟨first,head,packet,same.trans resident,state⟩

end Leanux.Proofs.WG.RetirementSecurity
