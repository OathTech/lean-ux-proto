import Leanux.Proofs.WG.RetirementSecurity.TxCryptSocketFrames

/-! Exact completion frames for pending encryption. Actual socket sends and
handshake-work requests leave the ring and all TX packet cells unchanged;
the original queue-retention theorem supplies the owning queue component. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem peerGet_cryptWire (pid : PeerId) : SameView txCryptWire (peerGet pid) :=
  (TxRing.peerGet_frame pid).product (TxDisposition.peerGet_packets pid)

theorem peerPut_cryptWire (pid : Option PeerId) : SameView txCryptWire (peerPut pid) :=
  (TxRing.peerPut_frame pid).product (TxDisposition.peerPut_packets pid)

theorem sendQueued_cryptWire (pid : PeerId) (retry : Bool) :
    SameView txCryptWire (sendQueuedHandshakeInitiation pid retry) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | (rx_retention_head branchExpired
       exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => txCryptWire w = initial))
    | (rx_retention_head peerGet; exact (peerGet_cryptWire _).wp (fun s => s = initial))
    | (rx_retention_head peerPut; exact (peerPut_cryptWire _).wp (fun s => s = initial))
    | crypt_wire_step initial

theorem keepKeyFresh_cryptWire (pid : PeerId) : SameView txCryptWire (keepKeyFresh pid) := by
  intro initial
  exact RxCredits.TxReservation.keepKeyFresh_preserves _ pid
    ((sendQueued_cryptWire pid false).wp (fun s => s = initial))

theorem createDataDone_cryptWire (pid : PeerId) (items : List SkbId) :
    SameView txCryptWire (createDataDone pid items) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold createDataDone timersAnyAuthenticatedPacketSent WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => txCryptWire w = initial)
       intro x b
       change Preserves (fun w => txCryptWire w = initial) _)
    | (rx_retention_head timersTraversal
       exact (timersTraversal_cryptWire _).wp (fun s => s = initial))
    | (rx_retention_head delTimer
       exact (delTimer_cryptWire _ _).wp (fun s => s = initial))
    | (rx_retention_head sendSkbToPeer
       exact (sendSkbToPeer_cryptWire _ _ _).wp (fun s => s = initial))
    | (rx_retention_head timersDataSent
       exact (timersDataSent_cryptWire _).wp (fun s => s = initial))
    | (rx_retention_head keepKeyFresh
       exact (keepKeyFresh_cryptWire _).wp (fun s => s = initial))
    | crypt_wire_step initial

theorem TxCryptInventory.send_done (crypt : TxCryptInventory active w)
    (pid : PeerId) (items : List SkbId) (a b : Ambient)
    (run : ((createDataDone pid items).run w).run a = .ok (((),v),b)) :
    TxCryptInventory active v := by
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp
    (createDataDone_cryptWire pid items) w a () v b run
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
    (RxCredits.TxReservation.createDataDone_queues pid items) w a () v b run
  exact crypt.frame_packets (congrArg Prod.fst fields)
    (fun _ owned => owned.queues queues) (congrArg Prod.snd fields)

theorem TxCryptInventory.send_completion (crypt : TxCryptInventory active w)
    (pid : PeerId) (items : List SkbId) (head : DataPacket) (a b : Ambient)
    (run : ((txCompletionSource pid items head).run w).run a = .ok (((),v),b)) :
    TxCryptInventory active v := by
  simp only [txCompletionSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨crypted,u,c,branchRun,tail⟩ := run
  have same : u = w := by cases branchRun; rfl
  subst u
  cases crypted with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact crypt
  | true =>
    simp only [ite_true] at tail
    exact crypt.send_done pid items c b tail

theorem TxCryptInventory.dispose (crypt : TxCryptInventory active w)
    (outside : CryptOutside items active w) (pid : PeerId) (kid : KeypairId) (a b : Ambient)
    (run : ((TxDisposition.disposeSource pid items kid).run w).run a = .ok ((result,v),b)) :
    result = true ∧ TxCryptInventory active v := by
  have factor : TxDisposition.disposeSource pid items kid = (do
      TxDisposition.freeList items
      keypairPut (some kid) false
      peerPut (some pid)
      pure true) := by simp [TxDisposition.disposeSource,TxDisposition.freeList]
  rw [factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,freeRun,_,t,e,keyRun,_,s,f,peerRun,done⟩ := run
  cases done
  exact ⟨rfl,((crypt.free_list outside a c freeRun).key_put (some kid) false c e keyRun).peer_put
    (some pid) e b peerRun⟩

end Leanux.Proofs.WG.RetirementSecurity
