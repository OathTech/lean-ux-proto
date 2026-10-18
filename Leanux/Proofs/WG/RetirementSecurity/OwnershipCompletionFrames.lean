import Leanux.Proofs.WG.RetirementSecurity.OwnershipSocketFrames
import Leanux.Proofs.WG.Queues.TxCompletionQueues

/-! The actual completed-send path may queue handshake work, but it neither
acquires nor releases a key reference. Its peer borrow is repaid on refusal;
on acceptance it becomes a peer work reference, not a key credit. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

private def ownershipFromBorrow (s : WGStoreView × (PeerId → Option Peer)) :=
  ((fun id : KeypairId => (s.1.dev.bind fun d => d.keypairs[id]?).map fun k => (k.internalId,k.refcount)),
   s.1.dev.isSome,(fun pid => (s.2 pid).map peerOwnership),
   (fun id : SkbId => (s.1.dev.bind fun d => d.txSkbs[id]?).map (·.keypair)),
   (fun id : SkbId => (s.1.dev.bind fun d => d.rxSkbs[id]?).map (·.keypair)))

private theorem ownership_borrow_factor (w : WGWorld) :
    ownershipFromBorrow (PeerBorrow.view w) = ownershipPointView w := by
  unfold ownershipFromBorrow PeerBorrow.view PeerBorrow.outsidePeers PeerBorrow.resident
    ownershipPointView keyReferenceView
  simp only [wgStoreView,keyAt,ownershipAt,peerAt,packetKeyWords,
    Option.bind_map,Function.comp_def,Option.isSome_map]

theorem peerGet_ownership (pid : PeerId) : SameView ownershipPointView (peerGet pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold peerGet refcountInc
  simp only [requireNotPending,branch,branchCmp,unsupported]
  repeat' ownership_source_step initial

private def queueInstall (pid : PeerId) : WG.M Unit := do
  updatePeer pid (fun p => {p with handshakePending := true})
  recordQueued .sendWorker pid
  modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}

private theorem queueInstall_ownership (pid : PeerId) :
    SameView ownershipPointView (queueInstall pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold queueInstall updatePeer
  simp only [recordQueued]
  repeat' ownership_source_step initial

theorem handshakeBorrow_ownership (pid : PeerId) (pending : Bool) :
    SameView ownershipPointView (Queues.RxCredits.handshakeBorrow pid pending) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  rw [Queues.RxCredits.handshakeBorrow,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,getRun,tail⟩ := run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.strict_acquire_spec pid (wgStoreView w)) w a () u c rfl getRun
  have before := (ProjectedAction.iff_run_ambient _ _ _).mp (peerGet_ownership pid)
    w a () u c getRun
  simp only [Queues.RxCredits.handshakeQueueTail,MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨peek,t,e,peekRun,queued,s,f,branchRun,tail⟩ := tail
  have peekSame : t = u := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.peekQueuedUnit .sendWorker pid) (fun s => s = u))
    u c peek t e rfl peekRun
  subst t
  have branchSame : s = u := by cases branchRun; rfl
  subst s
  cases queued with
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,z,g,putRun,final⟩ := tail
    cases final
    have restored := (hoare_iff_run_ambient _ _ _).mp
      (PeerBorrow.repay_spec (some pid) (wgStoreView w)) u f () v b borrowed putRun
    exact (ownership_borrow_factor v).symm.trans
      ((congrArg ownershipFromBorrow restored).trans (ownership_borrow_factor w))
  | false =>
    simp only [Bool.false_eq_true,ite_false] at tail
    have install : ((queueInstall pid).run u).run f = .ok (((),v),b) := tail
    exact ((ProjectedAction.iff_run_ambient _ _ _).mp (queueInstall_ownership pid)
      u f () v b install).trans before

theorem sendQueued_ownership (pid : PeerId) (retry : Bool) :
    SameView ownershipPointView (sendQueuedHandshakeInitiation pid retry) := by
  rw [← Queues.RxCredits.queuedSource_eq]
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold Queues.RxCredits.queuedSource
  simp only [Queues.RxCredits.modifyPeer_source,branch]
  repeat' first
    | (rx_retention_head branchExpired
       exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => ownershipPointView w = initial))
    | (rx_retention_head Queues.RxCredits.handshakeBorrow
       exact (handshakeBorrow_ownership _ _).wp (fun s => s = initial))
    | ownership_source_step initial

theorem keepKeyFresh_ownership (pid : PeerId) :
    SameView ownershipPointView (keepKeyFresh pid) := by
  intro initial
  exact Queues.RxCredits.TxReservation.keepKeyFresh_preserves _ pid
    ((sendQueued_ownership pid false).wp (fun s => s = initial))

theorem createDataDone_ownership (pid : PeerId) (items : List SkbId) :
    SameView ownershipPointView (createDataDone pid items) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold createDataDone timersAnyAuthenticatedPacketSent WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => ownershipPointView w = initial)
       intro x b
       change Preserves (fun w => ownershipPointView w = initial) _)
    | (rx_retention_head timersTraversal
       exact (timersTraversal_ownership _).wp (fun s => s = initial))
    | (rx_retention_head delTimer
       exact (delTimer_ownership _ _).wp (fun s => s = initial))
    | (rx_retention_head sendSkbToPeer
       exact (sendSkbToPeer_ownership _ _ _).wp (fun s => s = initial))
    | (rx_retention_head timersDataSent
       exact (timersDataSent_ownership _).wp (fun s => s = initial))
    | (rx_retention_head keepKeyFresh
       exact (keepKeyFresh_ownership _).wp (fun s => s = initial))
    | ownership_source_step initial

theorem HolderAccount.complete_tx (account : HolderAccount temporary w)
    (pid : PeerId) (items : List SkbId) (a b : Ambient)
    (run : ((createDataDone pid items).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := account.points
  ((ProjectedAction.iff_run_ambient _ _ _).mp (createDataDone_ownership pid items) w a () v b run)

end Leanux.Proofs.WG.RetirementSecurity
