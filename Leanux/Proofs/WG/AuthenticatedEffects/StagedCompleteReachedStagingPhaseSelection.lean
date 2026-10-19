import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseTake

/-! Borrow points are embedded in the actual outer selection receipt. Their
selected account is derived from the original idle entry and native take;
no completed selection or later successful staging outcome is required. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staging.Points CompleteCarrier HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

theorem take_receipt_run
    (native : ((Take.takePrefix pid).run w).run a=.ok ((some peer,u),b)) :
    runWGPrefix (receiptWGObserved (liftWGPrefix (Take.takePrefix pid))
      (fun r=>Event.stagingTaken ⟨pid,r⟩)) w a h=
      (.ok ((some peer,u),b),h++[.stagingTaken ⟨pid,⟨some peer,w,u,a,b⟩⟩]) := by
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift,native]

noncomputable def borrow_point
    (native : ((Take.takePrefix pid).run w).run a=.ok ((some peer,u),b))
    (point : Point (borrowShape (some peer)) u b (h++[.stagingTaken ⟨pid,⟨some peer,w,u,a,b⟩⟩])
      leaf v c middle remaining) :
    Point (selectionShape pid) w a h leaf v c middle
      (savedReceipt (fun r=>Event.old (.responder (.selected pid r))) w a remaining) := by
  unfold selectionShape
  apply Point.marked
  apply Point.receiptBody
  exact .right (.receipt _ (takeShape pid)) borrowShape (take_receipt_run native) point

/-- Every actual key-borrow point keeps the SAME transferred ticket ledger,
its ordered selected cohort and its native take anchor, even before a Stop. -/
theorem borrow_every_point (before : Accounted h ledger debts locals w)
    (native : ((Take.takePrefix pid).run w).run a=.ok ((some peer,u),b))
    (point : Point (borrowShape (some peer)) u b (h++[.stagingTaken ⟨pid,⟨some peer,w,u,a,b⟩⟩])
      leaf v c middle remaining) :
    ∃ after generation,Staged.Obligations.Step ledger after ∧
      after=transferLocation (.staged generation pid peer.internalId) (.selected h.length) ledger ∧
      CompleteSelected.Ready after debts locals generation pid peer h.length middle v c ∧
      runWGPrefix (CausalJournal.selection pid) w a h=
        runWGPrefix (savedReceipt (fun r=>Event.old (.responder (.selected pid r))) w a remaining) v c middle := by
  obtain ⟨after,generation,steps,transferred,ready⟩:=
    CompleteSelected.taken ⟨pid,⟨some peer,w,u,a,b⟩⟩ native rfl before
  exact ⟨after,generation,steps,transferred,(borrow_covers ready).point point,(borrow_point native point).residual⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
