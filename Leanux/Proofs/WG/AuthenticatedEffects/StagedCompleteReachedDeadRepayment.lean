import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDeadSource

/-! The same original DEAD repayment frontier supplies a fixed successful
prefix and the actual failed key, peer-cut or peer-finish interval. A final
peer cut retains its exact successor ledger and receipt position. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch

theorem dead_repayment_reached
    (before : Accounted history ledger debts locals w.wg)
    (frontier : Converse.Dead.RepayStopped ledger debts locals pid key w history reason last) :
    ∃ stage, ∃ cut : DeadCut,
      runPrefix (deadRepaymentPrefix pid key stage) w history = (.ok ((),cut.world),cut.before) ∧
      Staged.Obligations.Step ledger cut.ledger ∧ cut.debts = debts ∧ cut.locals = locals ∧
      cut.Valid reason last := by
  cases frontier with
  | keyStopped accounted failed =>
    exact ⟨.key,⟨ledger,debts,locals,w,history,.key key⟩,rfl,.refl _,rfl,rfl,before,failed,accounted⟩
  | peerStopped u middle keyRun accounted stopped =>
    cases stopped with
    | cutStopped entry complete failed =>
      refine ⟨.peer,⟨ledger,debts,locals,u,middle,.peerCut (some pid)⟩,keyRun,.refl _,rfl,rfl,
        accounted,?_,entry,complete⟩
      change runPrefix ((liftWGObserver (PeerRelease.cut (some pid))) >>= fun _ => pure ()) u middle = _
      rw [runPrefix_bind,liftWGObserver_run,failed]
      rfl
    | finishStopped value g ambient cutHistory after performed step frame successor entry complete same failed =>
      refine ⟨.finish,⟨after,debts,locals,{u with wg := g,ambient := ambient},
        cutHistory ++ [PeerRelease.receipt (some pid) value u.wg g u.ambient ambient],.peerFinish value⟩,
        ?_,step,rfl,rfl,⟨entry,complete⟩,failed,?_⟩
      · change runPrefix (Admission.actualOps.access (keypairPutPrefix (some key) false) >>= fun _ => _) w history = _
        rw [runPrefix_bind,keyRun]
        dsimp only
        rw [runPrefix_bind,recordedPeerCut_run (some pid) performed]
        rfl
      · simpa only [same] using (show Accounted
          (cutHistory ++ [PeerRelease.receipt (some pid) value u.wg g u.ambient ambient])
          after debts locals g from ⟨entry,complete⟩)

theorem dead_repayment_failed
    (frontier : Converse.Dead.RepayStopped ledger debts locals pid key w history reason last) :
    runPrefix (DeadEntry.repay pid key) w history = (.error reason,last) := by
  cases frontier with
  | keyStopped _ failed => rw [DeadEntry.repay,runPrefix_bind,failed]
  | peerStopped u middle keyRun _ stopped =>
    rw [DeadEntry.repay,runPrefix_bind,keyRun]
    dsimp only
    rw [runPrefix_bind,PeerRelease.actual_run]
    cases stopped with
    | cutStopped _ _ failed => rw [failed]
    | finishStopped value g ambient cutHistory after performed step frame successor entry complete same failed =>
      rw [performed]
      dsimp only
      rw [failed]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
