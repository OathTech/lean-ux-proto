import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedOrdinaryCleanupCuts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionDisposal

/-! Actual crypted completion starts the same worker's ordinary cleanup
path. Sending chooses the ledger once; all later native free points keep it,
and the original key/peer repayment remains after the cleanup suffix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OrdinaryCleanup
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CompletionBatch
variable {initial : Ledger}

def workerPrefix (pid : PeerId) (done : List SkbId) (skb : SkbId) (phase : CleanupPrimitive.Phase) :
    PrefixM CausalJournal.Event Unit := do
  let selected ← workerSelection pid
  match selected with
  | none => pure ()
  | some picked =>
    if picked.crypted then
      CompletionEffects.completeScoped CausalJournal.Event.scope CausalSources.Cause.completion
        CausalJournal.completionOps pid picked.items
      sourcePrefix done skb phase
    else pure ()

theorem selected_cleanup_path
    (path : SelectionPath initial locals pid w history ⟨items,head,true⟩ u middle)
    (completed : runPrefix (CompletionEffects.completeScoped CausalJournal.Event.scope
      CausalSources.Cause.completion CausalJournal.completionOps pid items) u middle=
      (.ok ((),freeWorld),freeHistory)) :
    ∃ context : Context, context.pid=pid ∧ context.locals=locals ∧ context.items=items ∧
      context.initialLedger=initial ∧
      ∃ ledger debts final last,
        SendSettlements context initial [] ledger debts ∧
        CleanupPath context ledger items debts freeWorld freeHistory final last := by
  obtain ⟨account,pending⟩ := path.accounted_entry
  obtain ⟨context,peer,localEq,batch,origin,_,owned⟩ := TxSelection.selected_context account.entry pending
  have before := Converse.Sending.start owned (LocalDebts.empty context context.items) account.complete
  obtain ⟨_,_,checked⟩ := Converse.completeScoped_checked context initial [] u middle before
  have normal : runPrefix (CompletionEffects.completeScoped CausalJournal.Event.scope
      CausalSources.Cause.completion CausalJournal.completionOps context.pid context.items) u middle=
      (.ok ((),freeWorld),freeHistory) := by simpa only [peer,batch] using completed
  rw [normal] at checked
  obtain ⟨ledger,debts,trace,ready,localDebts,complete⟩ := checked
  obtain ⟨final,last,cleaned⟩ := cleanup_path context.items ready.ready_to_free localDebts complete
  exact ⟨context,peer,localEq,batch,origin,ledger,debts,final,last,trace,by simpa only [batch] using cleaned⟩

theorem worker_prefix_run
    (path : SelectionPath initial locals pid w history ⟨items,head,true⟩ u middle)
    (completed : runPrefix (CompletionEffects.completeScoped CausalJournal.Event.scope
      CausalSources.Cause.completion CausalJournal.completionOps pid items) u middle=
      (.ok ((),freeWorld),freeHistory))
    (reached : runPrefix (sourcePrefix done skb phase) freeWorld freeHistory=(.ok ((),v),after)) :
    runPrefix (workerPrefix pid done skb phase) w history=(.ok ((),v),after) := by
  rw [workerPrefix,runPrefix_bind,path.run]
  change runPrefix (_ >>= _) u middle=_
  rw [runPrefix_bind,completed]
  exact reached

theorem worker_continuation
    (path : SelectionPath initial locals pid w history ⟨items,head,true⟩ u middle)
    (completed : runPrefix (CompletionEffects.completeScoped CausalJournal.Event.scope
      CausalSources.Cause.completion CausalJournal.completionOps pid items) u middle=
      (.ok ((),freeWorld),freeHistory))
    (shape : items=done++skb::rest)
    (leading : runPrefix (freeLoop cleanupOps done) freeWorld freeHistory=(.ok ((),cutWorld),cutHistory))
    (interval : Interval context ledger debts skb rest cutWorld cutHistory generation v)
    (phase : CleanupPrimitive.Phase) :
    runPrefix (CausalJournal.transmit pid) w history=
      runPrefix (do
        due phase cutWorld skb
        freeLoop cleanupOps rest
        CompletionBatch.release cleanupOps pid head.keypair)
        v (CleanupPrimitive.current phase cutWorld skb cutHistory) := by
  rw [path.callback_run]
  change runPrefix (TxWorker.crypted pid items head) u middle=_
  rw [TxWorker.crypted,runPrefix_bind,completed]
  change runPrefix (HandshakeSecurity.StagedDisposal.TxSource.dispose cleanupOps pid items head.keypair) freeWorld freeHistory=_
  rw [←dispose_factor]
  change runPrefix (freeLoop cleanupOps items >>= fun _ => CompletionBatch.release cleanupOps pid head.keypair) freeWorld freeHistory=_
  rw [shape,runPrefix_bind,loop_continuation leading interval phase]
  simp only [runPrefix_bind,due_run]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OrdinaryCleanup
