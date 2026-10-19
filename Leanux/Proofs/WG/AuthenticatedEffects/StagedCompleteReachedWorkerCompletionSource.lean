import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCompletionPrefixes
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionDisposal

/-! Completion prefixes parameterized by the native selected peer and list.
Their equality to the indexed completion prefixes is definitional; the worker
prefix executes the original selection and crypted branch before them. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkerCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch

def prelude (pid : PeerId) (items : List SkbId) : PrefixM CausalJournal.Event Unit := do
  CausalJournal.completionOps.completion pid items
  CausalJournal.completionOps.traversal pid
  CausalJournal.completionOps.sent pid

def entered (pid : PeerId) (items : List SkbId) (history : List CausalJournal.Event) : CausalJournal.Event :=
  .scope (.entered ⟨history.length,CausalSources.Cause.completion pid items⟩)

def preludePrefix (pid : PeerId) (items : List SkbId) : Completion.PreludeStage → PrefixM CausalJournal.Event Unit
  | .traversal => CausalJournal.completionOps.completion pid items
  | .authenticated => do
      CausalJournal.completionOps.completion pid items
      CausalJournal.completionOps.traversal pid

def iterationPrefix (pid : PeerId) (items done : List SkbId) : PrefixM CausalJournal.Event Bool :=
  fun w => ExceptT.mk fun history => runPrefix (do
    emitPrefix (entered pid items history)
    prelude pid items
    sendLoop CausalJournal.completionOps pid done false) w history

def finishPrefix (pid : PeerId) (sent : Bool) : Completion.FinishStage → PrefixM CausalJournal.Event Unit
  | .dataSent => CompletionBatch.discard (Completion.finishGuard sent)
  | .fresh => do
      let flag ← Completion.finishGuard sent
      if flag then CausalJournal.completionOps.dataSent pid

def completionPrefix (pid : PeerId) (items : List SkbId) : Completion.Point → PrefixM CausalJournal.Event Unit
  | .prelude stage => fun w => ExceptT.mk fun history => runPrefix (do
      emitPrefix (entered pid items history)
      preludePrefix pid items stage) w history
  | .packet done skb => do
      _ ← iterationPrefix pid items done
      _ ← Sending.iterationPrefix skb
      pure ()
  | .accounting done skb => do
      _ ← iterationPrefix pid items done
      let packet ← Sending.iterationPrefix skb
      _ ← Sending.accountingPrefix pid skb packet
      pure ()
  | .finish stage => fun w => ExceptT.mk fun history => runPrefix (do
      emitPrefix (entered pid items history)
      prelude pid items
      let sent ← sendLoop CausalJournal.completionOps pid items false
      finishPrefix pid sent stage) w history

theorem completionPrefix_context (context : Context) (point : Completion.Point) :
    completionPrefix context.pid context.items point = Completion.sourcePrefix context point := by
  cases point with
  | prelude stage => cases stage <;> rfl
  | packet done skb => rfl
  | accounting done skb => rfl
  | finish stage => cases stage <;> rfl

def workerPrefix (pid : PeerId) (point : Completion.Point) : PrefixM CausalJournal.Event Unit := do
  let selected ← workerSelection pid
  match selected with
  | none => pure ()
  | some picked => if picked.crypted then completionPrefix pid picked.items point else pure ()

theorem selected_run
    (path : SelectionPath ledger locals pid w history ⟨items,head,true⟩ u middle)
    (peer : context.pid = pid) (batch : context.items = items)
    (run : runPrefix (Completion.sourcePrefix context point) u middle = (.ok ((),v),last)) :
    runPrefix (workerPrefix pid point) w history = (.ok ((),v),last) := by
  rw [workerPrefix,runPrefix_bind,path.run]
  have same := completionPrefix_context context point
  rw [peer,batch] at same
  simpa only [↓reduceIte,same] using run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkerCompletion
