import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionStops

/-! Concrete worker cuts immediately before and after queue removal.
The original head read remains in the fixed prefix. The same ledger moves
from native queue ownership to a selected local without an invented event. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch

def workerReadPrefix (pid : PeerId) :
    PrefixM CausalJournal.Event (Option (List SkbId × DataPacket)) := do
  let first ← TxSelection.peek pid
  let go ← TxWorker.ready first
  if !go then return none
  let some items := first | CausalJournal.completionOps.step (invariant "unreachable")
  let some id := items.head? | CausalJournal.completionOps.step (invariant "an empty ring item")
  let head ← CausalJournal.completionOps.packet id
  return some (items,head)

def workerDropPrefix (pid : PeerId) : PrefixM CausalJournal.Event Unit := do
  let selected ← workerReadPrefix pid
  match selected with
  | none => pure ()
  | some (items,_) => CausalJournal.completionOps.drop pid items

/-- Both ownership projections belong to original named source cuts from
the same worker entry. Queue removal consumes that queue occurrence and
supplies its selected local; a later callback need not return. -/
theorem SelectionPath.dequeue_cuts
    (path : SelectionPath ledger locals pid w history picked v last) :
    ∃ readWorld readHistory dropWorld,
      runPrefix (workerReadPrefix pid) w history =
        (.ok (some (picked.items,picked.head),readWorld),readHistory) ∧
      Accounted readHistory ledger [] locals readWorld.wg ∧
      runPrefix (CausalJournal.completionOps.drop pid picked.items) readWorld readHistory =
        (.ok ((),dropWorld),last) ∧
      runPrefix (workerDropPrefix pid) w history = (.ok ((),dropWorld),last) ∧
      Accounted last ledger [] (⟨.selected,pid,picked.items⟩ :: locals) dropWorld.wg := by
  cases path with
  | intro pw rw sw dw ph rh sh id initial peeked readied nonempty read beforeDrop removed afterDrop guarded afterGuard pending =>
    have prefixRun : runPrefix (workerReadPrefix pid) w history =
        (.ok (some (picked.items,picked.head),sw),sh) := by
      simp only [workerReadPrefix,runPrefix_bind,peeked,readied,Bool.not_true,
        Bool.false_eq_true,↓reduceIte,nonempty,read,runPrefix_pure]
    refine ⟨sw,sh,dw,prefixRun,beforeDrop,removed,?_,afterDrop⟩
    rw [workerDropPrefix,runPrefix_bind,prefixRun]
    exact removed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
