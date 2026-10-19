import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAfterXmitScheduler

/-! Transport a fixed callback source equality through the remaining
initialized runner. Its premise must come from a source path; equality of
arbitrary monadic factorizations does not itself establish such a path. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AfterXmit
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

theorem resume_run_eq (trace : Trace) (operationIndex : Nat) (op : Operation)
    (state : RunnerOperation.State) (ret : Int) (body tail : PrefixM Event Unit)
    (same : runPrefix body w history=runPrefix tail v last) :
    runPrefixOuter (resume trace operationIndex op state ret w body) history =
      runPrefixOuter (resume trace operationIndex op state ret v tail) last := by
  unfold resume
  simp only [runAt_bind,bind_assoc,runPrefixOuter_bind,runAtPrefix_run]
  rw [same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AfterXmit
