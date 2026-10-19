import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedXmitInitialized

/-! Transport an already established fixed transmit-source run equality
through the original runner continuation. This congruence supplies no
native source provenance on its own. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Xmit
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

theorem resume_run_eq (trace : Trace) (operationIndex : Nat) (op : Operation)
    (state : RunnerOperation.State) (body tail : PrefixM Event Int)
    (same : runPrefix body w history=runPrefix tail v last) :
    runPrefixOuter (resume trace operationIndex op state w body) history =
      runPrefixOuter (resume trace operationIndex op state v tail) last := by
  unfold resume
  simp only [runAt_bind,bind_assoc,runPrefixOuter_bind,runAtPrefix_run]
  rw [same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Xmit
