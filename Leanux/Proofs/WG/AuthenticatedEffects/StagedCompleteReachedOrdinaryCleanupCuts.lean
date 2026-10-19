import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedOrdinaryCleanupPath

/-! Literal prefixes of the original cleanup list reach the native erase,
with the exact remaining list and original lifetime suffix. Every position
is selected by the list split, not by an arbitrary action factor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OrdinaryCleanup
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations AllocatedObligation CompletionBatch CompleteCarrier

theorem loop_append (done rest : List SkbId) :
    freeLoop cleanupOps (done ++ rest)=
      (freeLoop cleanupOps done >>= fun _ => freeLoop cleanupOps rest) := by
  induction done with
  | nil => simp only [List.nil_append,freeLoop,pure_bind]
  | cons skb done ih => simp only [List.cons_append,freeLoop,ih,bind_assoc]

def sourcePrefix (done : List SkbId) (skb : SkbId) (phase : CleanupPrimitive.Phase) :
    PrefixM CausalJournal.Event Unit := do
  freeLoop cleanupOps done
  let entry ← liftPrefix (get : Leanux.M World)
  CleanupPrimitive.atPhase phase entry skb

theorem prefix_run
    (leading : runPrefix (freeLoop cleanupOps done) w history=(.ok ((),u),middle))
    (interval : Interval context ledger debts skb rest u middle generation v)
    (phase : CleanupPrimitive.Phase) :
    runPrefix (sourcePrefix done skb phase) w history=
      (.ok ((),v),CleanupPrimitive.current phase u skb middle) := by
  rw [sourcePrefix,runPrefix_bind,leading]
  change runPrefix (liftPrefix (get : Leanux.M World) >>= _) u middle=_
  rw [runPrefix_bind,runPrefix_lift]
  exact interval.literal phase

theorem loop_continuation
    (leading : runPrefix (freeLoop cleanupOps done) w history=(.ok ((),u),middle))
    (interval : Interval context ledger debts skb rest u middle generation v)
    (phase : CleanupPrimitive.Phase) :
    runPrefix (freeLoop cleanupOps (done ++ skb :: rest)) w history=
      runPrefix (due phase u skb >>= fun _ => freeLoop cleanupOps rest)
        v (CleanupPrimitive.current phase u skb middle) := by
  rw [loop_append,runPrefix_bind,leading]
  exact interval.continuation phase

/-- At every original list position, the actual post-erase state has complete
accounting with the consumed debt and the same terminal ledger. Its remaining
access markers and cleanup suffix are the original native continuation. -/
theorem every_interior (done : List SkbId)
    (path : CleanupPath context ledger (done ++ skb :: rest) debts w history final last) :
    ∃ cutWorld cutHistory cutDebts generation nextWorld,
      Interval context ledger cutDebts skb rest cutWorld cutHistory generation nextWorld ∧
      CleanupPath context ledger rest (forgetFreedCell cutHistory generation skb cutDebts)
        nextWorld (finished cutWorld skb cutHistory) final last ∧
      ∀ phase : CleanupPrimitive.Phase,
        runPrefix (sourcePrefix done skb phase) w history=
          (.ok ((),nextWorld),CleanupPrimitive.current phase cutWorld skb cutHistory) ∧
        Accounted (CleanupPrimitive.current phase cutWorld skb cutHistory) ledger
          (forgetFreedCell cutHistory generation skb cutDebts)
          (⟨.selected,context.pid,rest⟩ :: context.locals) nextWorld.wg ∧
        runPrefix (freeLoop cleanupOps (done ++ skb :: rest)) w history=
          runPrefix (due phase cutWorld skb >>= fun _ => freeLoop cleanupOps rest)
            nextWorld (CleanupPrimitive.current phase cutWorld skb cutHistory) := by
  obtain ⟨cutWorld,cutHistory,cutDebts,generation,nextWorld,leading,interval,tail⟩ :=
    prefix_interval done path
  refine ⟨cutWorld,cutHistory,cutDebts,generation,nextWorld,interval,tail,?_⟩
  intro phase
  exact ⟨prefix_run leading interval phase,interval.accounted phase,loop_continuation leading interval phase⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OrdinaryCleanup
