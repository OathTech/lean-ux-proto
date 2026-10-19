import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCleanupPrimitiveRuns

/-! Ordinary free has only its original lifetime-access suffix. Its terminal
outcome was recorded earlier by the send; these fixed remaining actions add
no terminal event and cannot fail after the native erase. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OrdinaryCleanup
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation

def finished (w : World) (skb : SkbId) (history : List CausalJournal.Event) :=
  history ++ [CleanupPrimitive.readEvent w.wg skb,CleanupPrimitive.releaseEvent w.wg skb]

def due (phase : CleanupPrimitive.Phase) (w : World) (skb : SkbId) : PrefixM CausalJournal.Event Unit :=
  match phase with
  | .mutated => emitPrefix (CleanupPrimitive.releaseEvent w.wg skb)
  | .released => pure ()

theorem due_run (phase : CleanupPrimitive.Phase) (w v : World) (skb : SkbId)
    (history : List CausalJournal.Event) :
    runPrefix (due phase w skb) v (CleanupPrimitive.current phase w skb history)=
      (.ok ((),v),finished w skb history) := by
  cases phase <;> simp [due,CleanupPrimitive.current,finished,runPrefix_emit,List.append_assoc]

theorem original_suffix (phase : CleanupPrimitive.Phase) (w v : World) (skb : SkbId)
    (history : List CausalJournal.Event)
    (native : (liftWG (freeTxSkb skb)).run w=.ok ((),v)) :
    runPrefix (FirstTerminal.cleanupFree skb) w history=
      runPrefix (due phase w skb) v (CleanupPrimitive.current phase w skb history) := by
  rw [CleanupPrimitive.cleanup_run skb w v history native,due_run]
  rfl

theorem source_split (phase : CleanupPrimitive.Phase) (w v : World) (skb : SkbId)
    (history : List CausalJournal.Event)
    (native : (liftWG (freeTxSkb skb)).run w=.ok ((),v)) :
    runPrefix (FirstTerminal.cleanupFree skb) w history=
      runPrefix (do CleanupPrimitive.atPhase phase w skb; due phase w skb) w history := by
  rw [runPrefix_bind,CleanupPrimitive.prefix_run phase skb w v history native]
  exact original_suffix phase w v skb history native

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.OrdinaryCleanup
