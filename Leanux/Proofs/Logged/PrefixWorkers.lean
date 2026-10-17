import Leanux.Proofs.Logged.PrefixLoops

/-! One original worker iteration, retaining the observed prefix on error. -/
namespace Leanux.Proofs.Logged
open Leanux

def workerIterPrefix (w : Worker) (pid : Option Nat)
    (step afterItem : PrefixM Event Bool) : PrefixM Event IterResult := do
  let _ := (w, pid)
  if !(← step) then return .ended
  return if ← afterItem then .yielded else .continued

theorem workerIterPrefix_erases (w : Worker) (pid : Option Nat)
    (hs : ErasesPrefix step originalStep) (ha : ErasesPrefix afterItem originalAfter) :
    ErasesPrefix (workerIterPrefix w pid step afterItem) (workerIter w pid originalStep originalAfter) := by
  unfold workerIterPrefix workerIter
  apply erasesPrefix_bind hs
  intro more
  split
  · exact erasesPrefix_pure _
  · apply erasesPrefix_bind ha
    intro yes
    exact erasesPrefix_pure _

theorem workerIterPrefix_preserves (w : Worker) (pid : Option Nat)
    (hsafe : ∀ h w, I h w → S h) (hs : PrefixPreserves I S step)
    (ha : PrefixPreserves I S afterItem) :
    PrefixPreserves I S (workerIterPrefix w pid step afterItem) := by
  unfold workerIterPrefix
  apply PrefixPreserves.bind hs
  intro more
  split
  · exact PrefixPreserves.pure hsafe _
  · apply PrefixPreserves.bind ha
    intro yes
    exact PrefixPreserves.pure hsafe _

/-- The original bounded whole worker loop, including exhaustion and callback
Stops. The callback runs only after a step reports an item. -/
def workerLoopPrefix (w : Worker) (pid : Option Nat) (step : PrefixM Event Bool)
    (afterItem : PrefixM Event Unit) (bound : Nat) (drained : String) : PrefixM Event Unit := do
  for _ in [0:bound] do
    if (← workerIterPrefix w pid step (do afterItem; pure false)) == .ended then return
  liftPrefix (invariant drained)

theorem workerLoopPrefix_erases (w : Worker) (pid : Option Nat)
    (hs : ErasesPrefix step originalStep) (ha : ErasesPrefix afterItem originalAfter)
    (bound : Nat) (drained : String) :
    ErasesPrefix (workerLoopPrefix w pid step afterItem bound drained)
      (workerLoop w pid originalStep originalAfter bound drained) := by
  unfold workerLoopPrefix workerLoop
  repeat' first
    | with_reducible apply workerIterPrefix_erases _ _ hs
    | with_reducible exact ha
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem workerLoopPrefix_preserves {Event : Type} {I : List Event → World → Prop}
    {S : List Event → Prop} {step : PrefixM Event Bool} {afterItem : PrefixM Event Unit}
    (w : Worker) (pid : Option Nat)
    (hsafe : ∀ h w, I h w → S h) (hs : PrefixPreserves I S step)
    (ha : PrefixPreserves I S afterItem) (bound : Nat) (drained : String) :
    PrefixPreserves I S (workerLoopPrefix w pid step afterItem bound drained) := by
  have hi : PrefixPreserves I S (liftPrefix (invariant drained) : PrefixM Event Unit) := by
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ hsafe
    intro h w x v _ hr
    cases hr
  unfold workerLoopPrefix
  repeat' first
    | with_reducible apply workerIterPrefix_preserves _ _ hsafe hs
    | with_reducible exact ha
    | with_reducible exact hi
    | with_reducible exact PrefixPreserves.pure hsafe _
    | with_reducible apply PrefixPreserves.range _ _ _ hsafe
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

end Leanux.Proofs.Logged
