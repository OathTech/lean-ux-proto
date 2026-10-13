import Leanux.Proofs.Logged.Prefix

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

end Leanux.Proofs.Logged
