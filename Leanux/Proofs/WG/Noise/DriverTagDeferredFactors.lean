import Leanux.Proofs.Logged.PrefixLoops
import Leanux.Env

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Deferred
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- These four actual executions must be explicit callbacks. The other old
atoms contain no owner invocation relevant to the tag journal. -/
structure Hooks (E : Type) where
  sendOne : PrefixM E Unit
  clearOne : PrefixM E Unit
  timer : Worker → PeerId → PeerTimer → WheelEntry → Option UInt64 → PrefixM E Unit
  placeholder : UInt64 → PrefixM E Unit

def sendWith {E : Type} (hooks : Hooks E)
    (schedule : PrefixM E Unit) : PrefixM E Unit := do
  if (← liftPrefix getWG).dev.isNone then return
  liftPrefix Env.requireNoCryptWork
  liftPrefix (modifyWG fun w => {w with queuedThisCall := []})
  for _ in [0:(← liftPrefix recordBudget)] do
    if (← liftPrefix (liftWG getDev)).sendWorkQueue.isEmpty then liftPrefix Env.deliverSent; return
    hooks.sendOne
    schedule
  liftPrefix (budgetExhausted "the send work queue")

theorem send_erases_native {E : Type} (hooks : Hooks E)
    (one : ErasesPrefix hooks.sendOne Env.runOneSendWorker)
    (schedule : PrefixM E Unit) (hs : ErasesPrefix schedule (Env.schedule none)) :
    ErasesPrefix (sendWith hooks schedule) Env.runSendWorkers := by
  unfold sendWith Env.runSendWorkers
  repeat' first
    | exact hs
    | exact one
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Noise.DriverTags.Deferred
