import Leanux.Proofs.WG.Noise.DriverTagPollSource
import Leanux.Proofs.WG.Noise.DriverTagSchedulerSource
import Leanux.Proofs.WG.Noise.DriverTagDeferredCallsSource

/-! Concrete scheduler and deferred callers: every NAPI, worker, timer and
guard obligation is now discharged against the actual original call. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Scheduled
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

def softirq : ProductObs Unit := liftPrefix Env.napiSoftirq
def irqExit : ProductObs Unit := liftPrefix Env.napiIrqExit
def inlinePoll : ProductObs Unit := liftPrefix Env.pollScheduledInline

theorem softirq_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory softirq :=
  TimerProduct.lift_preserves entry _ Poll.softirq_native

theorem irqExit_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory irqExit :=
  TimerProduct.lift_preserves entry _ Poll.irqExit_native

theorem inlinePoll_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory inlinePoll :=
  TimerProduct.lift_preserves entry _ Poll.inline_native

def schedule (stack : Option Worker := none) : ProductObs Unit :=
  Scheduler.schedule softirq irqExit stack

def nested (worker : Worker) : ProductObs Unit :=
  Scheduler.nested softirq irqExit worker

def deferred (call : EnvDeferredCall) : ProductObs call.Result :=
  DeferredCalls.observed (schedule none) call

theorem schedule_preserves (entry : TagMap) (stack : Option Worker) :
    PrefixPreserves (StateInv entry) ValidHistory (schedule stack) :=
  Scheduler.schedule_preserves entry softirq irqExit
    (softirq_preserves entry) (irqExit_preserves entry) stack

theorem schedule_erases (stack : Option Worker) :
    ErasesPrefix (schedule stack) (Env.schedule stack) :=
  Scheduler.schedule_erases softirq irqExit (erasesPrefix_lift _) (erasesPrefix_lift _) stack

theorem nested_preserves (entry : TagMap) (worker : Worker) :
    PrefixPreserves (StateInv entry) ValidHistory (nested worker) :=
  Scheduler.nested_preserves entry softirq irqExit
    (softirq_preserves entry) (irqExit_preserves entry) worker

theorem nested_erases (worker : Worker) :
    ErasesPrefix (nested worker) (Env.nestedResched worker) :=
  Scheduler.nested_erases softirq irqExit (erasesPrefix_lift _) (erasesPrefix_lift _) worker

theorem deferred_preserves (entry : TagMap) (call : EnvDeferredCall) :
    PrefixPreserves (StateInv entry) ValidHistory (deferred call) :=
  DeferredCalls.observed_preserves entry (schedule none) (schedule_preserves entry none) call

theorem deferred_erases (call : EnvDeferredCall) : ErasesPrefix (deferred call) call.original :=
  DeferredCalls.observed_erases (schedule none) (schedule_erases none) call

end Leanux.Proofs.WG.Noise.DriverTags.Scheduled

