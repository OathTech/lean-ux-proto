import Leanux.Proofs.WG.TimerDiscipline.HookSchedulerCommonSource
import Leanux.Proofs.WG.TimerDiscipline.HookPollFrontierSource
import Leanux.Proofs.WG.TimerDiscipline.HookStateLeavesSource

/-! Counter-frontier transport through the existing common-journal scheduler
and deferred observers. Native quiet leaves are discharged by their actual
ordinary/snapshot source contracts. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeJournal Lifetimes

theorem frontier_transport :
    HookState.CounterTransport (fun h w => Frontier h w.wg.keypairCounter) :=
  fun _ _ _ grow prior => prior.mono grow

theorem callbacks_state :
    HookScheduler.StateContracts (fun h w => Frontier h w.wg.keypairCounter) Ordered callbacks :=
  ⟨transmit_frontier,receive_frontier,softirq_frontier,irqExit_frontier⟩

theorem schedule_frontier (worker : Option Worker) :
    PrefixPreserves (fun h w => Frontier h w.wg.keypairCounter) Ordered (schedule worker) :=
  HookScheduler.schedule_preserves_state (fun _ _ prior => prior.1)
    (HookState.counter_store frontier_transport) callbacks callbacks_state
    (HookState.scheduler_leaves (fun _ _ prior => prior.1) frontier_transport) worker

theorem deferred_frontier (call : EnvDeferredCall) :
    PrefixPreserves (fun h w => Frontier h w.wg.keypairCounter) Ordered (deferred call) :=
  HookDeferred.observed_preserves_state (fun _ _ prior => prior.1)
    (HookState.counter_store frontier_transport)
    (HookState.scheduler_leaves (fun _ _ prior => prior.1) frontier_transport)
    (HookState.deferred_leaves (fun _ _ prior => prior.1) frontier_transport)
    callbacks callbacks_state sendOne sendOne_frontier call
end Leanux.Proofs.WG.TimerDiscipline.HookCommon
