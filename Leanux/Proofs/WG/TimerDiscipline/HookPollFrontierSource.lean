import Leanux.Proofs.WG.TimerDiscipline.HookCommonFrontierSource
import Leanux.Proofs.WG.Roaming.PollCallbackSource

/-! Concrete normal counter-frontier transport and failure-retained session order through unchanged poll/NAPI observers. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeJournal Queues
theorem poll_frontier (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (poll pid budget) :=
  Roaming.PollHookRules.poll_preserves_state (fun _ _ prior=>prior.1)
    (fun action grow=>quiet_frontier action grow) consume stack consume_frontier stack_frontier pid budget
theorem softirq_frontier :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered softirq :=
  RxNapi.softirq_preserves (fun _ _ prior=>prior.1) frontier_store
    (quiet_frontier _ (counter_product_frame (counter_native_frame PollCounterFrames.pending)))
    poll_frontier
theorem inline_frontier :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered inline :=
  RxNapi.inline_preserves (fun _ _ prior=>prior.1) frontier_store
    (quiet_frontier _ (counter_product_frame (counter_native_frame PollCounterFrames.pending)))
    poll_frontier
theorem irqExit_frontier :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered irqExit :=
  RxNapi.irqExit_preserves (fun _ _ prior=>prior.1) frontier_store
    (quiet_frontier _ (counter_product_frame (counter_native_frame PollCounterFrames.scheduled)))
    softirq_frontier
end Leanux.Proofs.WG.TimerDiscipline.HookCommon
