import Leanux.Proofs.WG.Index.ReachedRunnerBridge
import Leanux.Proofs.WG.Index.ReachedIndexFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.Reached
open Lean Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Queues Queues.RxCredits

/-- The existing account and index projection depend only on the landed
WireGuard store observation at this outer boundary. -/
theorem anyEntry_store (h : List RxHistory.Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (entry : AnyEntry h w) :
    AnyEntry h v := by
  obtain ⟨cs,entry⟩ := entry
  exact ⟨cs,HolderEntryDispatch.wg_store entry.1 same,
    core_device (congrArg WGStoreView.dev same) entry.2⟩
end Leanux.Proofs.WG.Index.Reached
