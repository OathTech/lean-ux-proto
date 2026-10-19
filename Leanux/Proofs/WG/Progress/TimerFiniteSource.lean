import Leanux.Proofs.WG.Progress.TimerFiniteNativeSource
import Leanux.Proofs.WG.TimerDiscipline.HookDeferredSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.TimerFinite
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues

theorem placeholder_source (jHi : UInt64) :
    RxHistory.placeholderTimerPassSource jHi = placeholder jHi := by
  unfold RxHistory.placeholderTimerPassSource placeholder
  simp only [callback_source]
  rfl

end Leanux.Proofs.WG.Progress.TimerFinite
