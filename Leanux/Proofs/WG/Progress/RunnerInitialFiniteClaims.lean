import Leanux.Proofs.WG.Progress.RunnerInitialFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RunnerFinite
open Leanux

/-- Complete initialization has exactly the finite prefill and boot result,
including invalid prefill counts and indexed initialization Stops. -/
theorem original_initial_finite (trace : Runner.Trace) (placeholders : Bool) :
    runnerInitial trace placeholders = initial trace placeholders :=
  initial_source trace placeholders

end Leanux.Proofs.WG.Progress.RunnerFinite
