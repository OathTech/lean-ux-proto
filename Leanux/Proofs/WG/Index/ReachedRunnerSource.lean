import Leanux.Proofs.WG.Index.ReachedRunnerFrames
import Leanux.Proofs.WG.Index.ReachedInitialSource
import Leanux.Proofs.WG.Origins.NormalRunnerInvariant

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.Reached
open Lean Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Queues Queues.RxCredits

/-- Pair a supplied same-execution index contract with the original syscall's
checked accounting. This supplies no missing index-preservation premise. -/
theorem syscall_pair (call : Syscall)
    (normal : ∀ cs w h, Entry cs [] h w → ∀ result v,
      (runPrefix (RxHistory.syscall call) w h).1 = .ok (result,v) → Core v.wg) :
    PrefixPreserves AnyEntry OwnerChecks.Safe (RxHistory.syscall call) := by
  intro w h entry
  obtain ⟨cs,entry⟩ := entry
  obtain ⟨suffix,hist,safe,post⟩ := ConservationSyscall.checked call entry.1
  refine ⟨suffix,hist,safe,?_⟩
  cases run : (runPrefix (RxHistory.syscall call) w h).1 with
  | error stop => trivial
  | ok pair =>
    rw [run] at post
    obtain ⟨next,certificate,account⟩ := post
    exact ⟨next,account,normal cs w h entry pair.1 pair.2 run⟩

/-- Conditional outer composition on the existing paired runner. Actual
syscall preservation remains explicit until its caller families are discharged. -/
theorem runner_core_of_syscalls
    (calls : ∀ call, PrefixPreserves AnyEntry OwnerChecks.Safe (RxHistory.syscall call))
    (trace : Runner.Trace) (placeholders : Bool) (json : Json) (w : World)
    (history : List RxHistory.Event)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) [] =
      (.ok (json,w),history)) :
    AnyEntry history w :=
  RunnerInvariant.Normal.executeTraceWith_normal AnyEntry OwnerChecks.Safe
    anyEntry_safe anyEntry_store RxHistory.syscall calls trace placeholders
    (fun w same => ⟨[],initial_entry trace.net trace.bare w same⟩) run
end Leanux.Proofs.WG.Index.Reached
