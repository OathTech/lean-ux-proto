import Leanux.Proofs.WG.Roaming.HandshakeAttemptSyscallSource
import Leanux.Proofs.WG.Queues.JointRunner
import Leanux.Proofs.WG.Origins.RunnerInvariant

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeAttemptTransport
open Leanux Leanux.WG Leanux.Proofs.Logged Queues Lifetimes Configuration
variable {Attempt : Type} {valid : List Attempt → Prop}

namespace Initialized

def observed (r : Receive Attempt valid) (trace : Runner.Trace) (placeholders : Bool) :
    PrefixOuter (Event Attempt) Lean.Json :=
  RxHistory.executeTraceWith (Syscalls.call r) trace placeholders


def history (r : Receive Attempt valid) (trace : Runner.Trace) (placeholders : Bool) :
    List (Event Attempt) :=
  (runPrefixOuter (observed r trace placeholders) []).2

def outcome (r : Receive Attempt valid) (trace : Runner.Trace) (placeholders : Bool) :
    Except (Nat × Stop) Lean.Json :=
  (runPrefixOuter (observed r trace placeholders) []).1

theorem safe (r : Receive Attempt valid) (empty : valid [])
    (trace : Runner.Trace) (placeholders : Bool) :
    Safe valid (history r trace placeholders) :=
  RunnerInvariant.executeTraceWith (fun h _=>Safe valid h) (Safe valid)
    (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) (Syscalls.call r) (Syscalls.call_preserves r)
    trace placeholders (fun _ _=>empty)

theorem projects (r : Receive Attempt valid) (trace : Runner.Trace) (placeholders : Bool) :
    ProjectsOuter rxEvent id (observed r trace placeholders) (RxHistory.executeTraceHistory trace placeholders) := by
  change ProjectsOuter rxEvent id (RxHistory.executeTraceWith _ _ _) (RxHistory.executeTraceWith _ _ _)
  rw [RoutingJoint.executeTrace_rx_factor,RoutingJoint.executeTrace_rx_factor]
  exact RoutingJoint.executeTraceWith_projects rxEvent id (Syscalls.call r) RxHistory.syscall
    (fun j _=>j) (fun j _=>j) (Syscalls.call_projects r) (fun _ _=>rfl) trace placeholders

theorem erases (r : Receive Attempt valid) (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (observed r trace placeholders) (Runner.executeTrace trace placeholders) := by
  intro h
  have same := congrArg Prod.fst (projects r trace placeholders h)
  simp only [Except.map_id] at same
  exact same.symm.trans (RxHistory.executeTraceHistory_erases trace placeholders (h.filterMap rxEvent))

theorem history_rx (r : Receive Attempt valid) (trace : Runner.Trace) (placeholders : Bool) :
    (history r trace placeholders).filterMap rxEvent =
      (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 :=
  (congrArg Prod.snd (projects r trace placeholders [])).symm


theorem outcome_original (r : Receive Attempt valid) (trace : Runner.Trace) (placeholders : Bool) :
    outcome r trace placeholders = Runner.executeTrace trace placeholders :=
  erases r trace placeholders []

end Initialized
end Leanux.Proofs.WG.Roaming.HandshakeAttemptTransport
