import Leanux.Proofs.WG.Progress.RunnerInitialFiniteSource
import Leanux.Proofs.WG.Progress.SyscallFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RunnerFinite
open Lean Leanux Leanux.Runner

/-- Original operation boundary with only its syscall callback exposed.
The actual record installation and four completion guards remain literal. -/
def operationWith (invoke : Syscall → Leanux.M Int) (trace : Trace) (op : Operation) (state : RunnerAccumulator) :
    Except (Nat × Stop) (Int × World) := do
  let world := state.1
  let results := state.2.1
  let ends := state.2.2.1
  let index := results.size
  let ahead := trace.hidden.map fun h => (h.drop (index + 1)).toList   -- B3, E2's lookahead
  let world := { world with
    ambient := { world.ambient with hidden := trace.hidden.map (·[index]!) }
    fixture := { world.fixture with hiddenAhead := ahead }
    wg := { world.wg with netRxRaised := false } }
  let (ret, w) ← (invoke (toSyscall results ends index op)).run world
    |>.mapError fun e => (index, e)
  let (_, w) ← (skipAmbient : M Unit).run w |>.mapError fun e => (index, e)
  if let some (r :: _) := w.ambient.hidden then
    throw (index, .hidden s!"a record of site {r.site} was not consumed")
  if let a :: _ := w.ambient.suspended then
    throw (index, .hidden s!"{a.worker.symbol} is still suspended at the end of the operation (its stop has no record)")
  if w.ambient.hidden.isSome then
    if let i :: _ := w.ambient.pendingWork then
      let name := ((Worker.all.find? (·.index == i)).map (·.symbol)).getD s!"unit {i}"
      throw (index, .hidden s!"{name} is pending at the end of the operation (the dispatch its requeue causes has no section in the records)")
  if w.wg.netRxRaised then
    throw (index, .invariant "a NET_RX softirq raised by a loopback transmission was left pending")
  return (ret, w)

theorem operation_factor (trace : Trace) (op : Operation) (state : RunnerAccumulator) :
    runnerOperation trace op state = operationWith Leanux.syscall trace op state := rfl

def operation := operationWith SyscallFinite.call

theorem operation_source (trace : Trace) (op : Operation) (state : RunnerAccumulator) :
    runnerOperation trace op state = operation trace op state := by
  rw [operation_factor, funext SyscallFinite.call_source]
  rfl

/-- One finite operation followed by the original finite presentation loops. -/
def step (trace : Trace) (op : Operation) (state : RunnerAccumulator) :
    Except (Nat × Stop) (ForInStep RunnerAccumulator) := do
  let (ret, w) ← operation trace op state
  runnerPresent op state ret w

theorem step_source (trace : Trace) (op : Operation) (state : RunnerAccumulator) :
    runnerStep trace op state = step trace op state := by
  rw [runnerStep_operation_source, operation_source]
  rfl

/-- Finite trace evaluation: finite initialization, a finite operation-array
traversal with the concrete finite syscall, and original finite rendering.
Every native Stop, including an exhausted guard, remains unchanged. -/
def executeTrace (trace : Trace) (placeholders : Bool) : Except (Nat × Stop) Json := do
  let seed ← initial trace placeholders
  let final ← forIn trace.ops ((seed, #[], #[], #[], #[], #[]) : RunnerAccumulator)
    (step trace)
  runnerFinish trace final

theorem executeTrace_source (trace : Trace) (placeholders : Bool) :
    Runner.executeTrace trace placeholders = executeTrace trace placeholders := by
  rw [← executeTrace_boundary_source]
  unfold runnerBoundarySource executeTrace
  rw [initial_source]
  have steps : runnerStep trace = step trace :=
    funext fun op => funext (step_source trace op)
  rw [steps]

end Leanux.Proofs.WG.Progress.RunnerFinite
