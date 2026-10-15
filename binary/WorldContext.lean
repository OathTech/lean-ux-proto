import WorldParts
import LookupObservation

namespace Binary.WorldContext
open Leanux

/-- Incoming non-physical context for one anchored lookup. This value stays
    fixed throughout that invocation. It contains no Kernel, pending work,
    routing state or suspended activation. Knowledge still needs its incoming
    lifetime/clock provenance; it cannot encode current physical state. -/
structure Context where
  supplied : WorldParts.Supplied
  fixture : WorldParts.Fixture
  history : WorldParts.History
  knowledge : WorldParts.Knowledge

def incoming (world : World) : Context :=
  ⟨WorldParts.supplied world, WorldParts.fixture world,
    WorldParts.history world, WorldParts.knowledge world⟩

/-- Decisions are taken from the actual machine observer's event prefix.
    Calls and returns have no decision record. No expected source stream is
    an argument. The caller must establish that these events were observed. -/
def steps (events : List LookupObservation.Point) : Array Step :=
  (events.filterMap (·.step)).toArray

def At (context : Context) (events : List LookupObservation.Point) (world : World) : Prop :=
  WorldParts.supplied world = context.supplied ∧
  WorldParts.fixture world = context.fixture ∧
  WorldParts.history world = {context.history with steps := context.history.steps ++ steps events} ∧
  WorldParts.knowledge world = context.knowledge

theorem at_entry (world : World) : At (incoming world) [] world := by
  simp [At, incoming, steps]

/-- This frame changes only the physical Kernel component. It says nothing
    about whether the new Kernel is physically represented. -/
theorem At.kernel_update {context events world} (represented : At context events world)
    (kernel : Kernel) : At context events {world with k := kernel} := represented

theorem steps_append (first second : List LookupObservation.Point) :
    steps (first ++ second) = steps first ++ steps second := by
  simp [steps, List.filterMap_append]

theorem steps_call (symbol : String) (machine : MachineState) :
    steps [LookupObservation.call symbol machine] = #[] := rfl

theorem steps_returned (symbol : String) (machine : MachineState) :
    steps [LookupObservation.returned symbol machine] = #[] := rfl

theorem steps_decision (rxSection : Nat) (decision : Decision) (outcome : Bool)
    (machine : MachineState) (operands : Option (Int × Int)) :
    steps [LookupObservation.decision rxSection decision outcome machine operands] =
      #[{decision, outcome, operands, netRx := rxSection}] := rfl

/-- A real source record and its matching observed edge advance only the
    history equation. The fixed incoming context is not rebound. -/
theorem At.decision {context events world} (represented : At context events world)
    (decision : Decision) (outcome : Bool) (machine : MachineState)
    (operands : Option (Int × Int)) :
    At context (events ++ [LookupObservation.decision world.netRxSection decision outcome machine operands])
      {world with steps := world.steps.push {decision, outcome, operands, netRx := world.netRxSection}} := by
  obtain ⟨supplied, fixture, history, knowledge⟩ := represented
  refine ⟨supplied, fixture, ?_, knowledge⟩
  have oldSteps := congrArg WorldParts.History.steps history
  change world.steps = context.history.steps ++ steps events at oldSteps
  have update : WorldParts.history
      {world with steps := world.steps.push {decision, outcome, operands, netRx := world.netRxSection}} =
      {WorldParts.history world with steps := world.steps.push {decision, outcome, operands, netRx := world.netRxSection}} := rfl
  rw [update, history, oldSteps, steps_append, steps_decision]
  congr 1
  simp

theorem At.call {context events world} (represented : At context events world)
    (symbol : String) (machine : MachineState) :
    At context (events ++ [LookupObservation.call symbol machine]) world := by
  simpa only [At, steps_append, steps_call, Array.append_empty] using represented

theorem At.returned {context events world} (represented : At context events world)
    (symbol : String) (machine : MachineState) :
    At context (events ++ [LookupObservation.returned symbol machine]) world := by
  simpa only [At, steps_append, steps_returned, Array.append_empty] using represented

/-- Once a concrete physical relation determines the remaining component,
    these equations determine the entire World, including function-valued
    supplied environment. This is not itself a physical representation. -/
theorem At.functional {context events first second}
    (hf : At context events first) (hs : At context events second)
    (physical : WorldParts.physical first = WorldParts.physical second) : first = second := by
  apply WorldParts.split_injective
  simp only [WorldParts.split, physical, hf.1.trans hs.1.symm,
    hf.2.1.trans hs.2.1.symm, hf.2.2.1.trans hs.2.2.1.symm, hf.2.2.2.trans hs.2.2.2.symm]

/-- All events observed so far, suitable at an endpoint. This is not the
    intermediate source point between two events emitted by one machine edge.
    Execution is proved separately by historyStep, not by this predicate. -/
def Observed (context : Context) (history : List MachineState) (world : World) : Prop :=
  ∃ events, LookupObservation.observe context.history.netRxSection history = .ok events ∧
    At context events world

theorem Observed.functional {context history first second}
    (hf : Observed context history first) (hs : Observed context history second)
    (physical : WorldParts.physical first = WorldParts.physical second) : first = second := by
  obtain ⟨events, seen, hf⟩ := hf
  obtain ⟨other, seenOther, hs⟩ := hs
  have equal : events = other := Except.ok.inj (seen.symm.trans seenOther)
  subst other
  exact hf.functional hs physical

/-- A semantic event cursor handles compiler-merged edges: the first source
    point can precede a second event emitted at the same physical state.
    The selected point must actually occur in the observer output and name
    this machine state; the cursor cannot manufacture or reorder events. -/
def ObservedPoint (context : Context) (history : List MachineState) (cursor : Nat)
    (machine : MachineState) (world : World) : Prop :=
  ∃ events point,
    LookupObservation.observe context.history.netRxSection history = .ok events ∧
    events[cursor]? = some point ∧ point.machine = machine ∧
    At context (events.take (cursor + 1)) world

theorem ObservedPoint.functional {context history cursor machine first second}
    (hf : ObservedPoint context history cursor machine first)
    (hs : ObservedPoint context history cursor machine second)
    (physical : WorldParts.physical first = WorldParts.physical second) : first = second := by
  obtain ⟨events, _, seen, _, _, hf⟩ := hf
  obtain ⟨other, _, seenOther, _, _, hs⟩ := hs
  have equal : events = other := Except.ok.inj (seen.symm.trans seenOther)
  subst other
  exact hf.functional hs physical

#print axioms at_entry
#print axioms At.kernel_update
#print axioms steps_append
#print axioms At.decision
#print axioms At.call
#print axioms At.returned
#print axioms At.functional
#print axioms Observed.functional
#print axioms ObservedPoint.functional
end Binary.WorldContext
