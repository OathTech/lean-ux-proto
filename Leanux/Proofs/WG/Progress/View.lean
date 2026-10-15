import Leanux.Proofs.WG.Progress.Model
import Leanux.Env.Batch

/-! Data-only observations for the scheduler claims. Each execution observation
is supplied by ObservationBridge from the same concrete entry, never by filling
omitted subsystem state with defaults. -/
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Campaign2

def mapOutcome (f : α → β) (out : Outcome α) : Outcome β :=
  out.map fun (value, state) => (f value, state)

def probeOutcome (entry : Snapshot) : Outcome Unit → Outcome Bool
  | .ok _ => .ok (true, entry)
  | .error (.hidden _) => .ok (false, entry)
  | .error err => .error err

structure ProbeObservation where
  probe : Outcome Bool
  activation : Outcome Unit

structure DispatchTrace where
  pid : Option Nat
  selected : Snapshot
  bytes : List UInt8
  started : Snapshot

structure DispatchObservation where
  actual : Outcome Bool
  selection : Outcome (Option (Option Nat))
  traced : Outcome (Option DispatchTrace)

structure CandidateObservation where
  actual : Outcome (List Activation)
  probes : Activation → Outcome Unit

def successful (out : Outcome α) : Bool :=
  match out with | .ok _ => true | .error _ => false

structure TurnAfterPeek where
  state : Snapshot
  next : Option Nat
  candidates : Outcome (List Activation)
  guard : Worker → Outcome Bool
  resumed : Activation → Outcome TurnResult
  dispatch : Worker → DispatchObservation
  napi : Outcome (Snapshot × Option Nat)

structure TurnObservation where
  actual : Outcome TurnResult
  afterPeek : Except Stop TurnAfterPeek

def NoStart (o : TurnAfterPeek) : Prop :=
  ∀ worker, o.next.bind sectionOf ≠ some (worker, true)

def PollReady (o : TurnAfterPeek) (d : Device) : Bool :=
  o.next == some (HiddenSite.sectionStart .netRx).info.id &&
    d.peers.toList.any (·.2.napiScheduled)

def ResumeBranch (o : TurnAfterPeek) (d : Device) : Prop :=
  NoStart o ∧ o.state.wg.device = some d ∧ PollReady o d = false

def ambiguity (s : Snapshot) : Stop :=
  .outsideDomain (match s.ambient.steps.back? with
    | some step => s!"{step.decision.info.file}:{step.decision.info.line}"
    | none => "syscall entry")
    "the records do not determine which suspended worker resumed"

def napiResult (out : Snapshot × Option Nat) : TurnResult :=
  if out.2 == some (HiddenSite.sectionStart .netRx).info.id then turnReturn else turnContinue

end Leanux.Proofs.WG.Progress
