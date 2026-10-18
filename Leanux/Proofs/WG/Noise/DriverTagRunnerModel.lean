import Leanux.Proofs.WG.Noise.DriverTagProductClaims
import Leanux.Proofs.WG.Origins.NormalRunnerInvariant
import Leanux.Proofs.WG.Queues.JointRunner

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Initialized
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Configuration Origins.HistorySupport Std.Do

def emptyTags : TagMap := fun _ => none

/-- Only the actual paired source's normal state is projected; Stops retain
their operation index and the completed journal. -/
abbrev Inspection := Except (Nat × Stop) (Json × Campaign2.Snapshot) × List DriverTagEvent

def Facts (out : Inspection) : Prop :=
  ValidHistory out.2 ∧ match out.1 with
    | .error _ => True
    | .ok (_,final) => DriverTagMapCoverage emptyTags out.2 final.tagAt


end Leanux.Proofs.WG.Noise.DriverTags.Initialized
