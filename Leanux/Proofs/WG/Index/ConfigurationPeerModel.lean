import Leanux.Proofs.WG.Index.ConfigurationIndexModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

def ExitState (P Q : WGWorld → Prop) (acc : Option Int × Int) : WGWorld → Prop :=
  match acc.1 with
  | none => P
  | some _ => Q

def ExitStep (P Q : WGWorld → Prop) (step : ForInStep (Option Int × Int)) : WGWorld → Prop :=
  match step with
  | .done acc => ExitState P Q acc
  | .yield acc => fun w=>acc.1=none ∧ P w


/-- Result-indexed exit and yielding-state predicates for the unchanged native accumulator. -/
def ResultExitState (P Q : Int → WGWorld → Prop) (acc : Option Int × Int) : WGWorld → Prop :=
  match acc.1 with
  | none=>P acc.2
  | some result=>Q result

def ResultExitStep (P Q : Int → WGWorld → Prop)
    (step : ForInStep (Option Int × Int)) : WGWorld → Prop :=
  match step with
  | .done acc=>ResultExitState P Q acc
  | .yield acc=>fun w=>acc.1=none ∧ P acc.2 w

end Leanux.Proofs.WG.Index.ConfigurationIndex
