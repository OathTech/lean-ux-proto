import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointCoverage

/-! Shared idle/advance/delivery refinements for the literal Runner and
Dispatch children. Unsupported outer children have no point constructor in
these embeddings. No deletion companion is dropped: deletion is not a service
root and remains the separate Dispatch contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Points
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal
variable {native inside : ChildPoints} {Good : History → World → Prop}

def RunnerPoints (points : ChildPoints) : Runner.Points.ChildPoints :=
  fun _ _ token w h u middle => match token with
  | .idle => RootPoints points .idle w h u middle
  | .advance => RootPoints points .advance w h u middle
  | .dispatch _ | .sends | .afterXmit => False

def DispatchPoints (points : ChildPoints) : Dispatch.Points.ChildPoints :=
  fun _ _ token w h u middle => match token with
  | .family .idle => RootPoints points .idle w h u middle
  | .family .delivery => RootPoints points .delivery w h u middle
  | .family (.config _) | .family .create | .family .delete | .family .open
  | .family .down | .family (.transmit ..) | .family (.receive ..)
  | .family (.flood ..) | .family (.batch _) | .family (.dumpDevice _)
  | .family (.dumpStart ..) | .family (.dumpReceive _) => False

noncomputable def runner_idle_contract
    (carrierGood : ∀ h w,CompleteProduct.Carrier h w→Good h w)
    (children : ChildContracts native inside Good) :
    Runner.Points.ChildSourceContract (RunnerPoints native) (RunnerPoints inside) Good .idle where
  remainder := remainder .idle children
  continuation := fun _ _ _ _ point=>remainder_run .idle children point
  coverage := fun _ _ _ _ point=>root_coverage .idle children point
  safe := fun _ _ _ _ before point=>root_safe .idle carrierGood children before point

noncomputable def runner_advance_contract
    (carrierGood : ∀ h w,CompleteProduct.Carrier h w→Good h w)
    (children : ChildContracts native inside Good) :
    Runner.Points.ChildSourceContract (RunnerPoints native) (RunnerPoints inside) Good .advance where
  remainder := remainder .advance children
  continuation := fun _ _ _ _ point=>remainder_run .advance children point
  coverage := fun _ _ _ _ point=>root_coverage .advance children point
  safe := fun _ _ _ _ before point=>root_safe .advance carrierGood children before point

noncomputable def dispatch_idle_contract
    (carrierGood : ∀ h w,CompleteProduct.Carrier h w→Good h w)
    (children : ChildContracts native inside Good) :
    Dispatch.Points.ChildSourceContract (DispatchPoints native) (DispatchPoints inside) Good (.family .idle) where
  remainder := remainder .idle children
  continuation := fun _ _ _ _ point=>remainder_run .idle children point
  coverage := fun _ _ _ _ point=>root_coverage .idle children point
  safe := fun _ _ _ _ before point=>root_safe .idle carrierGood children before point

noncomputable def dispatch_delivery_contract
    (carrierGood : ∀ h w,CompleteProduct.Carrier h w→Good h w)
    (children : ChildContracts native inside Good) :
    Dispatch.Points.ChildSourceContract (DispatchPoints native) (DispatchPoints inside) Good (.family .delivery) where
  remainder := remainder .delivery children
  continuation := fun _ _ _ _ point=>remainder_run .delivery children point
  coverage := fun _ _ _ _ point=>root_coverage .delivery children point
  safe := fun _ _ _ _ before point=>root_safe .delivery carrierGood children before point

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Points
