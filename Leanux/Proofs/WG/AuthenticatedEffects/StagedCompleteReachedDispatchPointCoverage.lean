import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchPointResidual

/-! Dispatch coverage refines a fixed Runner child. The claim is conditional
on named interior source contracts, never on a second dispatch contract.
Native subsystem atoms expose actual entry and normal-return boundaries here;
this interface does not claim every primitive interior of their source bodies. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal
variable {native inside : ChildPoints} {Good : History → World → Prop}

def Boundary : ChildPoints := fun _ _ _ _ _ _ _=>False

theorem boundary_carrier (before : Framed shape w h)
    (point : Point Boundary shape w h site u middle) : CompleteProduct.Carrier middle u := by
  induction point with
  | entry => exact before.carrier
  | returned _ performed => exact before.normal performed
  | interior _ impossible => cases impossible
  | stored point => exact point.carrier before
  | left _ _ ih => exact ih before.1
  | right _ _ leading _ ih => exact ih (before.2 _ _ _ leading)
  | marked _ _ ih => exact ih before

/-- Every original dispatch result is decomposed by its canonical source
witness, including failed prefixes and errno returns. -/
theorem dispatch_execution (call : Syscall)
    (performed : runPrefix (Driver.dispatchObserved hooks call) w h=(result,last)) :
    Execution (canonical call) w h result last := execution_cases _ performed

/-- Actual entry and normal-return boundaries retain the account at the
same native World and journal, with the original deletion companion. -/
theorem dispatch_boundary (call : Syscall)
    (before : Runner.Points.Child.Entry (.dispatch call) h w)
    (point : Point Boundary (canonical call) w h site u middle) : CompleteProduct.Carrier middle u :=
  boundary_carrier (canonical_framed call before) point

theorem dispatch_covered (call : Syscall)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w→Good h w)
    (children : ChildContracts native inside Good)
    (before : Runner.Points.Child.Entry (.dispatch call) h w) :
    Covered native Good (canonical call) w h := covered carrierGood children _ (canonical_framed call before)

theorem dispatch_remainder (call : Syscall) (children : ChildContracts native inside Good)
    (point : Point native (canonical call) w h site u middle) :
    ∃remaining,Residual children (canonical call) w h site u middle remaining ∧
      runPrefix (Driver.dispatchObserved hooks call) w h=runPrefix remaining u middle := by
  obtain ⟨remaining,residual⟩ := point.residual children
  exact ⟨remaining,residual,residual.run⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
