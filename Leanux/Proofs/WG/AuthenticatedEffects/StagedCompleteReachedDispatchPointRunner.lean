import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchPointCoverage

/-! A direct refinement of RunnerPoint's dispatch child. Its point witnesses
are fixed canonical dispatch syntax, and the constructed remainder is the
original continuation. Other runner child families remain separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal
variable {native inside : ChildPoints} {Good : History → World → Prop}

def RunnerPoints (points : ChildPoints) : Runner.Points.ChildPoints :=
  fun _ _ token w h u middle => match token with
  | .dispatch call => ∃site,Point points (canonical call) w h site u middle
  | .sends | .idle | .afterXmit | .advance => False

noncomputable def runnerRemainder (call : Syscall) (children : ChildContracts native inside Good)
    (w : World) (h : History) (u : World) (middle : History)
    (point : RunnerPoints native _ _ (.dispatch call) w h u middle) : PrefixM Event Int :=
  Classical.choose (dispatch_remainder call children (Classical.choose_spec point))

theorem runner_remainder (call : Syscall) (children : ChildContracts native inside Good)
    (point : RunnerPoints native _ _ (.dispatch call) w h u middle) :
    runPrefix (Driver.dispatchObserved hooks call) w h=
      runPrefix (runnerRemainder call children w h u middle point) u middle :=
  (Classical.choose_spec (dispatch_remainder call children (Classical.choose_spec point))).2

/-- The Runner dispatch child is discharged from exactly the finite named WG
source-family contracts. Native frames are concrete; no contract for dispatch
itself and no arbitrary successful factorization is an incoming premise. -/
noncomputable def runner_dispatch_contract (call : Syscall)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w→Good h w)
    (children : ChildContracts native inside Good) :
    Runner.Points.ChildSourceContract (RunnerPoints native) (RunnerPoints inside) Good (.dispatch call) where
  remainder := runnerRemainder call children
  continuation := fun _ _ _ _ point=>runner_remainder call children point
  coverage := by
    intro w h u middle point
    obtain ⟨site,point⟩ := point
    exact ⟨site,point.coverage children⟩
  safe := by
    intro w h u middle before point
    obtain ⟨site,point⟩ := point
    exact point.safe carrierGood children (canonical_framed call before)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Dispatch.Points
