import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerPointInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerPointLoops

/-! Initialized outer source coverage is conditional only on the five named
child point families. Native runner atoms have concrete entry/return frames;
this does not assert completeness of a child's uninstantiated interior family. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal
variable {native inside : ChildPoints} {Good : History→World→Prop}

def Boundary : ChildPoints := fun _ _ _ _ _ _ _=>False

theorem boundary_carrier (framed : Framed shape h) (point : Point Boundary shape h site u middle) :
    CompleteProduct.Carrier middle u := by
  induction point with
  | nativeEntry token => exact framed
  | nativeReturn token performed => exact token.normal framed performed
  | childEntry token => exact token.entry_carrier framed
  | childReturn token performed => exact token.normal framed performed
  | interior token impossible => cases impossible
  | left tail _ ih => exact ih framed.1
  | right head tail leading _ ih => exact ih (framed.2 _ _ leading)
  | snapshot label w body => exact framed.1
  | marked label w _ ih => exact ih framed.2

/-- Every native outer boundary and every child entry/normal return has its
actual initialized account, independently of whether the later source stops. -/
theorem initialized_boundary (trace : Trace) (placeholders : Bool)
    (point : Point Boundary (executeShape trace placeholders) [] site u middle) :
    CompleteProduct.Carrier middle u := boundary_carrier (initialized_framed trace placeholders) point

/-- Native child points must be covered at the same World and journal and
retain their original residual. No final T2 completeness is claimed until
those named child contracts are instantiated by exhaustive source families. -/
theorem initialized_covered (trace : Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w→Good h w)
    (children : ChildContracts native inside Good) :
    Covered native Good (executeShape trace placeholders) [] :=
  covered carrierGood children (initialized_framed trace placeholders)

theorem initialized_execution (trace : Trace) (placeholders : Bool)
    (performed : runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun j w=>(j,w)) trace placeholders) []=(result,last)) :
    Execution (executeShape trace placeholders) [] result last :=
  (execution_iff _).mpr performed

/-- The residual is a certificate of the original source context. Projection
forgets only the successful endpoint World and keeps an indexed Stop intact. -/
theorem original_remainder (trace : Trace) (placeholders : Bool)
    (children : ChildContracts native inside Good)
    (point : Point native (executeShape trace placeholders) [] site u middle) :
    ∃remaining,Residual children (executeShape trace placeholders) [] site u middle remaining ∧
      runPrefixOuter (CausalJournal.execute trace placeholders) []=
        ((runPrefixOuter remaining middle).1.map Prod.fst,(runPrefixOuter remaining middle).2) := by
  obtain ⟨remaining,path⟩ := point.residual children
  refine ⟨remaining,path,?_⟩
  rw [CompleteRunner.history_correspondence,path.run]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
