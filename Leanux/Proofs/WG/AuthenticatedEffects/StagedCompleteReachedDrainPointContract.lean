import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDrainPointFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDrainPointCases

/-! Conditional cut composition for the fixed send-drain body. The three child
point families must themselves be the supplied source-indexed relations for
delivery, send-worker and scheduler. Their internal coverage and cut evidence
are not inferred from endpoint preservation or arbitrary bind factorizations.
The caller's chosen Good may contain pending-receipt/selected interval evidence;
the proof never assigns an error a fictional returned world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Queues TransmitSecurity CausalJournal

abbrev ChildPoints := Child → World → History → World → History → Prop

inductive Site where
  | front (stage : FrontStage)
  | loop (count : Nat)
  | read (count : Nat)
  | childEntry (child : Child) (count : Nat)
  | childReturn (child : Child) (count : Nat)
  | childInterior (child : Child) (count : Nat)
  | finish
  | returned

/-- The only child lift is from its actual original entry. An arbitrary
factor-equation witness cannot construct a drain point. -/
inductive Point (inside : ChildPoints) (w : World) (history : History) :
    Site → World → History → Prop where
  | front (path : FrontPoint w history stage u middle) :
      Point inside w history (.front stage) u middle
  | loop (path : LoopPath w history u middle) :
      Point inside w history (.loop path.done.length) u middle
  | read (path : LoopPath w history u middle)
      (run : runPrefix (liftPrefix (liftWG getDev)) u middle = (.ok (device,v),last)) :
      Point inside w history (.read path.done.length) v last
  | childEntry (path : ChildEntry w history child u middle) :
      Point inside w history (.childEntry child path.count) u middle
  | childReturn (path : ChildEntry w history child u middle)
      (run : runPrefix child.action u middle = (.ok ((),v),last)) :
      Point inside w history (.childReturn child path.count) v last
  | childInterior (path : ChildEntry w history child u middle)
      (nativePoint : inside child u middle v last) :
      Point inside w history (.childInterior child path.count) v last
  | finish (path : FinishPath w history acc u middle) :
      Point inside w history .finish u middle
  | returned (run : runPrefix (Driver.sendWorkersObserved hooks) w history = (.ok ((),u),middle)) :
      Point inside w history .returned u middle

/-- A child's supplied native source points must be covered by its accounted
point family at exactly the same world/history. Safe endpoint transport alone
does not fill the coverage field. Both relations are explicit parameters; the
actual child-native point definitions and their fixed remaining source are
supplied by the eventual caller. The remainder equality does not itself create
a native point or establish its provenance. -/
structure ChildSourceContract (native inside : ChildPoints) (Good : History → World → Prop)
    (child : Child) where
  remainder : ∀ w h u middle, native child w h u middle → PrefixM Event Unit
  continuation : ∀ w h u middle (point : native child w h u middle),
    runPrefix child.action w h = runPrefix (remainder w h u middle point) u middle
  coverage : ∀ w h u middle, native child w h u middle → inside child w h u middle
  safe : ∀ w h u middle, CompleteProduct.Carrier h w → inside child w h u middle → Good middle u

/-- These are exactly the three open child-source obligations. No claim of
coverage for the whole mirror is made from unspecified child point families. -/
structure ChildContracts (native inside : ChildPoints) (Good : History → World → Prop) where
  delivery : ChildSourceContract native inside Good .delivery
  worker : ChildSourceContract native inside Good .worker
  scheduler : ChildSourceContract native inside Good .scheduler

variable {native inside : ChildPoints} {Good : History → World → Prop}

theorem ChildContracts.at (contracts : ChildContracts native inside Good)
    (before : CompleteProduct.Carrier h w) (accountedPoint : inside child w h u middle) : Good middle u := by
  cases child with
  | delivery => exact contracts.delivery.safe w h u middle before accountedPoint
  | worker => exact contracts.worker.safe w h u middle before accountedPoint
  | scheduler => exact contracts.scheduler.safe w h u middle before accountedPoint

theorem ChildContracts.coverage (contracts : ChildContracts native inside Good)
    (nativePoint : native child w h u middle) : inside child w h u middle := by
  cases child with
  | delivery => exact contracts.delivery.coverage w h u middle nativePoint
  | worker => exact contracts.worker.coverage w h u middle nativePoint
  | scheduler => exact contracts.scheduler.coverage w h u middle nativePoint

def ChildContracts.remainder (contracts : ChildContracts native inside Good)
    (point : native child w h u middle) : PrefixM Event Unit := by
  cases child with
  | delivery => exact contracts.delivery.remainder w h u middle point
  | worker => exact contracts.worker.remainder w h u middle point
  | scheduler => exact contracts.scheduler.remainder w h u middle point

theorem ChildContracts.continuation (contracts : ChildContracts native inside Good)
    (point : native child w h u middle) :
    runPrefix child.action w h = runPrefix (contracts.remainder point) u middle := by
  cases child with
  | delivery => exact contracts.delivery.continuation w h u middle point
  | worker => exact contracts.worker.continuation w h u middle point
  | scheduler => exact contracts.scheduler.continuation w h u middle point

/-- An already supplied child-native point keeps the enclosing drain's literal
continuation. This is context transport, not a constructor of native points. -/
theorem ChildEntry.interior_continuation (path : ChildEntry w history child u middle)
    (contracts : ChildContracts native inside Good) (point : native child u middle v last) :
    runPrefix (Driver.sendWorkersObserved hooks) w history =
      runPrefix (contracts.remainder point >>= fun _ => path.after) v last := by
  rw [path.continuation]
  exact Scheduler.bind_run_equal (fun _ => path.after) (contracts.continuation point)

/-- Coverage changes only the child's evidence; it retains the same source
entry, enclosing index, actual cut world and history. -/
theorem Point.coverage (contracts : ChildContracts native inside Good)
    (point : Point native w history site u middle) : Point inside w history site u middle := by
  cases point with
  | front path => exact .front path
  | loop path => exact .loop path
  | read path run => exact .read path run
  | childEntry path => exact .childEntry path
  | childReturn path run => exact .childReturn path run
  | childInterior path nativePoint => exact .childInterior path (contracts.coverage nativePoint)
  | finish path => exact .finish path
  | returned run => exact .returned run

/-- Every fixed drain point satisfies the chosen account/interval claim,
conditional on the three children's own source-point contracts. Normal and
stopped runs use the same relation; no eventual-drain premise is present. -/
theorem point_safe (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (before : CompleteProduct.Carrier history w)
    (point : Point inside w history site u middle) : Good middle u := by
  cases point with
  | front path => exact carrierGood _ _ (path.carrier before)
  | loop path => exact carrierGood _ _ (path.carrier before)
  | read path run =>
      exact carrierGood _ _ (Scheduler.checked_normal read_checked (path.carrier before) run)
  | childEntry path => exact carrierGood _ _ (path.carrier before)
  | childReturn path run => exact carrierGood _ _ (path.return_carrier before run)
  | childInterior path nativePoint => exact children.at (path.carrier before) nativePoint
  | finish path => exact carrierGood _ _ (path.carrier before)
  | returned run => exact carrierGood _ _ (Scheduler.checked_normal drain_checked before run)

def Covered (inside : ChildPoints) (Good : History → World → Prop) (w : World) (history : History) : Prop :=
  ∀ site u middle, Point inside w history site u middle → Good middle u

theorem covered (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (before : CompleteProduct.Carrier history w) :
    Covered inside Good w history := fun _ _ _ point => point_safe carrierGood children before point

theorem native_covered (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (before : CompleteProduct.Carrier history w) :
    Covered native Good w history := fun _ _ _ point =>
  point_safe carrierGood children before (point.coverage children)

/-- The actual drain has a complete source decomposition and satisfies all of
its fixed points, including supplied child interiors. The three child-native
coverage obligations remain explicit; this is not initialized T2 completeness. -/
theorem original_covered (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) (before : CompleteProduct.Carrier history w)
    (performed : runPrefix (Driver.sendWorkersObserved hooks) w history = (result,last)) :
    Execution w history result last ∧ Covered native Good w history ∧ Covered inside Good w history :=
  ⟨execution_cases performed,native_covered carrierGood children before,covered carrierGood children before⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain.Points
