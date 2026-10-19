import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointPhases
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointOpenFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointEnvironment
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointResidual

/-! Fixed lifecycle roots derive their phase certificate from the original
entry. Creation's temporary allocation metadata needs only the packet account;
destruction retains the actual native reference/service companions until its check.
Native atoms expose exact entry/returned cuts; finer atom interiors are not
claimed here. Five deeper callback interiors remain explicit. The environment
and descriptor-wrapper shapes are available separately, but their complete
root phase certificates are not claimed by this core coverage theorem. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
variable {native inside : ChildPoints} {Good : History → World → Prop}

inductive Root where
  | create | opened | up | down | removeAll | prepare | tail | destruct

def Root.Result : Root → Type
  | .create | .opened | .up => Int
  | _ => Unit

def Root.action (root : Root) : PrefixM Event root.Result := match root with
  | .create => liftPrefix (liftWG wgCreate)
  | .opened => liftWGObserver (Driver.openObserved hooks)
  | .up => liftWGObserver (Driver.upObserved hooks)
  | .down => liftWGObserver (Driver.downObserved hooks)
  | .removeAll => liftWGObserver (Driver.removeAllObserved hooks)
  | .prepare => liftWGObserver RetiredPeer.Lifecycle.Packet.prepareObserved
  | .tail => liftPrefix (liftWG CompleteRetired.tail)
  | .destruct => liftWGObserver (Driver.destructObserved hooks)

noncomputable def canonical (root : Root) : Shape root.action := match root with
  | .create => createShape
  | .opened => openedShape
  | .up => upShape
  | .down => downShape
  | .removeAll => removeAllShape
  | .prepare => prepareShape
  | .tail => tailShape
  | .destruct => destructShape

def Root.Entry (root : Root) (h : History) (w : World) : Prop := match root with
  | .opened | .up => CompleteProduct.Carrier h w
  | .tail => ∃ledger holders,CompleteRetired.GuardEntry h ledger holders w.wg
  | .destruct => RetiredPeer.Lifecycle.Packet.Entry h w.wg w.ambient
  | _ => Account h w

/-- No whole-tree framing premise is supplied: the literal source and its
original entry facts establish every reached phase, including reset's SAME
ledger/holder guard and the no-pending fact derived from actual guard success. -/
theorem root_framed (root : Root) (before : root.Entry h w) : Framed (canonical root) w h := by
  cases root with
  | create => exact create_framed before
  | opened => exact opened_framed before
  | up => exact up_framed before
  | down => exact down_framed before
  | removeAll => exact remove_all_ordinary.framed before
  | prepare => exact prepare_framed before
  | tail => obtain ⟨ledger,holders,guard⟩:=before; exact tail_framed guard
  | destruct => exact destruct_framed before

def Boundary : ChildPoints := fun _ _ _ _ _ _ _=>False

theorem boundary_carrier (before : Framed shape w h)
    (point : Point Boundary shape w h site u middle) : Account middle u := by
  induction point with
  | entry => exact before.account
  | returned shape performed => exact before.normal performed
  | interior _ impossible => cases impossible
  | left _ _ ih => exact ih before.1
  | right head _ leading _ ih => exact ih (before.2 _ _ _ leading)
  | marked _ _ ih => exact ih before

theorem lifecycle_execution (root : Root) {result : Result root.Result}
    (performed : runPrefix root.action w h=(result,last)) :
    Execution (canonical root) w h result last := execution_cases _ performed

theorem lifecycle_boundary (root : Root) (before : root.Entry h w)
    (point : Point Boundary (canonical root) w h site u middle) : Account middle u :=
  boundary_carrier (root_framed root before) point

theorem lifecycle_covered (root : Root)
    (accountGood : ∀ h w, Account h w → Good h w)
    (children : ChildContracts native inside Good) (before : root.Entry h w) :
    Covered native Good (canonical root) w h := covered accountGood children _ (root_framed root before)

theorem lifecycle_remainder (root : Root) (children : ChildContracts native inside Good)
    (point : Point native (canonical root) w h site u middle) :
    ∃remaining,Residual children (canonical root) w h site u middle remaining ∧
      runPrefix root.action w h=runPrefix remaining u middle := by
  obtain ⟨remaining,residual⟩ := point.residual children
  exact ⟨remaining,residual,residual.run⟩

/-- Exact native points are indexed by the selected canonical source root,
not by an arbitrary prefix/suffix factorization. -/
def RootPoints (points : ChildPoints) (root : Root) (w : World) (h : History)
    (u : World) (middle : History) : Prop :=
  ∃site,Point points (canonical root) w h site u middle

noncomputable def remainder (root : Root) (children : ChildContracts native inside Good)
    (w : World) (h : History) (u : World) (middle : History)
    (point : RootPoints native root w h u middle) : PrefixM Event root.Result :=
  Classical.choose (lifecycle_remainder root children (Classical.choose_spec point))

theorem remainder_run (root : Root) (children : ChildContracts native inside Good)
    (point : RootPoints native root w h u middle) :
    runPrefix root.action w h=runPrefix (remainder root children w h u middle point) u middle :=
  (Classical.choose_spec (lifecycle_remainder root children (Classical.choose_spec point))).2

theorem root_coverage (root : Root) (children : ChildContracts native inside Good)
    (point : RootPoints native root w h u middle) : RootPoints inside root w h u middle := by
  obtain ⟨site,point⟩ := point
  exact ⟨site,point.coverage children⟩

theorem root_safe (root : Root)
    (accountGood : ∀ h w, Account h w → Good h w)
    (children : ChildContracts native inside Good) (before : root.Entry h w)
    (point : RootPoints inside root w h u middle) : Good middle u := by
  obtain ⟨site,point⟩ := point
  exact point.safe accountGood children (root_framed root before)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
