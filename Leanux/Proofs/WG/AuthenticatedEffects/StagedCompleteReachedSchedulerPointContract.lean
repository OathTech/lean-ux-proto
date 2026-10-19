import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerPointExecution
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerPointFrames

/-! Fixed-source point composition. The shape parameter is data, not a proof
whose irrelevance could identify arbitrary factorizations. Public scheduler
contracts specialize it to the canonical original-source witnesses. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev ChildPoints := (α : Type) → (action : PrefixM Event α) → Child action →
  World → History → World → History → Prop

inductive Site where
  | entry
  | returned
  | interior
  | left (site : Site)
  | right (site : Site)
  | marked (label : Label) (site : Site)

inductive Point (inside : ChildPoints) : {α : Type} → {action : PrefixM Event α} →
    Shape action → World → History → Site → World → History → Prop where
  | entry (shape : Shape action) : Point inside shape w h .entry w h
  | returned (shape : Shape action)
      (performed : runPrefix action w h = (.ok (value,u),middle)) :
      Point inside shape w h .returned u middle
  | interior (token : Child action) (point : inside _ _ token w h u middle) :
      Point inside (.child token) w h .interior u middle
  | left {body : PrefixM Event α} {next : α → PrefixM Event β}
      {head : Shape body} (tail : ∀ value, Shape (next value)) (point : Point inside head w h site u middle) :
      Point inside (.bind head tail) w h (.left site) u middle
  | right {body : PrefixM Event α} {next : α → PrefixM Event β} (head : Shape body)
      (tail : ∀ value, Shape (next value))
      (leading : runPrefix body w h = (.ok (value,u),middle))
      (point : Point inside (tail value) u middle site v last) :
      Point inside (.bind head tail) w h (.right site) v last
  | marked (label : Label) (point : Point inside shape w h site u middle) :
      Point inside (.marked label shape) w h (.marked label site) u middle

/-- Each supplied child family must cover its actual native source points at
exactly the same world and history and retain its original continuation.
Continuation equality never constructs a point. -/
structure ChildSourceContract (native inside : ChildPoints) (Good : History → World → Prop)
    {α : Type} {action : PrefixM Event α} (token : Child action) where
  remainder : ∀ w h u middle, native _ _ token w h u middle → PrefixM Event α
  continuation : ∀ w h u middle (point : native _ _ token w h u middle),
    runPrefix action w h = runPrefix (remainder w h u middle point) u middle
  coverage : ∀ w h u middle, native _ _ token w h u middle → inside _ _ token w h u middle
  safe : ∀ w h u middle, CompleteProduct.Carrier h w → inside _ _ token w h u middle → Good middle u

/-- Only committed activations and committed NAPI are children. Native
consistency trials have a checked store frame and no child activation. -/
structure ChildContracts (native inside : ChildPoints) (Good : History → World → Prop) where
  iteration : ∀ a, ChildSourceContract native inside Good (.iteration a)
  napi : ChildSourceContract native inside Good .napi

variable {native inside : ChildPoints} {Good : History → World → Prop}

def ChildContracts.at (contracts : ChildContracts native inside Good) (token : Child action) :
    ChildSourceContract native inside Good token := by
  cases token with
  | iteration a => exact contracts.iteration a
  | napi => exact contracts.napi

theorem Point.coverage (contracts : ChildContracts native inside Good)
    (point : Point native shape w h site u middle) : Point inside shape w h site u middle := by
  induction point with
  | entry shape => exact .entry shape
  | returned shape performed => exact .returned shape performed
  | interior token point => exact .interior token ((contracts.at token).coverage _ _ _ _ point)
  | left tail point ih => exact .left tail ih
  | right head tail leading point ih => exact .right head tail leading ih
  | marked label point ih => exact .marked label ih

/-- Coverage uses the original successful bind prefix. Failed actions have no
returned world; their entry and any supplied actual interior remain available. -/
theorem Point.safe (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (contracts : ChildContracts native inside Good) (before : CompleteProduct.Carrier h w)
    (point : Point inside shape w h site u middle) : Good middle u := by
  induction point with
  | entry shape => exact carrierGood _ _ before
  | returned shape performed => exact carrierGood _ _ (shape.normal before performed)
  | interior token point => exact (contracts.at token).safe _ _ _ _ before point
  | left tail point ih => exact ih before
  | right head tail leading point ih => exact ih (head.normal before leading)
  | marked label point ih => exact ih before


def Covered (inside : ChildPoints) (Good : History → World → Prop)
    (shape : Shape action) (w : World) (h : History) : Prop :=
  ∀ site u middle, Point inside shape w h site u middle → Good middle u

theorem covered (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (contracts : ChildContracts native inside Good) (shape : Shape action)
    (before : CompleteProduct.Carrier h w) : Covered native Good shape w h :=
  fun _ _ _ point => Point.safe carrierGood contracts before (point.coverage contracts)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler.Points
