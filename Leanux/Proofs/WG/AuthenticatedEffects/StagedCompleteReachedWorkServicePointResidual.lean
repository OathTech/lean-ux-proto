import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointContract

/-! Source-constructed remainders retain the actual surrounding binds. An
arbitrary equal-run action cannot construct this relation. The sole open leaf
remainders are those of the explicit native-child source contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

inductive Residual {native inside : ChildPoints} {Good : History → World → Prop}
    (children : ChildContracts native inside Good) :
    {α : Type} → {action : PrefixM Event α} → Shape action →
    World → History → Site → World → History → PrefixM Event α → Prop where
  | entry (shape : Shape action) : Residual children shape w h .entry w h action
  | returned (shape : Shape action)
      (performed : runPrefix action w h = (.ok (value,u),middle)) :
      Residual children shape w h .returned u middle (pure value)
  | leaf (source : Consume.Leaf.Shape action)
      (remaining : Consume.Leaf.Residual leafContracts source w h site u middle remainder) :
      Residual children (.leaf source) w h (.leaf site) u middle remainder
  | acquire {w : World} (point : SavedCall.AcquirePoint pid w.wg w.ambient v b) :
      Residual children (.native (.acquire pid)) w h .acquire {w with wg:=v,ambient:=b} h
        (SavedCall.acquireRemainder h point)
  | interior (token : Child) (point : native token w h u middle) :
      Residual children (.child token) w h .interior u middle
        ((children.contract token).remainder w h u middle point)
  | left {body : PrefixM Event α} {next : α → PrefixM Event β} {head : Shape body}
      (tail : ∀ value, Shape (next value))
      (remaining : Residual children head w h site u middle remainder) :
      Residual children (.bind head tail) w h (.left site) u middle (remainder >>= next)
  | right {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value))
      (leading : runPrefix body w h = (.ok (value,u),middle))
      (remaining : Residual children (tail value) u middle site v last remainder) :
      Residual children (.bind head tail) w h (.right site) v last remainder
  | marked (label : Label) (remaining : Residual children shape w h site u middle remainder) :
      Residual children (.marked label shape) w h (.marked label site) u middle remainder

variable {native inside : ChildPoints} {Good : History → World → Prop}
variable {children : ChildContracts native inside Good}

theorem Point.residual (children : ChildContracts native inside Good)
    (point : Point native shape w h site u middle) :
    ∃ remaining, Residual children shape w h site u middle remaining := by
  induction point with
  | entry shape => exact ⟨_,.entry shape⟩
  | returned shape performed => exact ⟨_,.returned shape performed⟩
  | acquire point => exact ⟨_,.acquire point⟩
  | leaf source point =>
      obtain ⟨remaining,residual⟩ := point.residual leafContracts
      exact ⟨_,.leaf source residual⟩
  | interior token point => exact ⟨_,.interior token point⟩
  | left tail point ih =>
      obtain ⟨remaining,residual⟩ := ih
      exact ⟨_,.left tail residual⟩
  | right head tail leading point ih =>
      obtain ⟨remaining,residual⟩ := ih
      exact ⟨_,.right head tail leading residual⟩
  | marked label point ih =>
      obtain ⟨remaining,residual⟩ := ih
      exact ⟨_,.marked label residual⟩

theorem Residual.point (residual : Residual children shape w h site u middle remaining) :
    Point native shape w h site u middle := by
  induction residual with
  | entry shape => exact .entry shape
  | returned shape performed => exact .returned shape performed
  | acquire point => exact .acquire point
  | leaf source remaining => exact .leaf source remaining.point
  | interior token point => exact .interior token point
  | left tail remaining ih => exact .left tail ih
  | right head tail leading remaining ih => exact .right head tail leading ih
  | marked label remaining ih => exact .marked label ih

theorem Residual.run {α : Type} {action : PrefixM Event α} {shape : Shape action}
    {remaining : PrefixM Event α}
    (residual : Residual children shape w h site u middle remaining) :
    runPrefix action w h = runPrefix remaining u middle := by
  induction residual with
  | entry shape => rfl
  | returned shape performed => exact performed.trans (runPrefix_pure _ _ _).symm
  | acquire point => exact SavedCall.acquireRemainder_run _ point
  | leaf source remaining => exact remaining.run
  | interior token point => exact (children.contract token).continuation _ _ _ _ point
  | left tail remaining ih => exact Scheduler.bind_run_equal _ ih
  | right head tail leading remaining ih => rw [runPrefix_bind,leading]; exact ih
  | marked label remaining ih => exact ih

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
