import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointContract

/-! Source-constructed remainders retain the actual surrounding binds. An
arbitrary equal-run action cannot construct this relation. The sole open leaf
remainders are those of the five explicit committed-child source contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

inductive Residual {native inside : ChildPoints} {Good : History → World → Prop}
    (children : ChildContracts native inside Good) :
    {α : Type} → {action : PrefixM Event α} → Shape action →
    World → History → Site → World → History → PrefixM Event α → Prop where
  | entry (shape : Shape action) : Residual children shape w h .entry w h action
  | returned (shape : Shape action)
      (performed : runPrefix action w h = (.ok (value,u),middle)) :
      Residual children shape w h .returned u middle (pure value)
  | interior (token : Child) (point : native token w h u middle) :
      Residual children (.child token) w h .interior u middle
        ((children.at token).remainder w h u middle point)
  | metadata {α : Type} {body : WG.M α} {source : PeerMetadata.Shape body} {w : World}
      (point : PeerMetadata.Point source w.wg w.ambient v b) :
      Residual children (.native (.metadata body source)) w h .metadata {w with wg:=v,ambient:=b} h (metadataRemainder h point)
  | rx {α : Type} {body : WG.M α} {source : RxAccess.Shape body} {w : World}
      (point : RxAccess.Point source w.wg w.ambient v b) :
      Residual children (.native (.rx body source)) w h .rx {w with wg:=v,ambient:=b} h (rxRemainder h point)
  | free {w : World} (point : SkbAccess.Point (SkbStore.freeRx skb) w.wg w.ambient v b) :
      Residual children (.native (.free skb)) w h .free {w with wg:=v,ambient:=b} h (freeRemainder h point)
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
  | interior token point => exact ⟨_,.interior token point⟩
  | metadata point => exact ⟨_,.metadata point⟩
  | rx point => exact ⟨_,.rx point⟩
  | free point => exact ⟨_,.free point⟩
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
  | interior token point => exact .interior token point
  | metadata point => exact .metadata point
  | rx point => exact .rx point
  | free point => exact .free point
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
  | interior token point => exact (children.at token).continuation _ _ _ _ point
  | metadata point => exact metadataRemainder_run _ point
  | rx point => exact rxRemainder_run _ point
  | free point => exact freeRemainder_run _ point
  | left tail remaining ih => exact Scheduler.bind_run_equal _ ih
  | right head tail leading remaining ih => rw [runPrefix_bind,leading]; exact ih
  | marked label remaining ih => exact ih

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
