import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReadAccessSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSkbAccessSource

/-! Product-level read programs retain their actual WG getter points and
Ambient effects. No constructor commits a simulated world's WG state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductRead
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

inductive Shape : {α : Type} → Leanux.M α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | read : Shape (get : Leanux.M World)
  | ambient (body : AmbientM α) : Shape (Leanux.liftAmbient body)
  | wg (source : ReadAccess.Shape body) : Shape (liftWG body)
  | packet (skb : SkbId) : Shape (liftWG (getTxSkb skb))
  | bind {body : Leanux.M α} {next : α → Leanux.M β}
      (head : Shape body) (tail : ∀ value, Shape (next value)) : Shape (body >>= next)

inductive Point : {α : Type} → {action : Leanux.M α} → Shape action → World → World → Prop where
  | entry (source : Shape action) : Point source w w
  | returned (source : Shape action) (performed : action.run w=.ok (value,v)) : Point source w v
  | wg {w : World} (point : ReadAccess.Point source w.wg w.ambient v b) :
      Point (.wg source) w {w with wg:=v,ambient:=b}
  | packet {w : World} (point : SkbAccess.Point (SkbStore.getTx skb) w.wg w.ambient v b) :
      Point (.packet skb) w {w with wg:=v,ambient:=b}
  | left {body : Leanux.M α} {next : α → Leanux.M β} {head : Shape body}
      (tail : ∀ value, Shape (next value)) (point : Point head w v) : Point (.bind head tail) w v
  | right {body : Leanux.M α} {next : α → Leanux.M β} (head : Shape body)
      (tail : ∀ value, Shape (next value)) (leading : body.run w=.ok (value,u))
      (point : Point (tail value) u v) : Point (.bind head tail) w v

theorem Point.remaining {α : Type} {action : Leanux.M α} {source : Shape action}
    (point : Point source w v) : ∃ rest : Leanux.M α, action.run w=rest.run v := by
  induction point with
  | entry source => exact ⟨_,rfl⟩
  | returned source performed => exact ⟨pure _,performed⟩
  | wg point =>
      obtain ⟨rest,same⟩ := point.remaining
      exact ⟨liftWG rest,by simp only [liftWG_run,same]⟩
  | packet point =>
      obtain ⟨rest,same⟩ := point.remaining
      exact ⟨liftWG rest,by simp only [getTxSkb,liftWG_run,same]⟩
  | @left α β w v body next head tail point ih =>
      obtain ⟨rest,same⟩ := ih
      exact ⟨rest >>= next,by simp only [StateT.run_bind,same]⟩
  | right head tail leading point ih =>
      obtain ⟨rest,same⟩ := ih
      exact ⟨rest,by simp only [StateT.run_bind,leading];exact same⟩

theorem Point.observed_remaining {α E : Type} {action : Leanux.M α} {source : Shape action}
    (point : Point source w v) (h : List E) :
    ∃ rest : PrefixM E α,runPrefix (liftPrefix action) w h=runPrefix rest v h := by
  obtain ⟨rest,same⟩ := point.remaining
  exact ⟨liftPrefix rest,by simp only [runPrefix_lift,same]⟩

noncomputable def remainder {α E : Type} {action : Leanux.M α} {source : Shape action}
    (h : List E) (point : Point source w v) : PrefixM E α :=
  Classical.choose (point.observed_remaining h)

theorem remainder_run {α E : Type} {action : Leanux.M α} {source : Shape action}
    (h : List E) (point : Point source w v) :
    runPrefix (liftPrefix action) w h=runPrefix (remainder h point) v h :=
  Classical.choose_spec (point.observed_remaining h)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductRead
