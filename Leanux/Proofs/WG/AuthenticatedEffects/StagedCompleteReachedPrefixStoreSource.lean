import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedControlStoreSource

/-! Logged source syntax for fixed native runner helpers. Native leaves
use actual product-store source trees; binds retain their original operands. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PrefixStore
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
abbrev History := List Event

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (source : ProductStore.Shape body) : Shape (liftPrefix body)
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value,Shape (next value)) : Shape (body >>= next)

inductive Point : {α : Type} → {action : PrefixM Event α} → Shape action →
    World → History → World → History → Prop where
  | entry (source : Shape action) : Point source w h w h
  | returned (source : Shape action)
      (performed : runPrefix action w h=(.ok (value,v),last)) : Point source w h v last
  | native (point : ProductStore.Point source w v) : Point (.native source) w h v h
  | left {body : PrefixM Event α} {next : α → PrefixM Event β} {head : Shape body}
      (tail : ∀ value,Shape (next value)) (point : Point head w h v last) : Point (.bind head tail) w h v last
  | right {body : PrefixM Event α} {next : α → PrefixM Event β} (head : Shape body)
      (tail : ∀ value,Shape (next value)) (leading : runPrefix body w h=(.ok (value,u),middle))
      (point : Point (tail value) u middle v last) : Point (.bind head tail) w h v last

theorem Point.remaining {α : Type} {action : PrefixM Event α} {source : Shape action}
    (point : Point source w h v last) : ∃ rest : PrefixM Event α,runPrefix action w h=runPrefix rest v last := by
  induction point with
  | entry source => exact ⟨_,rfl⟩
  | returned source performed => exact ⟨pure _,performed⟩
  | native point => exact point.observed_remaining _
  | @left α β w h v last body next head tail point ih =>
      obtain ⟨rest,same⟩ := ih
      exact ⟨rest >>= next,by simp only [runPrefix_bind,same]⟩
  | right head tail leading point ih =>
      obtain ⟨rest,same⟩ := ih
      exact ⟨rest,by simp only [runPrefix_bind,leading];exact same⟩

noncomputable def remainder {α : Type} {action : PrefixM Event α} {source : Shape action}
    (point : Point source w h v last) : PrefixM Event α := Classical.choose point.remaining

theorem remainder_run {α : Type} {action : PrefixM Event α} {source : Shape action}
    (point : Point source w h v last) :
    runPrefix action w h=runPrefix (remainder point) v last := Classical.choose_spec point.remaining

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PrefixStore
