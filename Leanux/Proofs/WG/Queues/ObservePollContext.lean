import Leanux.Proofs.WG.Queues.ObservePollSource

/-! A local poll retains the caller's global prefix as a proof parameter.
Its fresh lifetime seed is not mistaken for an empty global routing history.
The reconstruction below is exactly the history emitted by seededWith. -/
namespace Leanux.Proofs.WG.Queues.RxHistory.ObserveSource
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- Interpret the local journal at its actual position after the caller's
prefix. Only records after the fresh seed become new global records. -/
def atPrefix {E L : Type} (seed : List E → List L) (promote : L → E)
    (prior : List E) (localHistory : List L) : List E :=
  prior ++ (localHistory.drop (seed prior).length).map promote

theorem atPrefix_seed {E L : Type} (seed : List E → List L) (promote : L → E)
    (prior : List E) : atPrefix seed promote prior (seed prior) = prior := by
  simp only [atPrefix,List.drop_length,List.map_nil,List.append_nil]

theorem atPrefix_suffix {E L : Type} (seed : List E → List L) (promote : L → E)
    (prior : List E) (suffix : List L) :
    atPrefix seed promote prior (seed prior ++ suffix) = prior ++ suffix.map promote := by
  simp only [atPrefix,List.drop_append_length]

/-- The local invariant is indexed by the actual incoming global prefix.
Both normal-state preservation and stopped-prefix safety are transferred;
the callback premise remains an arbitrary product-observer contract. -/
theorem seeded_preserves {E L α : Type} (seed : List E → List L) (promote : L → E)
    (poll : PrefixM L α) (I : List E → World → Prop) (S : List E → Prop)
    (callback : ∀ prior, PrefixPreserves
      (fun hist w => I (atPrefix seed promote prior hist) w)
      (fun hist => S (atPrefix seed promote prior hist)) poll) :
    PrefixPreserves I S (seededWith seed promote poll) := by
  intro w h hi
  have start : I (atPrefix seed promote h (seed h)) w := by
    simpa only [atPrefix_seed] using hi
  obtain ⟨_,_,safe,normal⟩ := callback h w (seed h) start
  refine ⟨_,rfl,safe,?_⟩
  exact normal

/-- When local promotion cannot construct a routing event (or another chosen
kind), that entire global projection remains the caller's original history,
including on a Stop. No event-uniqueness condition is involved. -/
theorem seeded_historyFrame {E L F α : Type} (seed : List E → List L)
    (promote : L → E) (poll : PrefixM L α) (ρ : E → Option F)
    (quiet : ∀ e, ρ (promote e) = none) :
    HistoryFrame ρ (seededWith seed promote poll) := by
  intro w h
  change (h ++ ((runPrefix poll w (seed h)).2.drop (seed h).length).map promote).filterMap ρ = h.filterMap ρ
  rw [List.filterMap_append,filterMap_disjoint promote ρ quiet,List.append_nil]

end Leanux.Proofs.WG.Queues.RxHistory.ObserveSource
