import Leanux.Proofs.WG.RetirementSecurity.Frames

/-! Local security consequences of the exact native release effect. These
statements do not replace the still separate initialized key-holder ledger. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG

theorem PutEffect.payment {id : KeypairId} (effect : PutEffect id now k w v) :
    references v id + 1 = k.refcount := by
  rw [references,effect.selected,keyAfterPut]
  split <;> simp_all
  have positive := effect.positive
  omega

theorem PutEffect.nonfinal {id : KeypairId} (effect : PutEffect id now k w v)
    (more : 1 < k.refcount) :
    keyAt v id = some {k with refcount := k.refcount - 1} := by
  rw [effect.selected,keyAfterPut,ite_eq_right (by omega)]

theorem PutEffect.final {id : KeypairId} (effect : PutEffect id now k w v)
    (last : k.refcount = 1) : keyAt v id = none := by
  rw [effect.selected,keyAfterPut,ite_eq_left last]

theorem PutEffect.unpublished {id : KeypairId} (effect : PutEffect id now k w v)
    (remove : now = true ∨ k.refcount = 1) : Unpublished id v := by
  have yes : (now || k.refcount == 1) = true := by
    rcases remove with h | h <;> simp [h]
  intro entries atIndex entry member
  rw [effect.index] at atIndex
  cases before : indexAt w with
  | none => simp [before] at atIndex
  | some old =>
    simp only [before,Option.map_some,yes,↓reduceIte,Option.some.injEq] at atIndex
    rw [←atIndex] at member
    have keep := (List.mem_filter.mp member).2
    intro same
    simp [same] at keep
    change (id == id) = false at keep
    simp at keep

end Leanux.Proofs.WG.RetirementSecurity
