import PairInsertInput
import PairExcept

namespace Binary.Pair.Insert
open Leanux Leanux.WG

/-- A successful runtime input assertion consumes the same bytes and leaves
the same cursor as the actual mirror's hidden-input operation. -/
theorem draw_hidden {records : List HiddenRecord} {value : Nat} {rest : List HiddenRecord}
    (accepted : draw records=.ok (value,rest)) (w : World)
    (supplied : w.hidden=some records) :
    (hiddenU64 .indexDraw).run w=.ok (value,{w with hidden := some rest}) := by
  unfold draw at accepted
  cases skipped : records.dropWhile (fun r => HiddenSite.passive r.site) with
  | nil => simp [skipped] at accepted
  | cons r rs =>
    rw [skipped] at accepted
    obtain ⟨site,accepted⟩ := check_ok _ _ _ _ accepted
    obtain ⟨shape,accepted⟩ := check_ok _ _ _ _ accepted
    have siteEq : r.site=4 := by simpa [HiddenSite.info] using site
    have both : r.bytes.length=8 ∧ (r.bytes.drop 4).all (· == 0)=true := by simpa using shape
    have length := both.1
    have padding : ¬∃ b, b ∈ r.bytes.drop 4 ∧ b≠0 := by
      have all := List.all_eq_true.mp both.2
      rintro ⟨b,member,different⟩
      exact different (by simpa using all b member)
    have answer := Except.ok.inj accepted
    cases answer
    simp [hiddenU64,hidden,skipAmbient,noteNetRxStart,HiddenSite.info,Worker.sectionId,Worker.index,
      StateT.run_bind,supplied,skipped,siteEq,length,padding]
    rfl

#print axioms draw_hidden
end Binary.Pair.Insert
