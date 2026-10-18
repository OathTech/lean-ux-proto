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

/-- Conversely, every accepted supplied draw has the runtime decoder's
shape and exact remaining cursor. Placeholder runs are not supplied inputs. -/
theorem hidden_draw {records : List HiddenRecord} {value : Nat} {w final : World}
    (supplied : w.hidden=some records)
    (accepted : (hiddenU64 .indexDraw).run w=.ok (value,final)) :
    ∃ rest, draw records=.ok (value,rest) ∧ final={w with hidden := some rest} := by
  cases skipped : records.dropWhile (fun r => HiddenSite.passive r.site) with
  | nil =>
    simp [hiddenU64,hidden,skipAmbient,noteNetRxStart,HiddenSite.info,Worker.sectionId,Worker.index,
      StateT.run_bind,supplied,skipped] at accepted
    cases accepted
  | cons r rs =>
    by_cases site : r.site=4
    · by_cases length : r.bytes.length=8
      · by_cases padding : (r.bytes.drop 4).all (· == 0)=true
        · have decoded : draw records=.ok ((r.bytes.take 4).foldr (fun b acc => acc*256+b.toNat) 0,rs) := by
            simp [draw,skipped,HiddenSite.info,site,length,padding]
            rfl
          have actual := draw_hidden decoded w supplied
          rw [actual] at accepted
          have equal := Except.ok.inj accepted
          cases equal
          exact ⟨rs,decoded,rfl⟩
        · have bad : (r.bytes.drop 4).any (· != 0)=true := by
            change ((r.bytes.drop 4).any (fun b => !(b == 0)))=true
            rw [←List.not_all_eq_any_not]
            cases yes : (r.bytes.drop 4).all (· == 0) <;> simp_all
          have badExists : ∃ b ∈ r.bytes.drop 4, b≠0 := by simpa only [List.any_eq_true,bne_iff_ne] using bad
          simp [hiddenU64,hidden,skipAmbient,noteNetRxStart,HiddenSite.info,Worker.sectionId,Worker.index,
            StateT.run_bind,supplied,skipped,site,length,badExists] at accepted
          cases accepted
      · simp [hiddenU64,hidden,skipAmbient,noteNetRxStart,HiddenSite.info,Worker.sectionId,Worker.index,
          StateT.run_bind,supplied,skipped,site,length] at accepted
        cases accepted
    · simp [hiddenU64,hidden,skipAmbient,noteNetRxStart,HiddenSite.info,Worker.sectionId,Worker.index,
        StateT.run_bind,supplied,skipped,site] at accepted
      cases accepted

#print axioms hidden_draw
end Binary.Pair.Insert
