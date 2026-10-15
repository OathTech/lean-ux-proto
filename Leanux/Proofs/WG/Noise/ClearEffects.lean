import Leanux.Proofs.WG.Noise.ClearFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Remaining occurrence counts decrease on the released key; a last
release is possible only when that key has no remaining occurrence. -/
theorem clearPut_ready {key : Option KeypairId} {d final : Device}
    (put : ClearPut key d final) (rest : List (Option KeypairId))
    (ready : ClearReady d (key :: rest)) : ClearReady final rest := by
  cases put with
  | null =>
    intro id occurs
    simpa using ready id (by simpa using occurs)
  | present d id k resident live word =>
    intro other occurs
    by_cases same : other = id
    · subst other
      obtain ⟨old, found, oldWord, bound⟩ := ready id (by simp)
      rw [resident] at found
      cases found
      have bound' : rest.count (some id) + 1 ≤ k.refcount := by simpa using bound
      have last : k.refcount ≠ 1 := by omega
      refine ⟨{ k with refcount := k.refcount - 1 }, ?_, word, ?_⟩
      · simpa [last] using Index.released_keypair d id k true
      · change rest.count (some id) ≤ k.refcount - 1
        omega
    · obtain ⟨old, found, oldWord, bound⟩ := ready other (by simpa [same, Ne.symm same] using occurs)
      refine ⟨old, ?_, oldWord, ?_⟩
      · rw [Index.released_other_keypair d id other k true (Ne.symm same)]
        exact found
      · simpa [same, Ne.symm same] using bound

theorem clearPut_exists (key : Option KeypairId) (d : Device)
    (rest : List (Option KeypairId)) (ready : ClearReady d (key :: rest)) :
    ∃ final, ClearPut key d final ∧ ClearReady final rest := by
  cases key with
  | none => exact ⟨d, .null d, clearPut_ready (.null d) rest ready⟩
  | some id =>
    obtain ⟨k, resident, word, bound⟩ := ready id (by simp)
    have live : 0 < k.refcount := by
      simp only [List.count_cons_self] at bound
      omega
    have put := ClearPut.present d id k resident live word
    exact ⟨_, put, clearPut_ready put rest ready⟩

end Leanux.Proofs.WG.Noise
