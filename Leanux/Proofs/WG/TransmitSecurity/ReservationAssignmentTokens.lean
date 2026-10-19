import Leanux.Proofs.WG.TransmitSecurity.ReservationAssignmentCredits

/-! Positional exclusivity joins the initialized native nonce projection.
Tokens name allocation stamps, not numeric key slots. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {h : List Journal.Event} {u v : Use}
  {index packetIndex firstIndex secondIndex leftIndex rightIndex : Nat}

theorem filtered_position_injective {E A : Type} {history : List E} {project : E → Option A} {first second : E} {token : A}
    (nodup : (history.filterMap project).Nodup)
    (left : history[firstIndex]? = some first) (right : history[secondIndex]? = some second)
    (atLeft : project first = some token) (atRight : project second = some token) :
    firstIndex = secondIndex := by
  have pairwise := List.pairwise_filterMap.mp nodup
  obtain ⟨lb,lv⟩ := List.getElem?_eq_some_iff.mp left
  obtain ⟨rb,rv⟩ := List.getElem?_eq_some_iff.mp right
  by_cases order : firstIndex < secondIndex
  · have unequal := pairwise.rel_getElem_of_lt lb rb order
    rw [lv,rv] at unequal
    exact False.elim (unequal token atLeft token atRight rfl)
  · by_cases reverse : secondIndex < firstIndex
    · have unequal := pairwise.rel_getElem_of_lt rb lb reverse
      rw [rv,lv] at unequal
      exact False.elim (unequal token atRight token atLeft rfl)
    · omega

theorem credit_valid (safe : Safe h) (found : h[index]? = some (.allocated packets r))
    (used : (credits h index)[packetIndex]? = some u) : u.Valid h := by
  have valid := ((credits_spec safe found).2.2 u (List.mem_of_getElem? used)).1
  have bound := credit_before safe found used
  refine ⟨?_,valid.2⟩
  have atPosition := valid.1
  rw [List.getElem?_take_of_lt bound] at atPosition
  exact atPosition

theorem credit_token_injective (safe : Safe h) (nonces : (h.filterMap Journal.nonce?).Nodup)
    (first : h[firstIndex]? = some (.allocated firstPackets firstRun))
    (second : h[secondIndex]? = some (.allocated secondPackets secondRun))
    (left : (credits h firstIndex)[leftIndex]? = some u)
    (right : (credits h secondIndex)[rightIndex]? = some v)
    (same : u.token = v.token) : firstIndex = secondIndex ∧ leftIndex = rightIndex := by
  apply credit_position_injective safe first second left right
  exact filtered_position_injective nonces (credit_valid safe first left).1
    (credit_valid safe second right).1 (by simp only [Journal.nonce?,same]) rfl

theorem credit_nonce (valid : u.Valid h) : u.token.nonce = u.packet.nonce := by
  obtain ⟨_,_,_,_,_,value⟩ := valid.2.1.2
  exact value.trans valid.2.2

end Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
