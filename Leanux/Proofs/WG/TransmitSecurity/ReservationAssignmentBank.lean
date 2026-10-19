import Leanux.Proofs.WG.TransmitSecurity.ReservationAssignmentTokens

/-! Reservation exclusivity applies to any one coherent assignment bank.
A stronger material certificate may select the bank without weakening the
positional, allocation-interval or nonce uniqueness requirements. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
open Leanux Leanux.WG Leanux.Proofs.Logged

abbrev Bank := Nat → List Use

def BankValid (h : List Journal.Event) (bank : Bank) : Prop :=
  ∀ (index : Nat) (packets : List DataPacket) (r : WGRunWitness (List SkbId)),
    h[index]? = some (.allocated packets r) →
      (bank index).map Use.packet = packets ∧
      ((bank index).map Use.position).Pairwise (· < ·) ∧
      ∀ u ∈ bank index, u.Valid (h.take index) ∧ Available (h.take index) u.position

theorem credits_bank_valid (safe : Safe h) : BankValid h (credits h) :=
  fun _ _ _ found => credits_spec safe found

namespace Bank
variable {h : List Journal.Event} {bank : Bank} {u v : Use}
  {index packetIndex firstIndex secondIndex leftIndex rightIndex : Nat}

theorem credit_before (safe : BankValid h bank) (found : h[index]? = some (.allocated packets r))
    (used : (bank index)[packetIndex]? = some u) : u.position < index := by
  have bound := ((safe _ _ _ found).2.2 u (List.mem_of_getElem? used)).1.bound
  simp only [List.length_take] at bound
  omega

theorem credit_between (safe : BankValid h bank)
    (first : h[firstIndex]? = some (.allocated firstPackets firstRun))
    (second : h[secondIndex]? = some (.allocated secondPackets secondRun))
    (later : firstIndex < secondIndex)
    (used : (bank secondIndex)[packetIndex]? = some u) : firstIndex < u.position := by
  have available := ((safe _ _ _ second).2.2 u (List.mem_of_getElem? used)).2
  apply available firstIndex firstPackets firstRun
  rw [List.getElem?_take_of_lt later]
  exact first

theorem credit_position_injective (safe : BankValid h bank)
    (first : h[firstIndex]? = some (.allocated firstPackets firstRun))
    (second : h[secondIndex]? = some (.allocated secondPackets secondRun))
    (left : (bank firstIndex)[leftIndex]? = some u)
    (right : (bank secondIndex)[rightIndex]? = some v)
    (same : u.position = v.position) : firstIndex = secondIndex ∧ leftIndex = rightIndex := by
  have batch : firstIndex = secondIndex := by
    have lb := credit_before safe first left
    have rb := credit_before safe second right
    by_cases order : firstIndex < secondIndex
    · have := credit_between safe first second order right
      omega
    · by_cases reverse : secondIndex < firstIndex
      · have := credit_between safe second first reverse left
        omega
      · omega
  subst secondIndex
  refine ⟨rfl,?_⟩
  have nodup : ((bank firstIndex).map Use.position).Nodup :=
    (safe _ _ _ first).2.1.imp (fun less => Nat.ne_of_lt less)
  apply nodup.eq_of_getElem?_eq
  · simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp left).choose
  · simp only [List.getElem?_map,left,right,Option.map_some,same]

theorem credit_valid (safe : BankValid h bank) (found : h[index]? = some (.allocated packets r))
    (used : (bank index)[packetIndex]? = some u) : u.Valid h := by
  have valid := ((safe _ _ _ found).2.2 u (List.mem_of_getElem? used)).1
  have bound := credit_before safe found used
  refine ⟨?_,valid.2.1,valid.2.2.1,?_⟩
  · have atPosition := valid.1
    rw [List.getElem?_take_of_lt bound] at atPosition
    exact atPosition
  · have atReceipt := valid.2.2.2
    have receiptBound := (List.getElem?_eq_some_iff.mp atReceipt).choose
    have beforeAllocation : u.position + 1 < index := by
      simp only [List.length_take] at receiptBound
      omega
    rw [List.getElem?_take_of_lt beforeAllocation] at atReceipt
    exact atReceipt

theorem credit_token_injective (safe : BankValid h bank) (nonces : (h.filterMap Journal.nonce?).Nodup)
    (first : h[firstIndex]? = some (.allocated firstPackets firstRun))
    (second : h[secondIndex]? = some (.allocated secondPackets secondRun))
    (left : (bank firstIndex)[leftIndex]? = some u)
    (right : (bank secondIndex)[rightIndex]? = some v)
    (same : u.token = v.token) : firstIndex = secondIndex ∧ leftIndex = rightIndex := by
  apply credit_position_injective safe first second left right
  exact filtered_position_injective nonces (credit_valid safe first left).1
    (credit_valid safe second right).1 (by simp only [Journal.nonce?,same]) rfl

end Bank
end Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
