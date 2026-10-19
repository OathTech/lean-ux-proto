import Leanux.Proofs.WG.TransmitSecurity.ReservationAssignmentInitialized

/-! A single mathematical assignment chosen for each actual allocation event.
Its reservation positions are injective across both packet and batch indices. -/
namespace Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {h : List Journal.Event} {u v : Use}
  {index packetIndex firstIndex secondIndex leftIndex rightIndex : Nat}

theorem Safe.at (safe : Safe h) (found : h[index]? = some (.allocated packets r)) :
    r.Valid (packets.mapM newTxSkb) ∧ Packets (h.take index) packets := by
  obtain ⟨bound,value⟩ := List.getElem?_eq_some_iff.mp found
  apply safe (h.take index) (.allocated packets r) (h.drop (index + 1))
  rw [←value,List.getElem_cons_drop bound,List.take_append_drop]

noncomputable def credits (h : List Journal.Event) (index : Nat) : List Use := by
  classical
  exact match h[index]? with
  | some (.allocated packets _) =>
      if claim : Packets (h.take index) packets then claim.choose else []
  | _ => []

theorem credits_spec (safe : Safe h) (found : h[index]? = some (.allocated packets r)) :
    (credits h index).map Use.packet = packets ∧
    ((credits h index).map Use.position).Pairwise (· < ·) ∧
    ∀ u ∈ credits h index, u.Valid (h.take index) ∧ Available (h.take index) u.position := by
  have checked := (safe.at found).2
  simpa only [credits,found,checked,↓reduceDIte] using checked.choose_spec

theorem credit_before (safe : Safe h) (found : h[index]? = some (.allocated packets r))
    (used : (credits h index)[packetIndex]? = some u) : u.position < index := by
  have bound := ((credits_spec safe found).2.2 u (List.mem_of_getElem? used)).1.bound
  simp only [List.length_take] at bound
  omega

theorem credit_between (safe : Safe h)
    (first : h[firstIndex]? = some (.allocated firstPackets firstRun))
    (second : h[secondIndex]? = some (.allocated secondPackets secondRun))
    (later : firstIndex < secondIndex)
    (used : (credits h secondIndex)[packetIndex]? = some u) : firstIndex < u.position := by
  have available := ((credits_spec safe second).2.2 u (List.mem_of_getElem? used)).2
  apply available firstIndex firstPackets firstRun
  rw [List.getElem?_take_of_lt later]
  exact first

theorem credit_position_injective (safe : Safe h)
    (first : h[firstIndex]? = some (.allocated firstPackets firstRun))
    (second : h[secondIndex]? = some (.allocated secondPackets secondRun))
    (left : (credits h firstIndex)[leftIndex]? = some u)
    (right : (credits h secondIndex)[rightIndex]? = some v)
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
  have nodup : ((credits h firstIndex).map Use.position).Nodup :=
    (credits_spec safe first).2.1.imp (fun less => Nat.ne_of_lt less)
  apply nodup.eq_of_getElem?_eq
  · simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp left).choose
  · simp only [List.getElem?_map,left,right,Option.map_some,same]

end Leanux.Proofs.WG.TransmitSecurity.ReservationAssignments
