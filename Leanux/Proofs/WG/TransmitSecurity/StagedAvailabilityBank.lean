import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityBirth

/-! One ordered assignment bank exposes the consequence of live staged
credits: a birth ticket cannot occur in two allocated packet positions.
The native-source initialization of BankValid remains a separate obligation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects.CausalJournal Leanux.Proofs.WG.TransmitSecurity.Staged.Origins

abbrev Bank := Nat → List Ticket

variable {history : List Event} {bank : Bank} {index ordinal : Nat}
  {firstIndex secondIndex leftIndex rightIndex : Nat} {ticket : Ticket}
  {packets firstPackets secondPackets : List DataPacket}
  {r firstRun secondRun : WGRunWitness (List SkbId)}

def BankValid (history : List Event) (bank : Bank) : Prop :=
  ∀ index packets (r : WGRunWitness (List SkbId)),
    history[index]? = some (.old (.allocated packets r)) →
      (bank index).Nodup ∧ ∃ generation pid stamp,
        Origins.Aligned (Live (history.take index) generation pid stamp)
          (bank index) (packets.map DataPacket.plaintext) ∧
        ∀ packet ∈ packets, packet.peer = pid

theorem Aligned.get_right {related : α → β → Prop}
    (aligned : Origins.Aligned related xs ys) (found : xs[index]? = some value) :
    ∃ other, ys[index]? = some other ∧ related value other := by
  induction aligned generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at found
              subst value
              exact ⟨_,rfl,head⟩
    | succ index => exact ih found

theorem Born.take_to_full (born : Born (history.take index) generation pid stamp ticket packet) :
    Born history generation pid stamp ticket packet := by
  simpa only [List.take_append_drop] using born.append (history.drop index)

theorem bank_credit (valid : BankValid history bank)
    (found : history[index]? = some (.old (.allocated packets r)))
    (used : (bank index)[ordinal]? = some ticket) :
    ∃ generation pid stamp packet,
      packets[ordinal]? = some packet ∧ packet.peer = pid ∧
      Live (history.take index) generation pid stamp ticket packet.plaintext := by
  obtain ⟨_,generation,pid,stamp,aligned,owner⟩ := valid index packets r found
  obtain ⟨plain,atPlain,live⟩ := Aligned.get_right aligned used
  rw [List.getElem?_map] at atPlain
  cases atPacket : packets[ordinal]? with
  | none => simp [atPacket] at atPlain
  | some packet =>
    simp only [atPacket,Option.map_some,Option.some.injEq] at atPlain
    exact ⟨generation,pid,stamp,packet,rfl,owner packet (List.mem_of_getElem? atPacket),
      atPlain.symm ▸ live⟩

theorem bank_credit_before (valid : BankValid history bank)
    (found : history[index]? = some (.old (.allocated packets r)))
    (used : (bank index)[ordinal]? = some ticket) : ticket.position < index := by
  obtain ⟨_,_,_,_,_,_,born,_⟩ := bank_credit valid found used
  have bound := born.position_lt
  simp only [List.length_take] at bound
  omega

theorem bank_credit_between (valid : BankValid history bank)
    (first : history[firstIndex]? = some (.old (.allocated firstPackets firstRun)))
    (second : history[secondIndex]? = some (.old (.allocated secondPackets secondRun)))
    (later : firstIndex < secondIndex)
    (left : (bank firstIndex)[leftIndex]? = some ticket)
    (right : (bank secondIndex)[rightIndex]? = some ticket) : firstIndex < ticket.position := by
  obtain ⟨g,pid,stamp,packet,atPacket,owner,born,_⟩ := bank_credit valid first left
  obtain ⟨g',pid',stamp',packet',_,_,born',available⟩ := bank_credit valid second right
  have samePeer : pid = pid' := ((Born.take_to_full born).unique (Born.take_to_full born')).2.1
  apply available firstIndex (.old (.allocated firstPackets firstRun))
  · rw [List.getElem?_take_of_lt later]
    exact first
  · exact ⟨packet,List.mem_of_getElem? atPacket,owner.trans samePeer⟩

/-- An available staged birth can fund only one allocation position, even
when byte-identical payloads occur in different batches or different peers. -/
theorem bank_ticket_injective (valid : BankValid history bank)
    (first : history[firstIndex]? = some (.old (.allocated firstPackets firstRun)))
    (second : history[secondIndex]? = some (.old (.allocated secondPackets secondRun)))
    (left : (bank firstIndex)[leftIndex]? = some ticket)
    (right : (bank secondIndex)[rightIndex]? = some ticket) :
    firstIndex = secondIndex ∧ leftIndex = rightIndex := by
  have batch : firstIndex = secondIndex := by
    have lb := bank_credit_before valid first left
    have rb := bank_credit_before valid second right
    by_cases order : firstIndex < secondIndex
    · have := bank_credit_between valid first second order left right
      omega
    · by_cases reverse : secondIndex < firstIndex
      · have := bank_credit_between valid second first reverse right left
        omega
      · omega
  subst secondIndex
  refine ⟨rfl,?_⟩
  apply (valid _ _ _ first).1.eq_of_getElem?_eq
  · exact (List.getElem?_eq_some_iff.mp left).choose
  · exact left.trans right.symm

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
