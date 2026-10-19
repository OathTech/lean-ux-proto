import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionHistory

/-! Occurrence-preserving extraction from the sent-list suffix. The global
append ordinal identifies an event position and an offset inside that event;
equal datagram values do not collapse two transmissions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG

def Occurrence (history : List Event) (ordinal : Nat) (datagram : SentDatagram) : Prop :=
  ∃ before event after inside,
    history = before ++ event :: after ∧
    (added event)[inside]? = some datagram ∧
    ordinal = (emitted before).length + inside

theorem locate (history : List Event) (ordinal : Nat) (datagram : SentDatagram)
    (atPosition : (emitted history)[ordinal]? = some datagram) :
    Occurrence history ordinal datagram := by
  induction history generalizing ordinal with
  | nil => simp only [emitted,List.flatMap_nil,List.getElem?_nil] at atPosition; cases atPosition
  | cons event rest ih =>
    change (added event ++ emitted rest)[ordinal]? = some datagram at atPosition
    by_cases earlier : ordinal < (added event).length
    · rw [List.getElem?_append_left earlier] at atPosition
      exact ⟨[],event,rest,ordinal,rfl,atPosition,(Nat.zero_add ordinal).symm⟩
    · rw [List.getElem?_append_right (by omega)] at atPosition
      obtain ⟨before,receipt,after,inside,historyEq,insideEq,ordinalEq⟩ :=
        ih (ordinal - (added event).length) atPosition
      refine ⟨event :: before,receipt,after,inside,?_,insideEq,?_⟩
      · rw [historyEq]; rfl
      · change ordinal = (added event ++ emitted before).length + inside
        rw [List.length_append]
        omega

/-- Every position of the native sent list has its own journal append
ordinal, counted from the exact flattened receipt suffix. -/
theorem Inv.locate (hi : Inv history w) (index : Nat) (datagram : SentDatagram)
    (atPosition : w.sent[index]? = some datagram) :
    Occurrence history ((emitted history).length - w.sent.length + index) datagram := by
  obtain ⟨earlier,historyEq⟩ := hi
  have lengths := congrArg List.length historyEq
  simp only [List.length_append] at lengths
  have offset : (emitted history).length - w.sent.length = earlier.length := by omega
  apply Emissions.locate
  rw [offset,historyEq,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  exact atPosition

theorem ordinal_injective (history : List Event) (w : WGWorld) (first second : Nat)
    (same : (emitted history).length - w.sent.length + first =
      (emitted history).length - w.sent.length + second) : first = second :=
  Nat.add_left_cancel same

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
