import Leanux.Proofs.WG.Queues.RxClearQueue

/-! An ordered queue ledger records source-owned peer references. Selection
removes the first matching occurrence, retaining every duplicate after it.
These lemmas rearrange existing funded reservations; they create none. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.WorkReservations
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

def Selected (owners : Reservations) (pid : PeerId) (o : Owner)
    (restOwners : Reservations) : Prop :=
  ∃ before after, owners = before ++ o :: after ∧
    pid ∉ before.map Owner.slot ∧ o.slot = pid ∧ restOwners = before ++ after

theorem select_exists (owners : Reservations) (pid : PeerId)
    (present : pid ∈ owners.map Owner.slot) : ∃ o restOwners, Selected owners pid o restOwners := by
  induction owners with
  | nil => simp at present
  | cons head tail ih =>
    by_cases same : head.slot = pid
    · exact ⟨head,tail,[],tail,rfl,by simp,same,rfl⟩
    · have inside : pid ∈ tail.map Owner.slot := by simpa [same,Ne.symm same] using present
      obtain ⟨o,restOwners,before,after,split,absent,slot,rest⟩ := ih inside
      refine ⟨o,head :: restOwners,head :: before,after,?_,?_,slot,?_⟩
      · simp [split]
      · simp [Ne.symm same,absent]
      · simp [rest]

theorem Selected.perm (selected : Selected owners pid o restOwners) :
    owners.Perm (o :: restOwners) := by
  obtain ⟨before,after,rfl,_,_,rfl⟩ := selected
  exact List.perm_middle

theorem Selected.slot (selected : Selected owners pid o restOwners) : o.slot = pid := by
  obtain ⟨_,_,_,_,slot,_⟩ := selected
  exact slot

theorem Selected.erase (selected : Selected owners pid o restOwners) :
    (owners.map Owner.slot).erase pid = restOwners.map Owner.slot := by
  obtain ⟨before,after,rfl,absent,slot,rfl⟩ := selected
  simp only [List.map_append,List.map_cons,slot]
  rw [List.erase_append_right _ absent,List.erase_cons_head]

theorem carrier_loans_perm (hi : CarrierState cs loans w) (hp : loans.Perm other) :
    CarrierState cs other w := by
  refine ⟨hi.inventory,hi.queues,?_,hi.keys⟩
  intro o
  have count : loans.count o = other.count o := by
    rw [List.count_eq_length_filter,List.count_eq_length_filter]
    exact (hp.filter _).length_eq
  simpa only [demand,←count] using hi.funded o

theorem selected_funded (hi : ClearWork.Inv cs (owners ++ loans) w)
    (selected : Selected owners pid o restOwners) :
    ClearWork.Inv cs (o :: (restOwners ++ loans)) w :=
  ⟨carrier_loans_perm hi.1 (by simpa using selected.perm.append_right loans),hi.2⟩

end Leanux.Proofs.WG.Queues.RxCredits.WorkReservations
