import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationInjectiveFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationBatch

/-! Assign the actual selected ticket list to batch ordinals without changing
ledger order or replacing its tickets. Other pending entries and all terminal
outcomes remain unchanged. Native allocator transport lives above this map. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

def ticketOrdinal (ticket : Ticket) : List Ticket → Nat
  | [] => 0
  | first :: rest => if ticket = first then 0 else ticketOrdinal ticket rest + 1

theorem ticketOrdinal_get (member : ticket ∈ tickets) :
    tickets[ticketOrdinal ticket tickets]? = some ticket := by
  induction tickets with
  | nil => cases member
  | cons first rest ih =>
    by_cases same : ticket = first
    · subst first
      simp [ticketOrdinal]
    · have inside : ticket ∈ rest := (List.mem_cons.mp member).resolve_left same
      simpa [ticketOrdinal,same] using ih inside

theorem nodup_ordinal {items : List α} {left right : Nat} {value : α} (unique : items.Nodup)
    (first : items[left]? = some value) (second : items[right]? = some value) : left = right := by
  induction items generalizing left right with
  | nil => simp at first
  | cons item rest ih =>
    obtain ⟨absent,tail⟩ := List.nodup_cons.mp unique
    cases left with
    | zero =>
      have same : item = value := Option.some.inj first
      subst item
      cases right with
      | zero => rfl
      | succ right => exact False.elim (absent (List.mem_of_getElem? second))
    | succ left =>
      cases right with
      | zero =>
        have same : item = value := Option.some.inj second
        subst item
        exact False.elim (absent (List.mem_of_getElem? first))
      | succ right => exact congrArg Nat.succ (ih tail first second)

theorem ticketOrdinal_at (unique : tickets.Nodup) (atTicket : tickets[index]? = some ticket) :
    ticketOrdinal ticket tickets = index :=
  nodup_ordinal unique (ticketOrdinal_get (List.mem_of_getElem? atTicket)) atTicket

def assignEntry (takePosition batchPosition : Nat) (tickets : List Ticket)
    (entry : Ticket × Status) : Ticket × Status :=
  (entry.1,match entry.2 with
    | .pending (.selected actual) =>
      if actual = takePosition then .pending (.allocated batchPosition (ticketOrdinal entry.1 tickets))
      else entry.2
    | .pending (.staged epoch pid allocation) => .pending (.staged epoch pid allocation)
    | .pending (.allocated position ordinal) => .pending (.allocated position ordinal)
    | .terminal outcome => .terminal outcome)

def assignBatch (takePosition batchPosition : Nat) (ledger : Ledger) : Ledger :=
  ledger.map (assignEntry takePosition batchPosition (pendingAt (.selected takePosition) ledger))

theorem assignEntry_step (takePosition batchPosition : Nat) (tickets : List Ticket) (ledger : Ledger) :
    TransmitSecurity.Staged.Obligations.Step ledger
      (ledger.map (assignEntry takePosition batchPosition tickets)) := by
  induction ledger with
  | nil => exact .nil
  | cons entry rest ih =>
    obtain ⟨ticket,status⟩ := entry
    apply TransmitSecurity.Staged.Obligations.Step.cons ticket ?_ ih
    cases status with
    | terminal _ => exact .retain _
    | pending location =>
      cases location with
      | staged _ _ _ => exact .retain _
      | allocated _ _ => exact .retain _
      | selected actual =>
        by_cases same : actual = takePosition
        · simpa only [assignEntry,same,ite_true] using
            Change.transfer (.selected actual) (.allocated batchPosition (ticketOrdinal ticket tickets))
        · simpa only [assignEntry,same,ite_false] using Change.retain (.pending (.selected actual))

theorem assignBatch_step (takePosition batchPosition : Nat) (ledger : Ledger) :
    TransmitSecurity.Staged.Obligations.Step ledger (assignBatch takePosition batchPosition ledger) :=
  assignEntry_step takePosition batchPosition _ ledger

theorem assignBatch_cases
    (member : (ticket,Status.pending (.allocated position ordinal)) ∈ assignBatch takePosition batchPosition ledger) :
    (ticket,Status.pending (.allocated position ordinal)) ∈ ledger ∨
      ((ticket,Status.pending (.selected takePosition)) ∈ ledger ∧ position = batchPosition ∧
        ordinal = ticketOrdinal ticket (pendingAt (.selected takePosition) ledger)) := by
  obtain ⟨⟨old,status⟩,before,equal⟩ := List.mem_map.mp member
  have sameTicket : old = ticket := congrArg Prod.fst equal
  subst old
  cases status with
  | terminal outcome => simp [assignEntry] at equal
  | pending location =>
    cases location with
    | staged epoch pid allocation => simp [assignEntry] at equal
    | allocated oldPosition oldOrdinal =>
      have same := Status.pending.inj (Prod.mk.inj equal).2
      cases same
      exact Or.inl before
    | selected actual =>
      by_cases chosen : actual = takePosition
      · subst actual
        simp only [assignEntry,ite_true] at equal
        obtain ⟨samePosition,sameOrdinal⟩ := Pending.allocated.inj (Status.pending.inj (Prod.mk.inj equal).2)
        exact Or.inr ⟨before,samePosition.symm,sameOrdinal.symm⟩
      · simp [assignEntry,chosen] at equal

theorem assignBatch_selected
    (member : (ticket,Status.pending (.selected takePosition)) ∈ ledger) :
    (ticket,Status.pending (.allocated batchPosition
      (ticketOrdinal ticket (pendingAt (.selected takePosition) ledger)))) ∈
      assignBatch takePosition batchPosition ledger := by
  exact List.mem_map.mpr ⟨_,member,by simp [assignEntry]⟩

/-- The ordinal of each actual selected ticket is retained, including when
packet values repeat. Selected-ticket uniqueness follows from the fixed ledger. -/
theorem assignBatch_at (valid : Valid births ledger)
    (atTicket : (pendingAt (.selected takePosition) ledger)[ordinal]? = some ticket) :
    (ticket,Status.pending (.allocated batchPosition ordinal)) ∈ assignBatch takePosition batchPosition ledger := by
  have unique : (keys ledger).Nodup := valid.1.symm ▸ valid.2
  have mapped := assignBatch_selected (batchPosition := batchPosition)
    (mem_pendingAt.mp (List.mem_of_getElem? atTicket))
  rw [ticketOrdinal_at (pendingAt_unique unique _) atTicket] at mapped
  exact mapped

theorem assignBatch_selected_empty (takePosition batchPosition : Nat) (ledger : Ledger) :
    pendingAt (.selected takePosition) (assignBatch takePosition batchPosition ledger) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro ticket member
  obtain ⟨⟨old,status⟩,_,equal⟩ := List.mem_map.mp (mem_pendingAt.mp member)
  cases status with
  | terminal outcome => simp [assignEntry] at equal
  | pending location =>
    cases location with
    | staged epoch pid allocation => simp [assignEntry] at equal
    | allocated position ordinal => simp [assignEntry] at equal
    | selected actual =>
      by_cases same : actual = takePosition <;> simp [assignEntry,same] at equal

theorem assignBatch_staged (takePosition batchPosition generation pid allocation : Nat) (ledger : Ledger) :
    pendingAt (.staged generation pid allocation) (assignBatch takePosition batchPosition ledger) =
      pendingAt (.staged generation pid allocation) ledger := by
  unfold assignBatch pendingAt
  rw [List.filterMap_map]
  congr 1
  funext entry
  obtain ⟨ticket,status⟩ := entry
  cases status with
  | terminal outcome => rfl
  | pending location =>
    cases location with
    | staged epoch peer stamp => rfl
    | allocated position ordinal => rfl
    | selected actual =>
      by_cases same : actual = takePosition <;> simp [assignEntry,same]

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
