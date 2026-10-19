import Leanux.Proofs.WG.TransmitSecurity.StagedObligationQueueFrames

/-! Fresh birth admission extends the fixed ledger. Every old status remains
in place, including its first terminal result. The strict source-position bound
is an explicit local carrier obligation, not an initialized assumption. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission
open Leanux Leanux.WG
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

def Bounded (position : Nat) (births : List Ticket) : Prop :=
  ∀ ticket ∈ births, ticket.position < position

def appendBirths (ledger : Ledger) (position : Nat) (location : Pending) (packets : List Packet) : Ledger :=
  ledger ++ (freshTickets position 0 packets).map (fun ticket => (ticket,Status.pending location))

theorem bounded_append (before : Bounded position births) (packets : List Packet) :
    Bounded (position+1) (births ++ freshTickets position 0 packets) := by
  intro ticket member
  rcases List.mem_append.mp member with old | fresh
  · have earlier := before ticket old
    omega
  · have atPosition := (freshTickets_fields fresh).1
    omega

theorem bounded_mono (before : Bounded position births) (later : position ≤ next) :
    Bounded next births := fun ticket member => Nat.lt_of_lt_of_le (before ticket member) later

theorem valid (before : Valid births ledger) (bounded : Bounded position births) :
    Valid (births ++ freshTickets position 0 packets) (appendBirths ledger position location packets) :=
  admit_at before position packets location bounded

theorem retains (member : (ticket,status) ∈ ledger) :
    (ticket,status) ∈ appendBirths ledger position location packets := List.mem_append_left _ member

/-- Appending a fresh birth cannot replace any existing terminal result, even
when the new packet has bytes equal to an old packet. -/
theorem terminal_unchanged (before : Valid births ledger) (bounded : Bounded position births)
    (settled : (ticket,Status.terminal outcome) ∈ ledger)
    (later : (ticket,status) ∈ appendBirths ledger position location packets) :
    status = .terminal outcome := by
  have after := valid (packets := packets) (location := location) before bounded
  exact unique_status (after.1.symm ▸ after.2) later (retains settled)

theorem pending_append (query : Pending) :
    pendingAt query (appendBirths ledger position location packets) =
      pendingAt query ledger ++
        if location = query then freshTickets position 0 packets else [] := by
  simp only [appendBirths,pendingAt,List.filterMap_append,List.filterMap_map,Function.comp_def]
  by_cases same : location = query
  · subst query
    simp only [ite_true,List.filterMap_some]
  · simp only [same,ite_false]
    simp

theorem pending_other (different : location ≠ query) :
    pendingAt query (appendBirths ledger position location packets) = pendingAt query ledger := by
  rw [pending_append,ite_eq_right different,List.append_nil]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission
