import Leanux.Proofs.WG.TransmitSecurity.StagedObligationQueues
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTickets

/-! Settling a selected set retains every ledger entry and removes precisely
those tickets from its pending locations. Native cuts justify which set may be
settled; these list facts do not supply that source obligation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins

def settle (selected : List Ticket) (outcome : Terminal) (ledger : Ledger) : Ledger :=
  ledger.map fun entry =>
    (entry.1,if entry.1 ∈ selected then .terminal outcome else entry.2)

theorem settle_step (before : Ledger) (selected : List Ticket) (outcome : Terminal)
    (pending : ∀ ticket ∈ selected, ∀ status, (ticket,status) ∈ before →
      ∃ location, status = .pending location) :
    Step before (settle selected outcome before) := by
  induction before with
  | nil => exact .nil
  | cons entry rest ih =>
    apply Step.cons entry.1
    · by_cases chosen : entry.1 ∈ selected
      · obtain ⟨location,same⟩ := pending entry.1 chosen entry.2 (List.mem_cons_self ..)
        simp only [ite_eq_left chosen,same]
        exact .settle location outcome
      · simp only [ite_eq_right chosen]
        exact .retain _
    · apply ih
      intro ticket chosen status member
      exact pending ticket chosen status (List.mem_cons_of_mem _ member)

theorem mem_pendingAt : ticket ∈ pendingAt location ledger ↔
    (ticket,Status.pending location) ∈ ledger := by
  induction ledger with
  | nil => simp [pendingAt]
  | cons entry rest ih =>
    simp only [pendingAt,List.mem_filterMap,Prod.exists] at ih
    rcases entry with ⟨other,status⟩
    cases status with
    | terminal outcome => simp [pendingAt,ih,Prod.mk.injEq]
    | pending actual =>
      by_cases same : actual = location
      · subst actual
        simp [pendingAt,ih,Prod.mk.injEq]
      · simp [pendingAt,same,ih,Prod.mk.injEq,Ne.symm same]

theorem pendingAt_settle (selected : List Ticket) (outcome : Terminal)
    (ledger : Ledger) (location : Pending) :
    pendingAt location (settle selected outcome ledger) =
      (pendingAt location ledger).filter (fun ticket => decide (ticket ∉ selected)) := by
  induction ledger with
  | nil => rfl
  | cons entry rest ih =>
    simp only [settle,pendingAt,List.filterMap_map] at ih
    rcases entry with ⟨ticket,status⟩
    cases status with
    | terminal terminal =>
      by_cases chosen : ticket ∈ selected <;> simp [settle,pendingAt,chosen,ih]
    | pending actual =>
      by_cases same : actual = location <;>
        by_cases chosen : ticket ∈ selected <;> simp [settle,pendingAt,same,chosen,ih]

theorem filter_without_prefix {tickets : List Ticket} (unique : tickets.Nodup) (n : Nat) :
    tickets.filter (fun ticket : Ticket => decide (ticket ∉ tickets.take n)) =
      tickets.drop n := by
  obtain ⟨split,_,_,disjoint,_⟩ := HandshakeSecurity.StagedConservation.tickets_partition unique n
  have left : (tickets.take n).filter (fun ticket => decide (ticket ∉ tickets.take n)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro ticket member
    simp [member]
  have right : (tickets.drop n).filter (fun ticket => decide (ticket ∉ tickets.take n)) =
      tickets.drop n := by
    apply List.filter_eq_self.mpr
    intro ticket member
    have absent : ticket ∉ tickets.take n := fun chosen => disjoint ticket chosen member
    simp [absent]
  have filtered := congrArg (List.filter (fun ticket => decide (ticket ∉ tickets.take n))) split
  rw [List.filter_append,left,right,List.nil_append] at filtered
  exact filtered.symm

theorem pendingAt_unique (unique : (keys ledger).Nodup) (location : Pending) :
    (pendingAt location ledger).Nodup := by
  induction ledger with
  | nil => exact .nil
  | cons entry rest ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp unique
    rcases entry with ⟨ticket,status⟩
    cases status with
    | terminal outcome => exact ih tail
    | pending actual =>
      by_cases same : actual = location
      · subst actual
        have kept : (ticket :: pendingAt location rest).Nodup := by
          apply List.nodup_cons.mpr
          refine ⟨?_,ih tail⟩
          intro member
          exact fresh (List.mem_map.mpr ⟨(ticket,Status.pending location),mem_pendingAt.mp member,rfl⟩)
        simpa [pendingAt] using kept
      · simpa [pendingAt,same] using ih tail

theorem pendingAt_disjoint (unique : (keys ledger).Nodup) (different : left ≠ right)
    (first : ticket ∈ pendingAt left ledger) (second : ticket ∈ pendingAt right ledger) : False := by
  have equal := unique_status unique (mem_pendingAt.mp first) (mem_pendingAt.mp second)
  exact different (Status.pending.inj equal)

theorem settle_pending (unique : (keys ledger).Nodup)
    (selected : ∀ ticket ∈ chosen, ticket ∈ pendingAt location ledger) :
    Step ledger (settle chosen outcome ledger) := by
  apply settle_step
  intro ticket member status existing
  exact ⟨location,unique_status unique existing (mem_pendingAt.mp (selected ticket member))⟩

theorem settle_other_location (unique : (keys ledger).Nodup)
    (selected : ∀ ticket ∈ chosen, ticket ∈ pendingAt location ledger)
    (different : other ≠ location) :
    pendingAt other (settle chosen outcome ledger) = pendingAt other ledger := by
  rw [pendingAt_settle]
  apply List.filter_eq_self.mpr
  intro ticket member
  have absent : ticket ∉ chosen := fun chosen =>
    pendingAt_disjoint unique different member (selected ticket chosen)
  simp [absent]

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
