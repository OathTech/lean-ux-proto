import Leanux.Proofs.WG.TransmitSecurity.StagedObligationLedgerFacts

/-! Pointwise ownership and terminal changes retain the same ordered ledger,
including tickets belonging to other queues between the selected entries. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins

theorem Change.trans (first : Change before middle) (second : Change middle after) :
    Change before after := by
  cases first <;> cases second <;> first
    | exact .retain _
    | exact .transfer _ _
    | exact .settle _ _

theorem Step.refl (ledger : Ledger) : Step ledger ledger := by
  induction ledger with
  | nil => exact .nil
  | cons entry rest ih => exact .cons entry.1 (.retain entry.2) ih

theorem Step.trans (first : Step before middle) (second : Step middle after) :
    Step before after := by
  induction first generalizing after with
  | nil => exact second
  | cons ticket change tail ih =>
    cases second with
    | cons _ next rest => exact .cons ticket (change.trans next) (ih rest)

/-- Settle exactly the selected existing records. The explicit pending
premise excludes replacing any earlier terminal result. -/
theorem settle_selection (before : Ledger) (selected : List Ticket) (outcome : Terminal)
    (pending : ∀ ticket ∈ selected, ∀ status, (ticket,status) ∈ before →
      ∃ location, status = .pending location) :
    ∃ after, Step before after ∧ ∀ ticket status, (ticket,status) ∈ before →
      (ticket,if ticket ∈ selected then .terminal outcome else status) ∈ after := by
  induction before with
  | nil => exact ⟨[],.nil,by intro ticket status member; cases member⟩
  | cons entry rest ih =>
    obtain ⟨later,step,preserved⟩ := ih (by
      intro ticket chosen status member
      exact pending ticket chosen status (List.mem_cons_of_mem _ member))
    let result := if entry.1 ∈ selected then Status.terminal outcome else entry.2
    have changed : Change entry.2 result := by
      by_cases chosen : entry.1 ∈ selected
      · obtain ⟨location,same⟩ := pending entry.1 chosen entry.2 (List.mem_cons_self ..)
        simp only [result,ite_eq_left chosen,same]
        exact .settle location outcome
      · simp only [result,ite_eq_right chosen]
        exact .retain _
    refine ⟨(entry.1,result) :: later,.cons entry.1 changed step,?_⟩
    intro ticket status member
    rcases List.mem_cons.mp member with equal | inside
    · cases equal
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (preserved ticket status inside)

/-- Admission extends the ledger with fresh source-position tickets. Existing
terminal records stay in place; byte-identical packets receive distinct ordinals. -/
theorem admit_at (valid : Valid births ledger) (position : Nat) (packets : List Packet)
    (location : Pending) (earlier : ∀ ticket ∈ births, ticket.position < position) :
    Valid (births ++ freshTickets position 0 packets)
      (ledger ++ (freshTickets position 0 packets).map (fun ticket => (ticket,Status.pending location))) := by
  constructor
  · simp only [keys,List.map_append,List.map_map,Function.comp_def]
    change keys ledger ++ List.map id (freshTickets position 0 packets) = _
    rw [List.map_id,valid.1]
  · apply List.nodup_append.mpr
    refine ⟨valid.2,freshTickets_unique _ _ _,?_⟩
    intro left leftMember right rightMember equal
    have lt := earlier left leftMember
    have atPosition := (freshTickets_fields rightMember).1
    subst right
    omega

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
