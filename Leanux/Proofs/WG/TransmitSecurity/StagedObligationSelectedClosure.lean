import Leanux.Proofs.WG.TransmitSecurity.StagedObligationAllocationFrames

/-! A finished staging invocation cannot leave a selected ticket at an old
take position. While the invocation is active only its own take may hold
selected tickets; restoration or total allocation clears that last location. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins
open AuthenticatedEffects AllocatedObligation

def NoSelected (ledger : Ledger) : Prop := ∀ position, pendingAt (.selected position) ledger = []

def OnlySelected (position : Nat) (ledger : Ledger) : Prop :=
  ∀ other, other ≠ position → pendingAt (.selected other) ledger = []

theorem no_selected_empty : NoSelected [] := fun _ => rfl

theorem NoSelected.taken (before : NoSelected ledger) (generation pid stamp position : Nat) :
    OnlySelected position (transferLocation (.staged generation pid stamp) (.selected position) ledger) := by
  intro other different
  rw [pendingAt_transfer_other (by simp) (by simp [different])]
  exact before other

theorem OnlySelected.restored (before : OnlySelected position ledger) (generation pid stamp : Nat) :
    NoSelected (transferLocation (.selected position) (.staged generation pid stamp) ledger) := by
  intro other
  by_cases same : other = position
  · subst other
    exact pendingAt_transfer_source (by simp) ledger
  · rw [pendingAt_transfer_other (by simp [same]) (by simp)]
    exact before other same

theorem OnlySelected.assigned (before : OnlySelected takePosition ledger) (batchPosition : Nat) :
    NoSelected (assignBatch takePosition batchPosition ledger) := by
  intro position
  by_cases same : position = takePosition
  · subst position
    exact assignBatch_selected_empty _ _ _
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro ticket member
    obtain ⟨⟨old,status⟩,prior,equal⟩ := List.mem_map.mp (mem_pendingAt.mp member)
    have sameTicket : old = ticket := congrArg Prod.fst equal
    subst old
    cases status with
    | terminal outcome => simp [assignEntry] at equal
    | pending location =>
      cases location with
      | staged generation pid stamp => simp [assignEntry] at equal
      | allocated batch index => simp [assignEntry] at equal
      | selected actual =>
        by_cases chosen : actual = takePosition
        · simp [assignEntry,chosen] at equal
        · have samePosition : actual = position := by simpa [assignEntry,chosen] using equal
          subst actual
          have present := mem_pendingAt.mpr prior
          rw [before position same] at present
          cases present

theorem NoSelected.settled (before : NoSelected ledger) (tickets : List Ticket) (outcome : Terminal) :
    NoSelected (settle tickets outcome ledger) := by
  intro position
  rw [pendingAt_settle,before position]
  rfl

theorem NoSelected.admitted (before : NoSelected ledger) (birthPosition generation pid stamp : Nat)
    (packets : List Packet) :
    NoSelected (StagedAdmission.appendBirths ledger birthPosition (.staged generation pid stamp) packets) := by
  intro position
  rw [StagedAdmission.pending_other (by simp)]
  exact before position

/-- The actual take's deterministic ledger transfer starts the sole selected
location. This fact is independent of successful key borrowing. -/
theorem take_selected_only {births : List Ticket} (r : HandshakeSecurity.StagedConservation.Take.Receipt)
    (chosen : r.run.value = some peer) (accounted : TakeAccounted births ledger history r after)
    (before : NoSelected ledger) : OnlySelected history.length after := by
  have transfer := accounted.exactTransfer
  rw [chosen] at transfer
  obtain ⟨generation,_,same,_,_⟩ := transfer
  rw [same]
  exact before.taken generation r.pid peer.internalId history.length

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
