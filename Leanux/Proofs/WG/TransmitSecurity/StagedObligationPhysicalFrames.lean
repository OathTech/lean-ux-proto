import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationMixedFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSelectedPositions

/-! Staging changes preserve the allocated component of the same ledger.
Pending and cleanup-debt coverage are both transported: retaining only pending
cells would lose cells after their first terminal result and before free. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins
open AuthenticatedEffects AllocatedObligation

structure Physical (history : List CausalJournal.Event) (ledger : Ledger)
    (debts : List CleanupDebt) (w : WGWorld) : Prop where
  resident : Resident history ledger w
  covered : Covered history ledger debts w
  cleanup : DebtsResident history ledger debts w
  mixed : MixedInjective history ledger debts

/-- A ledger update outside allocated ownership preserves exact pending
membership and every old first terminal result. -/
structure AllocatedFrame (before after : Ledger) : Prop where
  pending : ∀ ticket position ordinal,
    (ticket,Status.pending (.allocated position ordinal)) ∈ after ↔
      (ticket,Status.pending (.allocated position ordinal)) ∈ before
  terminal : ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ before →
    (ticket,Status.terminal outcome) ∈ after

theorem AllocatedFrame.refl (ledger : Ledger) : AllocatedFrame ledger ledger :=
  ⟨fun _ _ _ => Iff.rfl,fun _ _ member => member⟩

theorem AllocatedFrame.tracked (frame : AllocatedFrame before after)
    (cleanup : DebtsResident history before debts w) :
    Tracked after debts ticket position ordinal ↔ Tracked before debts ticket position ordinal := by
  constructor
  · intro tracked
    rcases tracked with pending | ⟨outcome,member,_⟩
    · exact Or.inl ((frame.pending _ _ _).mp pending)
    · exact Or.inr ⟨outcome,member,(cleanup _ member).1⟩
  · intro tracked
    rcases tracked with pending | ⟨outcome,member,terminal⟩
    · exact Or.inl ((frame.pending _ _ _).mpr pending)
    · exact Or.inr ⟨outcome,member,frame.terminal _ _ terminal⟩

theorem Physical.ledger_frame (before : Physical history ledger debts w)
    (frame : AllocatedFrame ledger after) : Physical history after debts w := by
  refine ⟨?_,?_,?_,?_⟩
  · intro ticket position ordinal member
    exact before.resident ticket position ordinal ((frame.pending _ _ _).mp member)
  · intro id value cell
    obtain ⟨generation,ticket,position,ordinal,epoch,origin,tracked⟩ := before.covered id value cell
    exact ⟨generation,ticket,position,ordinal,epoch,origin,(frame.tracked before.cleanup).mpr tracked⟩
  · intro debt member
    obtain ⟨terminal,backed⟩ := before.cleanup debt member
    exact ⟨frame.terminal _ _ terminal,backed⟩
  · intro first firstPosition firstOrdinal firstTracked second secondPosition secondOrdinal secondTracked
      generation id firstValue secondValue firstOrigin secondOrigin
    exact before.mixed first firstPosition firstOrdinal ((frame.tracked before.cleanup).mp firstTracked)
      second secondPosition secondOrdinal ((frame.tracked before.cleanup).mp secondTracked)
      generation id firstValue secondValue firstOrigin secondOrigin

theorem Physical.views (before : Physical history ledger debts w)
    (epoch : Packets.epoch v = Packets.epoch w)
    (cells : PacketMaterial.view v = PacketMaterial.view w) : Physical history ledger debts v :=
  ⟨fun _ _ _ member => (before.resident _ _ _ member).views epoch cells,
    before.covered.views epoch cells,before.cleanup.views epoch cells,before.mixed⟩

theorem Physical.append (before : Physical history ledger debts w)
    (suffix : List CausalJournal.Event) : Physical (history ++ suffix) ledger debts w :=
  ⟨before.resident.append suffix,before.covered.append suffix,before.cleanup.append suffix,
    before.mixed.append before.resident before.cleanup suffix⟩

theorem physical_initial (net bare : Bool) : Physical [] [] [] (Runner.initialWG net bare) :=
by
  refine ⟨?_,covered_initial net bare,debts_empty _ _ _,mixed_empty _⟩
  intro _ _ _ member
  cases member

theorem transfer_allocated_frame (source target : Pending)
    (notSource : ∀ position ordinal, Pending.allocated position ordinal ≠ source)
    (notTarget : ∀ position ordinal, Pending.allocated position ordinal ≠ target) :
    AllocatedFrame ledger (transferLocation source target ledger) := by
  refine ⟨?_,fun _ _ member => (transferLocation_step _ _ _).terminal member⟩
  intro ticket position ordinal
  rw [←mem_pendingAt,←mem_pendingAt,pendingAt_transfer_other (notSource _ _) (notTarget _ _)]

theorem take_allocated_frame (generation pid stamp position : Nat) :
    AllocatedFrame ledger (transferLocation (.staged generation pid stamp) (.selected position) ledger) :=
  transfer_allocated_frame _ _ (by intro _ _; simp) (by intro _ _; simp)

theorem restore_allocated_frame (generation pid stamp position : Nat) :
    AllocatedFrame ledger (transferLocation (.selected position) (.staged generation pid stamp) ledger) :=
  transfer_allocated_frame _ _ (by intro _ _; simp) (by intro _ _; simp)

theorem admission_allocated_frame (generation pid stamp birthPosition : Nat) (packets : List Packet) :
    AllocatedFrame ledger
      (StagedAdmission.appendBirths ledger birthPosition (.staged generation pid stamp) packets) := by
  refine ⟨?_,fun _ _ member => StagedAdmission.retains member⟩
  intro ticket position ordinal
  rw [←mem_pendingAt,←mem_pendingAt,StagedAdmission.pending_other (by simp)]

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
