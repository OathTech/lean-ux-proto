import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionFrontOutcome
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationPhysicalSettlementFrames

/-! The front's exact ledger changes preserve allocated backing and selected
positions. Physical state equality is kept separate from ledger accounting;
an arbitrary valid disposal receipt alone cannot supply that equality. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal

theorem Checkpoint.allocated_frame (cut : Checkpoint entry history ledger snapshot) :
    AllocatedFrame entry.ledger ledger := by
  cases cut with
  | initial => exact .refl _
  | nonfinal => exact .refl _
  | released => exact settle_allocated_frame entry.valid (fun _ member => member) (by simp) _
  | trimmed => exact settle_allocated_frame entry.valid (fun _ member => List.mem_of_mem_take member) (by simp) _

theorem Checkpoint.selected (cut : Checkpoint entry history ledger snapshot)
    (before : SelectedRecorded entry.history entry.ledger) : SelectedRecorded history ledger := by
  cases cut with
  | initial => exact before
  | nonfinal => exact before.append _
  | released => exact (before.settled _ _).append _
  | trimmed => exact (before.settled _ _).append _

theorem Checkpoint.extends (cut : Checkpoint entry history ledger snapshot) :
    ∃ suffix, history = entry.history ++ suffix := by
  cases cut with
  | initial => exact ⟨[],by simp⟩
  | nonfinal => exact ⟨_,rfl⟩
  | released => exact ⟨_,rfl⟩
  | trimmed => exact ⟨_,rfl⟩

/-- This local lift requires equality at the actual accounted snapshot.
The separate source contract supplies it even when a later suffix stops. -/
theorem Checkpoint.core (cut : Checkpoint entry history ledger snapshot)
    (canonical : entry.births = births entry.history)
    (before : Core entry.history entry.ledger debts entry.world)
    (physical : PacketOrigins.snapshot snapshot = PacketOrigins.snapshot entry.world) :
    Core history ledger debts snapshot := by
  obtain ⟨suffix,append⟩ := cut.extends
  refine ⟨?_,cut.accounted.2.2.2,cut.selected before.selected,?_⟩
  · rw [cut.canonical canonical]
    exact cut.accounted.2.1
  · rw [append]
    exact ((before.physical.ledger_frame cut.allocated_frame).views
      (congrArg Prod.fst physical) (congrArg Prod.snd physical)).append suffix

theorem Normal.allocated_frame (normal : Normal entry input r history ledger) :
    AllocatedFrame entry.ledger ledger := by
  obtain ⟨prior,snapshot,cut,after⟩ := normal.2.2.2.2
  cases result : r.value with
  | error code =>
    rw [result] at after
    rw [after.1]
    exact cut.allocated_frame
  | ok pid =>
    rw [result] at after
    obtain ⟨w,a,generation,stamp,_,_,rfl⟩ := after
    have first := cut.allocated_frame
    have second := admission_allocated_frame (ledger := prior) generation pid stamp history.length
      (input.packets.map (fun p => {p with mtu := input.mtu}))
    exact ⟨fun _ _ _ => (second.pending _ _ _).trans (first.pending _ _ _),
      fun _ _ member => second.terminal _ _ (first.terminal _ _ member)⟩

theorem Normal.selected (normal : Normal entry input r history ledger)
    (before : SelectedRecorded entry.history entry.ledger) :
    SelectedRecorded (history ++ [routedEvent input r]) ledger := by
  obtain ⟨prior,snapshot,cut,after⟩ := normal.2.2.2.2
  cases result : r.value with
  | error code =>
    rw [result] at after
    rw [after.1]
    exact (cut.selected before).append _
  | ok pid =>
    rw [result] at after
    obtain ⟨w,a,generation,stamp,_,_,rfl⟩ := after
    exact ((cut.selected before).admitted _ _ _ _ _).append _

theorem Normal.core (normal : Normal entry input r history ledger)
    (before : Core entry.history entry.ledger debts entry.world)
    (physical : PacketOrigins.snapshot r.after = PacketOrigins.snapshot entry.world) :
    Core (history ++ [routedEvent input r]) ledger debts r.after := by
  obtain ⟨prior,snapshot,cut,_⟩ := normal.2.2.2.2
  obtain ⟨suffix,append⟩ := cut.extends
  refine ⟨normal.2.1,normal.2.2.1,normal.selected before.selected,?_⟩
  rw [append,List.append_assoc]
  exact ((before.physical.ledger_frame normal.allocated_frame).views
    (congrArg Prod.fst physical) (congrArg Prod.snd physical)).append _

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
