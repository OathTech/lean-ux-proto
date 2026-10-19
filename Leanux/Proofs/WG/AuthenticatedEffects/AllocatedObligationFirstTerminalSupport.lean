import Leanux.Proofs.WG.TransmitSecurity.StagedObligationPhysicalFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalFrames

/-! A local conjunction of the existing fixed-ledger and physical carriers.
It includes pending cells and terminal cleanup debt. Source attribution and
initialized transport are separate; none is assumed by this abbreviation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

structure Support (births : List Ticket) (history : List CausalJournal.Event)
    (ledger : Ledger) (debts : List CleanupDebt) (w : WGWorld) : Prop
    extends Physical history ledger debts w where
  valid : Valid births ledger

theorem Support.append (before : Support births history ledger debts w)
    (suffix : List CausalJournal.Event) : Support births (history ++ suffix) ledger debts w :=
  ⟨before.toPhysical.append suffix,before.valid⟩

theorem Support.views (before : Support births history ledger debts w)
    (epoch : Packets.epoch v = Packets.epoch w)
    (cells : PacketMaterial.view v = PacketMaterial.view w) : Support births history ledger debts v :=
  ⟨before.toPhysical.views epoch cells,before.valid⟩

/-- The same pending allocation becomes cleanup debt at its first terminal.
This ledger operation changes no native cell and preserves mixed uniqueness. -/
theorem Support.settle (before : Support births history ledger debts w)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (outcome : Staged.Obligations.Terminal) :
    Staged.Obligations.Step ledger (settle [ticket] outcome ledger) ∧
      Support births history (settle [ticket] outcome ledger)
        (⟨ticket,position,ordinal,outcome⟩ :: debts) w ∧
      (ticket,Status.terminal outcome) ∈ settle [ticket] outcome ledger := by
  have selected : ∀ t ∈ [ticket], t ∈ pendingAt (.allocated position ordinal) ledger := by
    intro t member
    have same : t = ticket := by simpa using member
    subst t
    exact mem_pendingAt.mpr pending
  have step := settle_pending (before.valid.1.symm ▸ before.valid.2) selected (outcome := outcome)
  refine ⟨step,⟨⟨?_,before.covered.settle before.valid pending outcome,
    before.cleanup.settle before.resident before.valid pending outcome,
    before.mixed.settle before.cleanup pending outcome⟩,step.valid before.valid⟩,?_⟩
  · intro other batch index member
    exact before.resident other batch index (pending_after_settle [ticket] outcome member).1
  · exact List.mem_map.mpr ⟨(ticket,Status.pending (.allocated position ordinal)),pending,by simp⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
