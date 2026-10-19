import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCounted
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationPhysicalSettlementFrames

/-! The complete fixed ledger survives a native counted prefix disposal.
The queue/count partition and exact packet-material frame are separate native
facts; the caller must bind them to the particular recorded source arm. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins
open AuthenticatedEffects CausalJournal

theorem core_counted (p : HandshakeSecurity.StagedDisposal.Partition pid w v)
    (before : Core history ledger debts w) (epoch : Packets.epoch w = some generation)
    (event : Event) (quiet : birthPackets event = [])
    (arm : HandshakeSecurity.StagedDisposal.Arm)
    (cells : PacketMaterial.view v = PacketMaterial.view w) :
    let selected := (pendingAt (.staged generation pid p.stamp) ledger).take p.removed
    let after := settle selected (.counted history.length arm) ledger
    Step ledger after ∧ Core (history ++ [event]) after debts v ∧
      selected.length = p.removed ∧
      (∀ ticket ∈ selected, (ticket,Status.terminal (.counted history.length arm)) ∈ after) ∧
      (∃ count, dropped w = some count ∧ dropped v = some (count+selected.length)) := by
  dsimp only
  obtain ⟨step,valid,queues,length,terminals,charged⟩ :=
    counted_step p before.valid before.queues epoch history.length arm
  have chosen : ∀ ticket ∈ (pendingAt (.staged generation pid p.stamp) ledger).take p.removed,
      ticket ∈ pendingAt (.staged generation pid p.stamp) ledger :=
    fun _ member => List.mem_of_mem_take member
  have frame := settle_allocated_frame before.valid chosen (by intro _ _; simp)
    (.counted history.length arm)
  refine ⟨step,⟨?_,queues.append_history _,(before.selected.settled _ _).append _,
    ((before.physical.ledger_frame frame).views p.epoch cells).append _⟩,length,terminals,charged⟩
  rw [births_quiet _ quiet]
  exact valid

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
