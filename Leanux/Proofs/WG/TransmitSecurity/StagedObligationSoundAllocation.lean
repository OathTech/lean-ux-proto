import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSoundHeld
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldAllocationSource

/-! Actual allocation preserves the semantic fixed-ticket claim. The original
birth-to-plaintext relation establishes each native allocation ordinal; every
selected location is empty on return, not merely the most recent location. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.SoundHeld
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance AllocatedObligation

theorem allocate (before : Held ledger debts generation pid peer position history w a)
    (shape : BatchPayload.Shape pid kid peer.staged packets)
    (bounded : Packets.Inv w)
    (ownership : RetirementSecurity.TxCoverage locals w)
    (inventory : RetirementSecurity.TxInventory locals w) :
    ∃ (items : List SkbId) (v : WGWorld),
      let receipt : WGRunWitness (List SkbId) := ⟨items,w,v,a,a⟩
      let events := history ++ [Event.old (.allocated packets receipt)]
      let after := assignBatch position history.length ledger
      runWGPrefix (state (Journal.allocate packets)) w a history = (.ok ((items,v),a),events) ∧
      receipt.Valid (packets.mapM newTxSkb) ∧ Staged.Obligations.Step ledger after ∧
      Core events after debts v ∧ Justified events after ∧ AllocationLinks events after ∧
      NoSelected after ∧
      RetirementSecurity.TxCoverage (⟨.unpublished,pid,items⟩ :: locals) v ∧
      RetirementSecurity.TxInventory (⟨.unpublished,pid,items⟩ :: locals) v := by
  obtain ⟨items,v,performed,native,step,core,_,coverage,occurrences⟩ :=
    HeldFrontier.allocate_held before.toHeld shape bounded ownership inventory
  have epoch := before.vacant.1
  cases device : w.dev with
  | none => simp [Packets.epoch,device] at epoch
  | some d =>
    exact ⟨items,v,performed,native,step,core,(before.justified.assigned _ _).append _,
      before.links.assigned packets ⟨items,w,v,a,a⟩ native device epoch
        (before.toHeld.allocation_alignment shape),before.only.assigned _,coverage,occurrences⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.SoundHeld
