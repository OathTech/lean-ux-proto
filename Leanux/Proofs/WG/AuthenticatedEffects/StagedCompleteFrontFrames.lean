import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryFront

/-! The front's native ownership projection supplies all packet geometry and
physical ownership fields needed by the paired accounting adapter. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteFront
open Leanux Leanux.WG
open TransmitSecurity RetirementSecurity AllocatedObligation StagedAdmission.Front

theorem physical (before : Inv h ledger debts locals w)
    (same : Ownership.view v = Ownership.view w) :
    Packets.Inv v ∧ TxCoverage locals v ∧ TxInventory locals v := by
  have snapshot : Packets.snapshot v = Packets.snapshot w := congrArg (fun x => x.1.1) same
  have cells : Queues.TxDisposition.txPackets v = Queues.TxDisposition.txPackets w :=
    congrArg (fun x => x.1.2) same
  have owners : txQueueContents v = txQueueContents w := congrArg Prod.snd same
  exact ⟨by simpa only [Packets.Inv,snapshot] using before.packets,
    before.coverage.cells cells owners,before.inventory.queueContents owners cells⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteFront
