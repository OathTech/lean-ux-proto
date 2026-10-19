import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSelected
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryRestoreSource
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldRestore

/-! Restoration moves the same selected tickets back to their actual vacant
peer queue. The exact transfer preserves all earlier terminal receipt counts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal StagedTerminalComplete CompleteCarrier

theorem restore (ledger : Ledger) (debts : List CleanupDebt) (locals : List RetirementSecurity.TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (Safe : List Event → Prop)
    (accountSafe : ∀ h w, Accounted h (HeldFrontier.restoredLedger ledger generation pid peer position)
      debts locals w → Safe h) :
    StatePrefixEnsures (Ready ledger debts locals generation pid peer position) Safe
      (CausalJournal.stagedRestore pid peer.staged)
      (fun _ h w _ => Accounted h (HeldFrontier.restoredLedger ledger generation pid peer position) debts locals w) := by
  intro w a h before
  have active : StagedEntry.Active h ledger debts locals position w :=
    ⟨before.core,before.justified,before.links,before.only,before.native.1,before.native.2.1,before.native.2.2⟩
  let ready : Restoration.Ready h ledger debts locals position generation pid peer.internalId peer.staged w :=
    ⟨active,before.vacant.1,before.vacant.2,before.aligned⟩
  obtain ⟨v,performed,normal⟩ := Restoration.total ready a
  have entry := normal.2.2.2.1
  have complete := (before.complete.transferred (.selected position)
    (.staged generation pid peer.internalId)).append_quiet
    (suffix := [Event.stagedRestored ⟨pid,peer.staged,⟨(),w,v,a,a⟩⟩])
    (fun _ member => by cases List.mem_singleton.mp member; intro pos; rfl)
  change runPrefix ((CausalJournal.stagedRestore pid peer.staged).run w) a h = _ at performed
  rw [performed]
  exact ⟨[.stagedRestored ⟨pid,peer.staged,⟨(),w,v,a,a⟩⟩],rfl,accountSafe _ _ ⟨entry,complete⟩,entry,complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
