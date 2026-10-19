import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldRestore
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadySource
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationNativeRestoreFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryRestoreSource

/-! Native key invalidation and repayment retain the allocation prerequisites;
the actual restore then closes the sole selected location into full Entry.Inv.
Only the later queued-initiation callback remains a source obligation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance RetirementSecurity AllocatedObligation
open HandshakeSecurity.StagedConservation

variable {Safe : List Event → Prop}
variable (frontier : ∀ h, SoundHeld.Active ledger debts generation pid peer position h → Safe h)

include frontier in
theorem write_key (kid : KeypairId) (key : Keypair) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe (liftWGPrefix (setKeypair kid key)) :=
  decorate (SoundHeld.decorate frontier (HeldFrontier.held_write_key (fun _ => id) kid key))
    (erasesStatePrefix_lift _) (NativeReady.write_key kid key)

include frontier in
theorem put_key (kid : Option KeypairId) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe (liftWGPrefix (keypairPut kid false)) :=
  decorate (SoundHeld.decorate frontier (HeldFrontier.held_key_put (fun _ => id) kid))
    (erasesStatePrefix_lift _) (NativeReady.put_key kid)

include frontier in
theorem pure_ready (value : α) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe (pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ before => frontier _ before.toSound.active) (fun _ _ _ before => before)

include frontier in
theorem before_restore (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe
      (RestoreEntry.prefixWith liftWGPrefix packets keypair invalid) := by
  have tail (kp : Option KeypairId) :
      StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe (do
        liftWGPrefix (keypairPut kp false)
        for _ in packets do _ ← liftWGPrefix (branch .stagedOrphanWalk true)
        _ ← liftWGPrefix (branch .stagedOrphanWalk false)) := by
    apply StatePrefixEnsures.bind (put_key frontier kp)
    intro _
    apply StatePrefixEnsures.bind
    · apply StatePrefixEnsures.forInInvariant packets PUnit.unit _
        (fun _ => Ready ledger debts locals generation pid peer position) Safe
        (fun _ _ _ _ before => frontier _ before.toSound.active)
      intro packet acc
      exact StatePrefixEnsures.bind (ambient frontier (AmbientM.branch .stagedOrphanWalk true))
        (fun _ => pure_ready frontier _)
    · intro _
      exact StatePrefixEnsures.bind (ambient frontier (AmbientM.branch .stagedOrphanWalk false))
        (fun _ => pure_ready frontier _)
  unfold RestoreEntry.prefixWith
  dsimp only
  split
  · split
    · apply StatePrefixEnsures.bind (read_key frontier _)
      intro key
      exact StatePrefixEnsures.bind (write_key frontier _ _) (fun _ => tail _)
    · exact StatePrefixEnsures.bind (ambient frontier (AmbientM.invariant "unreachable"))
        (fun _ => tail _)
  · exact tail _

theorem restore (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (Safe : List Event → Prop)
    (entrySafe : ∀ h w, StagedEntry.Inv h (HeldFrontier.restoredLedger ledger generation pid peer position)
      debts locals w → Safe h) :
    StatePrefixEnsures (Ready ledger debts locals generation pid peer position) Safe
      (CausalJournal.stagedRestore pid peer.staged)
      (fun _ h w _ => StagedEntry.Inv h (HeldFrontier.restoredLedger ledger generation pid peer position) debts locals w) := by
  intro w a h before
  have active : StagedEntry.Active h ledger debts locals position w :=
    ⟨before.core,before.justified,before.links,before.only,before.native.1,before.native.2.1,before.native.2.2⟩
  let ready : StagedEntry.Restoration.Ready h ledger debts locals position generation pid peer.internalId peer.staged w :=
    ⟨active,before.vacant.1,before.vacant.2,before.aligned⟩
  obtain ⟨v,performed,normal⟩ := StagedEntry.Restoration.total ready a
  have entry := normal.2.2.2.1
  change runPrefix ((CausalJournal.stagedRestore pid peer.staged).run w) a h = _ at performed
  rw [performed]
  exact ⟨[.stagedRestored ⟨pid,peer.staged,⟨(),w,v,a,a⟩⟩],rfl,entrySafe _ _ entry,entry⟩

theorem no_key (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (keypair : Option KeypairId) (invalid : Bool) (Safe : List Event → Prop)
    (selectedSafe : ∀ h, SoundHeld.Active ledger debts generation pid peer position h → Safe h)
    (entrySafe : ∀ h w, StagedEntry.Inv h (HeldFrontier.restoredLedger ledger generation pid peer position)
      debts locals w → Safe h)
    (Post : List Event → WGWorld → Ambient → Prop)
    (queued : StatePrefixEnsures
      (fun h w _ => StagedEntry.Inv h (HeldFrontier.restoredLedger ledger generation pid peer position) debts locals w)
      Safe (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false) (fun _ => Post)) :
    StatePrefixEnsures (Ready ledger debts locals generation pid peer position) Safe
      (HeldSource.noKey pid peer keypair invalid) (fun _ => Post) := by
  unfold HeldSource.noKey
  rw [RestoreEntry.no_key_factor]
  exact StatePrefixEnsures.bind (before_restore selectedSafe peer.staged keypair invalid) (fun _ =>
    StatePrefixEnsures.bind (restore ledger debts locals generation pid peer position Safe entrySafe) (fun _ => queued))

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
