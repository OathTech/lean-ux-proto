import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSoundHeld
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldRestore

/-! Actual restoration preserves terminal provenance and allocation lineage,
and closes the only active selected location before queueing an initiation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.SoundHeld
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance
open HandshakeSecurity.StagedConservation

structure Restored (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (history : List Event) (w : WGWorld) (a : Ambient) : Prop
    extends HeldFrontier.Restored ledger debts generation pid peer position history w a where
  justified : Justified history (HeldFrontier.restoredLedger ledger generation pid peer position)
  links : AllocationLinks history (HeldFrontier.restoredLedger ledger generation pid peer position)
  idle : NoSelected (HeldFrontier.restoredLedger ledger generation pid peer position)

theorem restore_observed (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (Safe : List Event → Prop)
    (selectedSafe : ∀ h, Active ledger debts generation pid peer position h → Safe h)
    (restoredSafe : ∀ h w a, Restored ledger debts generation pid peer position h w a → Safe h) :
    StatePrefixEnsures (Held ledger debts generation pid peer position) Safe
      (CausalJournal.stagedRestore pid peer.staged)
      (fun _ => Restored ledger debts generation pid peer position) := by
  intro w a h before
  unfold CausalJournal.stagedRestore Restore.observed
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (Restore.nativeRestore pid peer.staged))
    (fun run => Event.stagedRestored ⟨pid,peer.staged,run⟩) w a h
  rw [runWGPrefix_lift] at equation
  simp only [runWGPrefix,runStatePrefix] at equation
  rw [equation]
  cases run : ((Restore.nativeRestore pid peer.staged).run w).run a with
  | error stop => exact ⟨[],by simp,selectedSafe _ before.active,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    cases value
    let r : Restore.Receipt := ⟨pid,peer.staged,⟨(),w,v,a,b⟩⟩
    have transfer := core_restore r run before.core before.vacant.1 before.vacant.2 position before.aligned
    have base : HeldFrontier.Restored ledger debts generation pid peer position
        (h ++ [.stagedRestored r]) v b :=
      ⟨⟨h,r,rfl,rfl,rfl,run,rfl,before.toHeld⟩,transfer.1,transfer.2.1,transfer.2.2.1,transfer.2.2.2⟩
    have after : Restored ledger debts generation pid peer position (h ++ [.stagedRestored r]) v b :=
      ⟨base,(before.justified.transfer _ _).append _,
        (before.links.transferred _ _ (by intros; simp) (by intros; simp)).append _,
        before.only.restored _ _ _⟩
    exact ⟨[.stagedRestored r],rfl,restoredSafe _ _ _ after,after⟩

theorem no_key (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (keypair : Option KeypairId) (invalid : Bool)
    (Safe : List Event → Prop)
    (selectedSafe : ∀ h, Active ledger debts generation pid peer position h → Safe h)
    (restoredSafe : ∀ h w a, Restored ledger debts generation pid peer position h w a → Safe h)
    (queue : PeerId → Bool → WGPrefix Event Unit) (Post : List Event → WGWorld → Ambient → Prop)
    (queued : StatePrefixEnsures (Restored ledger debts generation pid peer position) Safe
      (queue pid false) (fun _ => Post)) :
    StatePrefixEnsures (Held ledger debts generation pid peer position) Safe
      (Restore.noKeyWith CausalJournal.effects CausalJournal.stagedRestore queue pid peer.staged keypair invalid)
      (fun _ => Post) := by
  rw [RestoreEntry.no_key_factor]
  apply StatePrefixEnsures.bind
    (decorate selectedSafe (HeldFrontier.prefix_held _ (fun _ => id) peer.staged keypair invalid))
  intro _
  exact StatePrefixEnsures.bind
    (restore_observed ledger debts generation pid peer position Safe selectedSafe restoredSafe) (fun _ => queued)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.SoundHeld
