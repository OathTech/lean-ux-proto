import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldNativeFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreCarrier

/-! Ownership changes at the native restore receipt. The queueing continuation
starts with the restored fixed tickets and complete physical carrier; a Stop
before that receipt retains the selected take frontier instead. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal
open HandshakeSecurity.StagedConservation

def restoredLedger (ledger : Ledger) (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) : Ledger :=
  transferLocation (.selected position) (.staged generation pid peer.internalId) ledger

structure Restored (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (history : List Event) (w : WGWorld) (_ : Ambient) : Prop where
  cut : ∃ (past : List Event) (r : Restore.Receipt),
    history = past ++ [.stagedRestored r] ∧ r.pid = pid ∧ r.packets = peer.staged ∧
    r.Valid ∧ r.run.after = w ∧
    Held ledger debts generation pid peer position past r.run.before r.run.ambientBefore
  step : Step ledger (restoredLedger ledger generation pid peer position)
  core : Core history (restoredLedger ledger generation pid peer position) debts w
  empty : pendingAt (.selected position) (restoredLedger ledger generation pid peer position) = []
  located : pendingAt (.staged generation pid peer.internalId) (restoredLedger ledger generation pid peer position) =
    pendingAt (.selected position) ledger

/-- The restore cut accounts for the same selected tickets on both sides.
Stopped restore prefixes do not claim a final native state; their active take
frontier remains the safety certificate. -/
theorem restore_observed (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (Safe : List Event → Prop)
    (selectedSafe : ∀ h, Anchor ledger debts generation pid peer position h → Safe h)
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
  | error stop => exact ⟨[],by simp,selectedSafe _ before.anchor,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    cases value
    let r : Restore.Receipt := ⟨pid,peer.staged,⟨(),w,v,a,b⟩⟩
    have transfer := core_restore r run before.core before.vacant.1 before.vacant.2 position before.aligned
    have after : Restored ledger debts generation pid peer position (h ++ [.stagedRestored r]) v b :=
      ⟨⟨h,r,rfl,rfl,rfl,run,rfl,before⟩,transfer.1,transfer.2.1,transfer.2.2.1,transfer.2.2.2⟩
    exact ⟨[.stagedRestored r],rfl,restoredSafe _ _ _ after,after⟩

/-- Native invalidation and repayment, restoration and queueing compose in
their original order. The queue callback must preserve its own actual stopped
frontier; no completed queue or successful enclosing send is assumed here. -/
theorem no_key (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (keypair : Option KeypairId) (invalid : Bool)
    (Safe : List Event → Prop)
    (selectedSafe : ∀ h, Anchor ledger debts generation pid peer position h → Safe h)
    (restoredSafe : ∀ h w a, Restored ledger debts generation pid peer position h w a → Safe h)
    (queue : PeerId → Bool → WGPrefix Event Unit) (Post : List Event → WGWorld → Ambient → Prop)
    (queued : StatePrefixEnsures (Restored ledger debts generation pid peer position) Safe
      (queue pid false) (fun _ => Post)) :
    StatePrefixEnsures (Held ledger debts generation pid peer position) Safe
      (Restore.noKeyWith CausalJournal.effects CausalJournal.stagedRestore queue pid peer.staged keypair invalid)
      (fun _ => Post) := by
  rw [RestoreEntry.no_key_factor]
  exact StatePrefixEnsures.bind (prefix_held Safe selectedSafe peer.staged keypair invalid) (fun _ =>
    StatePrefixEnsures.bind
      (restore_observed ledger debts generation pid peer position Safe selectedSafe restoredSafe) (fun _ => queued))

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldFrontier
