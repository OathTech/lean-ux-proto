import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSoundSource
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationNativeReadyFrames

/-! The selected carrier includes the native allocation preconditions. Thus
checked nonce traversal does not leave packet bounds or TX ownership to an
unrelated later entry assumption. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance RetirementSecurity
open HandshakeSecurity.StagedConservation

structure Ready (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List TxLocalBatch) (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (history : List Event) (w : WGWorld) (a : Ambient) : Prop
    extends toSound : SoundHeld.Held ledger debts generation pid peer position history w a where
  native : NativeReady.Inv locals w

theorem decorate {action : WGPrefix Event α} {source : WG.M α} {Safe : List Event → Prop}
    (rule : StatePrefixPreserves (SoundHeld.Held ledger debts generation pid peer position) Safe action)
    (erases : ErasesStatePrefix action source) (kept : Preserves (NativeReady.Inv locals) source) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe action := by
  intro w a h before
  obtain ⟨suffix,extended,safe,after⟩ := rule w a h before.toSound
  refine ⟨suffix,extended,safe,?_⟩
  cases result : (runPrefix (action.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    have nativeRun : (source.run w).run a = .ok ((value,v),b) := (erases w a h).symm.trans result
    exact ⟨by simpa only [result] using after,
      (hoare_iff_run_ambient _ _ _).mp kept w a value v b before.native nativeRun⟩

variable {Safe : List Event → Prop}
variable (frontier : ∀ h, SoundHeld.Active ledger debts generation pid peer position h → Safe h)

include frontier in
theorem ambient (action : AmbientM α) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe
      (liftWGPrefix (monadLift action : WG.M α)) :=
  decorate (SoundHeld.decorate frontier (HeldFrontier.held_ambient (fun _ => id) action))
    (erasesStatePrefix_lift _) (hoare_liftAmbient action _)

include frontier in
theorem world (action : WG.M α) (same : SameView id action) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe (liftWGPrefix action) :=
  decorate (SoundHeld.decorate frontier (HeldFrontier.held_world (fun _ => id) action same))
    (erasesStatePrefix_lift _) (NativeReady.world same)

include frontier in
theorem read_key (kid : KeypairId) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe (liftWGPrefix (getKeypair kid)) :=
  decorate (SoundHeld.decorate frontier (HeldFrontier.held_read_key (fun _ => id) kid))
    (erasesStatePrefix_lift _) (NativeReady.read_key kid)

include frontier in
theorem reserve (kid : KeypairId) :
    StatePrefixPreserves (Ready ledger debts locals generation pid peer position) Safe (state (Journal.reserve kid)) :=
  decorate (SoundHeld.decorate frontier (HeldFrontier.reservation_held (fun _ => id) kid))
    (reserve_erases kid) (NativeReady.reserve kid)

theorem checked (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List TxLocalBatch) (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (keypair : Option KeypairId) (Safe : List Event → Prop)
    (admitted : ∀ h, SoundHeld.Active ledger debts generation pid peer position h → Safe h)
    (Post : List Event → WGWorld → Ambient → Prop) (postSafe : ∀ h w a, Post h w a → Safe h)
    (noKey : Option KeypairId → Bool → WGPrefix Event Unit)
    (submit : KeypairId → List DataPacket → WGPrefix Event Unit)
    (rejected : ∀ kp invalid, StatePrefixEnsures (Ready ledger debts locals generation pid peer position) Safe
      (noKey kp invalid) (fun _ => Post))
    (submitted : ∀ kid packets, StatePrefixEnsures
      (fun h w a => Ready ledger debts locals generation pid peer position h w a ∧
        BatchPayload.Shape pid kid peer.staged packets) Safe (submit kid packets) (fun _ => Post)) :
    StatePrefixEnsures (Ready ledger debts locals generation pid peer position) Safe
      (RestoreEntry.checkedWith liftWGPrefix (fun kid => state (Journal.reserve kid)) noKey submit pid peer keypair)
      (fun _ => Post) :=
  CheckedCarrier.checked (Ready ledger debts locals generation pid peer position) pid peer keypair Safe
    (fun _ _ _ before => admitted _ before.toSound.active)
    (ambient admitted) (world admitted) (read_key admitted) (reserve admitted)
    Post postSafe noKey submit rejected submitted

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
