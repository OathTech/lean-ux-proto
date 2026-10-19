import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionConfiguration

/-! Native shutdown and deletion retain their real queued-send drain. Device
creation and the post-drain destruction suffix use direct sent frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Configuration TransmitSecurity TransmitSecurity.Driver HandshakeSecurity HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

macro "emission_lifecycle_step" : tactic => `(tactic| first
  | (emission_native_head requireNotPending; unfold requireNotPending; exact state_pure _)
  | (emission_native_head purgeStagedPackets; apply state_native; sent_frame [purgeStagedPackets] using [getPeer_sent_spec,setPeer_sent_spec])
  | (emission_native_head handshakeClear; exact state_native _ (EmissionClearing.handshake _))
  | (emission_native_head resetLastSentHandshake; exact state_native _ (EmissionConfiguration.reset_handshake _))
  | (emission_native_head socketReinit; exact state_native _ (EmissionCleanup.socket_reinit _ _))
  | emission_removal_step)

theorem down : StateSafe (downObserved hooks) := by
  unfold downObserved
  rw [show hooks.stagedPurge = (fun pid => liftWGPrefix (purgeStagedPackets pid)) from rfl,
    Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle.down_neutral]
  unfold downWith stopWith timersStopWith
  repeat' first
    | (emission_head sendDrainObserved; exact send_drain _)
    | emission_lifecycle_step

theorem destruct : StateSafe (destructObserved hooks) := by
  change StateSafe (Configuration.destructWith liftWGPrefix (removeAllObserved hooks) _)
  unfold Configuration.destructWith
  repeat' first
    | (emission_head removeAllObserved; exact remove_all)
    | (emission_head liftWGPrefix; exact state_native _ EmissionLifecycle.destruct_finish)
    | emission_lifecycle_step

theorem device_create : StateSafe (liftWGPrefix wgCreate) :=
  state_native _ EmissionLifecycle.create

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
