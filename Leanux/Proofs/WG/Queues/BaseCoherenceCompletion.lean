import Leanux.Proofs.WG.Queues.BaseCoherenceTraffic

/-! Base-list/table structure through actual receive completion and the timer
leaves it calls. Nullable lookup payment and staged-send refusals remain part
of the normal-source contracts. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem passive_configured {α : Type} {action : WG.M α}
    (passive : SameView DurableHolders.passiveView action)
    (configured : SameView ConfiguredIdentity.view action) : SameView view action :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.list_configured)
    (passive.of_factor Prod.fst slots (fun _ => rfl)) configured

theorem modTimer_view (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView view (modPeerTimer site pid timer delay) :=
  passive_configured
    ((pinned_const _private.Leanux.Proofs.WG.Queues.PassiveHolders.«0».Leanux.Proofs.WG.Queues.RxCredits.PassiveHolders.mod_preserves) site pid timer delay)
    (ConfiguredIdentity.modPeerTimer_view site pid timer delay)

theorem traversal_view (pid : PeerId) : SameView view (timersTraversal pid) :=
  passive_configured
    ((pinned_const _private.Leanux.Proofs.WG.Queues.PassiveHolders.«0».Leanux.Proofs.WG.Queues.RxCredits.PassiveHolders.traversal_preserves) pid)
    (ConfiguredIdentity.timersTraversal_view pid)

theorem handshakeComplete_view (pid : PeerId) (site : HiddenSite) :
    SameView view (timersHandshakeComplete pid site) :=
  passive_configured
    ((pinned_const _private.Leanux.Proofs.WG.Queues.PassiveHolders.«0».Leanux.Proofs.WG.Queues.RxCredits.PassiveHolders.handshake_preserves) pid site)
    (ConfiguredReceiveLeaves.timersHandshakeComplete_view pid site)

theorem dataReceived_view (pid : PeerId) : SameView view (timersDataReceived pid) :=
  passive_configured
    ((pinned_const _private.Leanux.Proofs.WG.Queues.PassiveHolders.«0».Leanux.Proofs.WG.Queues.RxCredits.PassiveHolders.dataReceived_preserves) pid)
    (ConfiguredReceiveLeaves.timersDataReceived_view pid)

theorem received_view (pid : PeerId) (kid : KeypairId) :
    SameView view (receivedWithKeypair pid kid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' base_rx_step initial

theorem freshRx_view (pid : PeerId) : SameView view (keepKeyFreshRx pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact (sendQueued_view _ _).wp (fun s => s = initial))
    | base_rx_step initial

theorem lookupSrc_view (protocol : Nat) (bytes : List UInt8) :
    SameView view (lookupSrc protocol bytes) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherence.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.borrow_view)
    ((hoare_iff_run_ambient _ _ _).mp (RxBorrow.lookupSrc_spec protocol bytes (wgStoreView w)) w a result v b rfl run)

private theorem stats_view (pid : PeerId) (len : Nat) : SameView view (updateRxStats pid len) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold updateRxStats
  repeat' base_rx_step initial

private theorem dishonest_view (why : Dishonest) : SameView view (dishonest why) := by
  cases why <;> intro initial <;> change Preserves (fun w => view w = initial) _
  all_goals unfold dishonest
  all_goals repeat' base_rx_step initial

/-- The full normal completion retains structural coherence even when the
source lookup's final peer payment erases its resident object. -/
theorem consumeDataDone_view (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    SameView view (consumeDataDone pid pkt endpoint) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold consumeDataDone WG.andM WG.orM timersAnyAuthenticatedPacketReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerEndpoint; exact (endpoint_view _ _).wp (fun s => s = initial))
    | (rx_retention_head receivedWithKeypair; exact (received_view _ _).wp (fun s => s = initial))
    | (rx_retention_head sendStagedPackets; exact (staged_view _).wp (fun s => s = initial))
    | (rx_retention_head keepKeyFreshRx; exact (freshRx_view _).wp (fun s => s = initial))
    | (rx_retention_head timersHandshakeComplete; exact (handshakeComplete_view _ _).wp (fun s => s = initial))
    | (rx_retention_head timersTraversal; exact (traversal_view _).wp (fun s => s = initial))
    | (rx_retention_head timersDataReceived; exact (dataReceived_view _).wp (fun s => s = initial))
    | (rx_retention_head delTimer; exact (delTimer_view _ _).wp (fun s => s = initial))
    | (rx_retention_head updateRxStats; exact (stats_view _ _).wp (fun s => s = initial))
    | (rx_retention_head dishonest; exact (dishonest_view _).wp (fun s => s = initial))
    | (rx_retention_head lookupSrc; exact (lookupSrc_view _ _).wp (fun s => s = initial))
    | (rx_retention_head inetEcnDecapsulate; exact (store_view (inetEcnDecapsulate_sameWGStore _ _ _)).wp (fun s => s = initial))
    | base_rx_step initial

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
