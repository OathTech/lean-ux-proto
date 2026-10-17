import Leanux.Proofs.WG.Queues.BaseCoherenceCompletion
import Leanux.Proofs.WG.Queues.HandshakeReceiveSlots

/-! Session construction and the original handshake receiver retain the base
list and public-key table. Acquisitions, authentication failure payments, normal
missing-peer returns, allocation refusal and source Stops keep their domains. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

/-- Session allocation/rotation affects neither structural field. No configured,
owner-bound or slot-invariant premise is needed for this narrow frame. -/
theorem beginSession_view (pid : PeerId) : SameView view (beginSession pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.list_configured)
    ((SessionCarrier.beginSession_view pid).of_factor (fun s => s.2.2.1) slots (fun _ => rfl))
    (ConfiguredMaintenance.beginSession_view pid)

theorem consumeInitiation_view (msg : List UInt8) : SameView view (consumeInitiation msg) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head pubkeyLookup; exact (pubkeyLookup_view _).wp (fun s => s=initial))
    | receive_crypto (fun w => view w=initial)
    | (rx_retention_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | base_rx_step initial

theorem consumeResponse_view (msg : List UInt8) : SameView view (consumeResponse msg) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact (indexLookup_view _ _).wp (fun s => s=initial))
    | receive_crypto (fun w => view w=initial)
    | base_rx_step initial

private theorem createResponse_structure (pid : PeerId) : SameView view (createResponse pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.combined_frame)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.create_frame) pid)
    (ConfiguredReceive.createResponse_view pid)

private theorem mac_structure (pid : PeerId) (msg : List UInt8) : SameView view (addMacToPacket pid msg) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.combined_frame)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.addMacToPacket_frame) pid msg)
    (ConfiguredHandshake.addMacToPacket_view pid msg)

private theorem send_structure (pid : PeerId) (msg : List UInt8) : SameView view (sendBufferToPeer pid msg) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.combined_frame)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.sendBufferToPeer_frame) pid msg)
    (ConfiguredHandshake.sendBufferToPeer_view pid msg)

private theorem derived_structure (pid : PeerId) : SameView view (timersSessionDerived pid) :=
  (modTimer_view .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).map (fun _ => ())

theorem sendHandshakeResponse_view (pid : PeerId) : SameView view (sendHandshakeResponse pid) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold sendHandshakeResponse timersAnyAuthenticatedPacketSent
  simp (config := {zeta := false}) only [hiddenClock64,branch,invariant]
  repeat' first
    | (rx_retention_head createResponse; exact (createResponse_structure _).wp (fun s => s=initial))
    | (rx_retention_head addMacToPacket; exact (mac_structure _ _).wp (fun s => s=initial))
    | (rx_retention_head beginSession; exact (beginSession_view _).wp (fun s => s=initial))
    | (rx_retention_head timersSessionDerived; exact (derived_structure _).wp (fun s => s=initial))
    | (rx_retention_head timersTraversal; exact (traversal_view _).wp (fun s => s=initial))
    | (rx_retention_head delTimer; exact (delTimer_view _ _).wp (fun s => s=initial))
    | (rx_retention_head sendBufferToPeer; exact (send_structure _ _).wp (fun s => s=initial))
    | base_rx_step initial

theorem cookieConsume_view (msg : List UInt8) : SameView view (cookieMessageConsume msg) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [hiddenClock64,branch,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact (indexLookup_view _ _).wp (fun s => s=initial))
    | base_rx_step initial

private theorem cookie_structure {α : Type} {action : WG.M α}
    (same : SameCookie action) : SameView view action := by
  apply same.of_factor (fun k : WGOwnedView => view {dev:=k.dev})
  intro w
  simp only [view,slots,rows,cookieView,cookieDevice,wgOwnedView,wgStoreView,
    Option.map_map,Function.comp_def]

private theorem reply4_structure (e : Endpoint) (bytes : List UInt8) :
    SameView view (send4 e none bytes 0 false) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.combined_frame)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send4_frame) e none bytes 0 false)
    (ConfiguredHandshake.send4_view e none bytes 0 false)

private theorem reply6_structure (e : Endpoint) (bytes : List UInt8) :
    SameView view (send6 e none bytes 0 false) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.combined_frame)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send6_frame) e none bytes 0 false)
    (ConfiguredHandshake.send6_view e none bytes 0 false)

private theorem cookieReply_structure (msg : List UInt8) (src : SkbSource) :
    SameView view (sendHandshakeCookie msg src) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold sendHandshakeCookie sendBufferAsReplyToSkb
  simp (config := {zeta := false}) only [branch,invariant,hiddenAlloc]
  repeat' first
    | (rx_retention_head cookieMessageCreate; exact (cookie_structure (cookieMessageCreate_sameCookie _ _ _)).wp (fun s => s=initial))
    | (rx_retention_head endpointFromSkb; exact (store_view (endpointFromSkb_sameWGStore _)).wp (fun s => s=initial))
    | (rx_retention_head send4; exact (reply4_structure _ _).wp (fun s => s=initial))
    | (rx_retention_head send6; exact (reply6_structure _ _).wp (fun s => s=initial))
    | base_rx_step initial

private theorem endpointFromSkb_structure (pid : PeerId) (src : SkbSource) :
    SameView view (setPeerEndpointFromSkb pid src) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact (store_view (endpointFromSkb_sameWGStore _)).wp (fun s => s=initial))
    | (rx_retention_head setPeerEndpoint; exact (endpoint_view _ _).wp (fun s => s=initial))
    | base_rx_step initial

private theorem afterMac_structure (msg : List UInt8) (src : SkbSource) (loaded : Bool) (state : MacState) :
    SameView view (Cookies.afterMac msg src loaded state) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold Cookies.afterMac timersAnyAuthenticatedPacketReceived
  simp (config := {zeta := false}) only [branch,invariant,WG.andM,WG.orM]
  repeat' first
    | (rx_retention_head consumeInitiation; exact (consumeInitiation_view _).wp (fun s => s=initial))
    | (rx_retention_head consumeResponse; exact (consumeResponse_view _).wp (fun s => s=initial))
    | (rx_retention_head sendHandshakeResponse; exact (sendHandshakeResponse_view _).wp (fun s => s=initial))
    | (rx_retention_head beginSession; exact (beginSession_view _).wp (fun s => s=initial))
    | (rx_retention_head sendHandshakeCookie; exact (cookieReply_structure _ _).wp (fun s => s=initial))
    | (rx_retention_head setPeerEndpointFromSkb; exact (endpointFromSkb_structure _ _).wp (fun s => s=initial))
    | (rx_retention_head timersSessionDerived; exact (derived_structure _).wp (fun s => s=initial))
    | (rx_retention_head timersHandshakeComplete; exact (handshakeComplete_view _ _).wp (fun s => s=initial))
    | (rx_retention_head sendKeepalive; exact (keepalive_view _).wp (fun s => s=initial))
    | (rx_retention_head delTimer; exact (delTimer_view _ _).wp (fun s => s=initial))
    | (rx_retention_head timersTraversal; exact (traversal_view _).wp (fun s => s=initial))
    | base_rx_step initial

/-- Normal missing-acquisition paths return before the selected-peer payment;
actual successful and failed authentication paths all retain this view. -/
theorem receiveHandshakePacket_view (msg : List UInt8) (src : SkbSource) :
    SameView view (receiveHandshakePacket msg src) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  rw [Cookies.receive_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head cookieMessageConsume; exact (cookieConsume_view _).wp (fun s => s=initial))
    | (rx_retention_head Cookies.loadPhase; exact (store_view Cookies.loadPhase_sameStore).wp (fun s => s=initial))
    | (rx_retention_head cookieValidatePacket; exact (cookie_structure (cookieValidatePacket_sameCookie _ _ _)).wp (fun s => s=initial))
    | (rx_retention_head Cookies.afterMac; exact (afterMac_structure _ _ _ _).wp (fun s => s=initial))
    | base_rx_step initial

theorem receiveStep_view : SameView view WG.receiveStep := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold WG.receiveStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head receiveHandshakePacket; exact (receiveHandshakePacket_view _ _).wp (fun s => s=initial))
    | base_rx_step initial

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
