import Leanux.Proofs.WG.Noise.PendingInvariantFrames
import Leanux.Proofs.WG.Origins.ConfiguredReceive
import Leanux.Proofs.WG.Origins.CurrentTraffic
import Leanux.Proofs.WG.Queues.HandshakeSlots

import Leanux.Proofs.WG.Noise.PendingTicketHandshakeFrames
import Leanux.Proofs.WG.Noise.PendingTicketTimerFrames
import Leanux.Proofs.WG.Noise.PendingTicketStagingFrames
import Leanux.Proofs.WG.Origins.ConfiguredTraffic
import Leanux.Proofs.WG.Queues.HandshakeReceiveSlots

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingReception
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues ConfiguredReceive
set_option pp.structureInstances false

theorem configured_of_view {α : Type} (a : WG.M α)
    (same : SameView ConfiguredIdentity.view a) :
    Preserves ConfiguredIdentity.Inv a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result final after hi run
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp same w ambient result final after run
  intro s hs
  exact hi s (frame.symm.trans hs)

theorem configured_update (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p) :
    Preserves ConfiguredIdentity.Inv (getPeer pid >>= fun p => setPeer pid (f p)) :=
  configured_of_view _ (ConfiguredIdentity.modifyPeer_view pid f same)

theorem configured_update_bind {α : Type} (pid : PeerId) (f : Peer → Peer)
    (tail : Unit → WG.M α)
    (same : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (rest : ∀ u, Preserves ConfiguredIdentity.Inv (tail u)) :
    Preserves ConfiguredIdentity.Inv (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (configured_update pid f same) rest

private theorem configured_ite {α : Type} (c : Prop) [Decidable c]
    (a b : WG.M α) (P : WGWorld → Prop)
    (ha : Preserves P a) (hb : Preserves P b) : Preserves P (if c then a else b) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite) c a b P ha hb

macro "pending_configured_step" : tactic => `(tactic| first
  | (receive_update_head setPeer; apply configured_update; intro p; rfl)
  | (receive_update_head Bind.bind
     apply configured_update_bind
     · intro p; rfl
     intro u)
  | (rx_retention_head getPeer
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w ambient p v after hi hr
     rw [(Peers.getPeer_current _ w v p ambient after hr).1]
     exact hi)
  | (rx_retention_head getDev; unfold getDev)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ ConfiguredIdentity.Inv)
  | (rx_retention_head get; exact hoare_consequence (hoare_get ConfiguredIdentity.Inv)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head MonadStateOf.get; exact hoare_consequence (hoare_get ConfiguredIdentity.Inv)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) ConfiguredIdentity.Inv)
  | (rx_retention_head ite; apply configured_ite)
  | rx_retention_step)

/-- Configured-only variant of ConfiguredReceive.consumeInitiation_preserves. -/
theorem consumeInitiation_preserves_configured_variant (msg : List UInt8) :
    Preserves ConfiguredIdentity.Inv (consumeInitiation msg) := by
  unfold consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head pubkeyLookup
       exact configured_of_view _ (ConfiguredReceive.pubkeyLookup_view _))
    | (rx_retention_head peerPut; exact ConfiguredIdentity.peerPut_preserves _)
    | receive_crypto ConfiguredIdentity.Inv
    | pending_configured_step

/-- Configured-only variant of ConfiguredReceive.consumeResponse_preserves. -/
theorem consumeResponse_preserves_configured_variant (msg : List UInt8) :
    Preserves ConfiguredIdentity.Inv (consumeResponse msg) := by
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact ConfiguredIdentity.indexLookup_preserves _ _)
    | (rx_retention_head peerPut; exact ConfiguredIdentity.peerPut_preserves _)
    | receive_crypto ConfiguredIdentity.Inv
    | pending_configured_step

/-- Configured-only variant of CurrentTraffic.cookieMessageConsume_preserves. -/
theorem cookieMessageConsume_preserves_configured_variant (msg : List UInt8) :
    Preserves ConfiguredIdentity.Inv (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact ConfiguredIdentity.indexLookup_preserves _ _)
    | (rx_retention_head peerPut; exact ConfiguredIdentity.peerPut_preserves _)
    | pending_configured_step


/-- Projection of the already owned owner-lookup transport, not a new lookup proof. -/
theorem indexLookup_pending_frame (kinds : List IndexKind) (index : Nat) :
    SameView PendingTickets.view (indexLookup kinds index) := by
  apply PendingTickets.frame_from_fresh
  · intro tracked entry w ambient result final after hi run
    exact (indexLookup_spec_freshTransport_variant tracked kinds index entry
      w ambient result final after hi run).1
  · exact Keypairs.WGFrames.indexLookup_sameSnapshot kinds index

theorem cookieMessageConsume_pending (msg : List UInt8) :
    PendingTickets.RetainsCall (cookieMessageConsume msg) := by
  intro initial
  suffices preserved : Preserves (fun w => Retained initial (PendingTickets.view w))
      (cookieMessageConsume msg) by
    apply hoare_consequence preserved
    · intro w equal
      rw [equal]
      exact Retained.refl _
    · exact fun _ _ h => h
  let P := Retained initial
  have update (pid : PeerId) (f : Peer → Peer)
      (same : ∀p, (f p).keypairNext = p.keypairNext) :
      Preserves (fun w => P (PendingTickets.view w)) (getPeer pid >>= fun p => setPeer pid (f p)) :=
    (PendingTickets.modifyPeer_spec_pending_variant pid f same).wp P
  have updateThen (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M Unit)
      (same : ∀p, (f p).keypairNext = p.keypairNext)
      (rest : ∀u, Preserves (fun w => P (PendingTickets.view w)) (tail u)) :
      Preserves (fun w => P (PendingTickets.view w)) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
    simpa only [bind_assoc] using preserves_bind (update pid f same) rest
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (receive_update_head setPeer; apply update; intro p; rfl)
    | (receive_update_head Bind.bind
       apply updateThen
       · intro p; rfl
       intro u)
    | (rx_retention_head indexLookup; exact (indexLookup_pending_frame _ _).wp P)
    | (rx_retention_head peerPut
       exact (PendingTickets.peerPut_retained _).wp P (fun _ _ later earlier => earlier.trans later))
    | (rx_retention_head getPeer
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w ambient p v after hi run
       exact (getPeer_normal _ w v p ambient after run).1 ▸ hi)
    | (rx_retention_head getDev; exact (PendingTickets.frame_store getDev_sameWGStore).wp P)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem native_preserves {α : Type} (action : WG.M α)
    (configured : Preserves ConfiguredIdentity.Inv action)
    (slots : Preserves CurrentSlots.Inv action)
    (pending : PendingTickets.RetainsCall action) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  apply PendingSession.native_retained action ?_ pending seen
  intro w ambient result final after hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp configured w ambient result final after hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp slots w ambient result final after hi.2 run⟩

theorem native_view {α : Type} (action : WG.M α)
    (configured : SameView ConfiguredIdentity.view action)
    (slots : Preserves CurrentSlots.Inv action)
    (pending : SameView PendingTickets.view action) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) action :=
  native_preserves action (configured_of_view action configured) slots
    (PendingTickets.retained_of_frame pending) seen

theorem native_cookie {α : Type} (action : WG.M α)
    (frame : SameCookie action) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) action := by
  apply native_view action ?_ ?_ (PendingTickets.frame_cookie action frame) seen
  · apply frame.of_factor (fun s : WGOwnedView => s.dev.map ConfiguredIdentity.state)
      ConfiguredIdentity.view
    intro w
    simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,ConfiguredIdentity.view,
      ConfiguredIdentity.state,Option.map_map,Function.comp_def]
    rfl
  · apply CurrentSlots.fields_preserves (project := id)
    apply frame.of_factor (fun k : WGOwnedView => CurrentSlots.fields {dev := k.dev})
    intro w
    unfold CurrentSlots.fields RxCredits.keyWords
    simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,
      Option.map_map,Option.bind_map,Function.comp_def]
    rfl

theorem native_store {α : Type} (action : WG.M α)
    (frame : SameWGStore action) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) action :=
  native_view action (ConfiguredIdentity.sameWG (project := id) frame)
    (CurrentSlots.store_preserves frame) (PendingTickets.frame_store frame) seen

theorem native_update (pid : PeerId) (f : Peer → Peer)
    (configured : ∀p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (slots : ∀p, Affiliation.peerCell (f p) = Affiliation.peerCell p)
    (next : ∀p, (f p).keypairNext = p.keypairNext) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (getPeer pid >>= fun p => setPeer pid (f p)) :=
  native_view _ (ConfiguredIdentity.modifyPeer_view pid f configured)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.update_peer) pid f slots)
    (PendingTickets.modifyPeer_spec_pending_variant pid f next) seen

theorem native_update_bind {α : Type} (pid : PeerId) (f : Peer → Peer)
    (tail : Unit → WG.M α)
    (configured : ∀p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (slots : ∀p, Affiliation.peerCell (f p) = Affiliation.peerCell p)
    (next : ∀p, (f p).keypairNext = p.keypairNext) (seen : List Nat)
    (rest : ∀u, Preserves (fun w => PendingSession.NativeInv w seen) (tail u)) :
    Preserves (fun w => PendingSession.NativeInv w seen)
      (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (native_update pid f configured slots next seen) rest

theorem native_modifyDevice (f : Device → Device)
    (configured : ∀d, ConfiguredIdentity.state (f d) = ConfiguredIdentity.state d)
    (front : ∀d, (f d).nextKeypairId = d.nextKeypairId)
    (peers : ∀d, (f d).peers = d.peers)
    (keys : ∀d, (f d).keypairs = d.keypairs) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (modifyDev f) := by
  apply native_view _ ?_ ?_ (PendingTickets.modifyDev_frame f peers keys) seen
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient result final after run
    cases run
    simp [ConfiguredIdentity.view,Option.map_map,Function.comp_def,configured]
  · apply CurrentSlots.fields_preserves (project := id)
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotFrames.«0».Leanux.Proofs.WG.CurrentSlots.fields_modify)
      f front peers keys

theorem initiation (msg : List UInt8) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (consumeInitiation msg) :=
  native_preserves _ (consumeInitiation_preserves_configured_variant msg)
    (HandshakeSlots.consumeInitiation msg)
    (PendingTickets.retained_of_frame (PendingTickets.consumeInitiation_frame msg)) seen

theorem response (msg : List UInt8) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (consumeResponse msg) :=
  native_preserves _ (consumeResponse_preserves_configured_variant msg)
    (HandshakeSlots.consumeResponse msg)
    (PendingTickets.retained_of_frame (PendingTickets.consumeResponse_frame msg)) seen

theorem cookieConsume (msg : List UInt8) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (cookieMessageConsume msg) :=
  native_preserves _ (cookieMessageConsume_preserves_configured_variant msg)
    (HandshakeSlots.cookieMessageConsume msg) (cookieMessageConsume_pending msg) seen

theorem create (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (createResponse pid) :=
  native_view _ (ConfiguredReceive.createResponse_view pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.create_slots) pid)
    (PendingTickets.createResponse_frame pid) seen

theorem mac (pid : PeerId) (msg : List UInt8) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (addMacToPacket pid msg) :=
  native_view _ (ConfiguredHandshake.addMacToPacket_view pid msg)
    (CurrentSlots.fields_preserves (project := id) (CurrentSlots.Removal.addMac_fields pid msg))
    (PendingTickets.addMacToPacket_frame pid msg) seen

theorem send (pid : PeerId) (msg : List UInt8) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (sendBufferToPeer pid msg) :=
  native_view _ (ConfiguredHandshake.sendBufferToPeer_view pid msg)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.send_slots) pid msg)
    (PendingTickets.sendBufferToPeer_frame pid msg) seen

theorem traversal (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (timersTraversal pid) :=
  native_view _ (ConfiguredIdentity.timersTraversal_view pid)
    (CurrentSlots.timersTraversal_preserves pid)
    (PendingTickets.timersTraversal_frame pid) seen

theorem sent (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (timersAnyAuthenticatedPacketSent pid) :=
  native_view _ (ConfiguredIdentity.timersAnyAuthenticatedPacketSent_view pid)
    (CurrentSlots.delTimer_preserves pid .sendKeepalive)
    (PendingTickets.timersAnyAuthenticatedPacketSent_frame pid) seen

theorem derived (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (timersSessionDerived pid) := by
  apply native_view _ (ConfiguredReceiveLeaves.timersSessionDerived_view pid) ?_
    (PendingTickets.timersSessionDerived_frame pid) seen
  unfold timersSessionDerived
  apply discard_view_spec id CurrentSlots.Inv
  exact CurrentSlots.modPeerTimer_preserves _ _ _ _

theorem complete (pid : PeerId) (site : HiddenSite) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (timersHandshakeComplete pid site) :=
  native_view _ (ConfiguredReceiveLeaves.timersHandshakeComplete_view pid site)
    (CurrentSlots.timersHandshakeComplete_preserves pid site)
    (PendingTickets.timersHandshakeComplete_frame pid site) seen

theorem received (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (timersAnyAuthenticatedPacketReceived pid) :=
  native_view _ (ConfiguredReceiveLeaves.timersAnyAuthenticatedPacketReceived_view pid)
    (CurrentSlots.delTimer_preserves pid .newHandshake)
    (PendingTickets.timersAnyAuthenticatedPacketReceived_frame pid) seen

theorem pay (peer : Option PeerId) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (peerPut peer) :=
  native_preserves _ (ConfiguredIdentity.peerPut_preserves peer)
    (CurrentSlots.peerPut_preserves peer) (PendingTickets.peerPut_retained peer) seen

theorem endpoint (pid : PeerId) (src : SkbSource) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (setPeerEndpointFromSkb pid src) :=
  native_view _ (ConfiguredReceiveLeaves.setPeerEndpointFromSkb_view pid src)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.endpoint_slots) pid src)
    (PendingTickets.setPeerEndpointFromSkb_frame pid src) seen

theorem sendCookie (msg : List UInt8) (src : SkbSource) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (sendHandshakeCookie msg src) := by
  unfold sendHandshakeCookie
  apply preserves_bind (native_cookie _ (cookieMessageCreate_sameCookie _ _ _) seen)
  intro bytes
  exact native_view _ (ConfiguredReceiveLeaves.sendBufferAsReplyToSkb_view src bytes)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.reply_slots) src bytes)
    (PendingTickets.sendBufferAsReplyToSkb_frame src bytes) seen

theorem keepalive (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (sendKeepalive pid) :=
  native_preserves _ (ConfiguredTraffic.keepalive pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.keepalive_slots) pid)
    (PendingTickets.sendKeepalive_retained pid) seen


open Origins.HandshakeSources in
macro "pending_native_step " seen:term : tactic => `(tactic| first
  | (receive_update_head setPeer
     apply native_update _ _ ?_ ?_ ?_ $seen
     all_goals intro p; rfl)
  | (receive_update_head Bind.bind
     apply native_update_bind _ _ _ ?_ ?_ ?_ $seen
     · intro p; rfl
     · intro p; rfl
     · intro p; rfl
     intro u)
  | (rx_retention_head getPeer
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w ambient p v after hi run
     exact (getPeer_normal _ w v p ambient after run).1 ▸ hi)
  | (rx_retention_head getDev; exact native_store _ getDev_sameWGStore $seen)
  | (rx_retention_head modifyDev
     apply native_modifyDevice _ ?_ ?_ ?_ ?_ $seen
     all_goals intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ite; apply configured_ite)
  | rx_retention_step)

end Leanux.Proofs.WG.Noise.PendingReception
