import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverWorkers

set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits Origins Origins.Retaining ConfiguredTraffic ConfiguredReceive

theorem carrier_update_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (slots : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p)
    (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (confirmed : List Nat) (next : ∀ x, Framing.Preserves (Carrier confirmed) (tail x)) :
    Framing.Preserves (Carrier confirmed) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (carrier_update pid f slots configured confirmed) next

private theorem carrier_conditional (confirmed : List Nat) (c : Prop) [Decidable c]
    (a b : WG.M α) (ha : Framing.Preserves (Carrier confirmed) a)
    (hb : Framing.Preserves (Carrier confirmed) b) :
    Framing.Preserves (Carrier confirmed) (if c then a else b) := by
  by_cases hc : c <;> simp only [hc,↓reduceIte] <;> assumption

macro "responder_carrier_handshake_step " confirmed:term : tactic => `(tactic| first
  | (receive_update_head Bind.bind
     apply carrier_update_bind
     · intro p; rfl
     · intro p; rfl
     intro x)
  | (rx_retention_head pubkeyLookup
     exact carrier_frame $confirmed (ConfiguredReceive.pubkeyLookup_view _) (pubkey_native _ $confirmed))
  | (rx_retention_head indexLookup
     exact carrier_join $confirmed (ConfiguredIdentity.indexLookup_preserves _ _) (indexLookup_native _ _ $confirmed))
  | (rx_retention_head getDev; exact carrier_store getDev_sameWGStore $confirmed)
  | (rx_retention_head ite; apply carrier_conditional $confirmed)
  | receive_crypto (Carrier $confirmed)
  | responder_carrier_poll_step $confirmed)

theorem carrier_initiation (msg : List UInt8) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (consumeInitiation msg) := by
  unfold consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | responder_carrier_handshake_step confirmed
    | split

theorem carrier_response (msg : List UInt8) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (consumeResponse msg) := by
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | responder_carrier_handshake_step confirmed
    | split

theorem carrier_cookie_consume (msg : List UInt8) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | responder_carrier_handshake_step confirmed
    | split

theorem carrier_cookie {action : WG.M α} (frame : Cookies.NoNoiseChange action) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) action := by
  apply carrier_frame confirmed
  · apply frame.of_factor (fun s => ConfiguredIdentity.view {dev := s.1})
    intro w
    simp only [Cookies.noiseView,Cookies.viewOfStore,wgStoreView,ConfiguredIdentity.view,
      Option.map_map,Function.comp_def]
    rfl
  · apply native_fields
    · apply frame.of_factor (fun s => pool {dev := s.1})
      intro w
      funext kid
      change (w.dev.bind fun d => d.keypairs[kid]?).map keyCore =
        ((w.dev.map Cookies.scrub).bind fun d => d.keypairs[kid]?).map keyCore
      simp only [Option.bind_map]
      rfl
    · apply frame.of_factor (fun s => CurrentSlots.fields {dev := s.1})
      intro w
      unfold CurrentSlots.fields
      simp only [Cookies.noiseView,Cookies.viewOfStore,wgStoreView,
        Option.map_map,Option.bind_map,Function.comp_def]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      funext kid
      change (w.dev.bind fun d => d.keypairs[kid]?).map (·.peer) =
        ((w.dev.map Cookies.scrub).bind fun d => d.keypairs[kid]?).map (·.peer)
      simp only [Option.bind_map]
      rfl

theorem carrier_create_response (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (createResponse pid) :=
  carrier_frame confirmed (ConfiguredReceive.createResponse_view pid) (createResponse_native pid confirmed)

theorem carrier_mac (pid : PeerId) (msg : List UInt8) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (addMacToPacket pid msg) :=
  carrier_frame confirmed (ConfiguredHandshake.addMacToPacket_view pid msg)
    (sendView_native
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.addMacToPacket_view) pid msg)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.mac_slots) pid msg) confirmed)

theorem carrier_send_buffer (pid : PeerId) (msg : List UInt8) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (sendBufferToPeer pid msg) := by
  apply carrier_frame confirmed (ConfiguredHandshake.sendBufferToPeer_view pid msg)
  apply sendView_native
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.sendBufferToPeer_view) pid msg)
    _ confirmed
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head send4; exact CurrentSlots.TxSource.send4_preserves _ _ _ _ _)
    | (rx_retention_head send6; exact CurrentSlots.TxSource.send6_preserves _ _ _ _ _)
    | slot_traffic_step

theorem carrier_derived (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (timersSessionDerived pid) := by
  apply carrier_frame confirmed (ConfiguredReceiveLeaves.timersSessionDerived_view pid)
  unfold timersSessionDerived
  exact discard_view_spec id (History.Native confirmed) _ (modTimer_native _ _ _ _ confirmed)

theorem carrier_traversal (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (timersTraversal pid) :=
  carrier_frame confirmed (ConfiguredIdentity.timersTraversal_view pid)
    (sendView_native
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.timersTraversal_view) pid)
      (CurrentSlots.timersTraversal_preserves pid) confirmed)

theorem carrier_sent (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (timersAnyAuthenticatedPacketSent pid) :=
  carrier_frame confirmed (ConfiguredIdentity.timersAnyAuthenticatedPacketSent_view pid)
    (delTimer_native pid .sendKeepalive confirmed)

theorem carrier_received (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (timersAnyAuthenticatedPacketReceived pid) :=
  carrier_frame confirmed (ConfiguredReceiveLeaves.timersAnyAuthenticatedPacketReceived_view pid)
    (delTimer_native pid .newHandshake confirmed)

theorem carrier_endpoint_skb (pid : PeerId) (src : SkbSource) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (setPeerEndpointFromSkb pid src) :=
  carrier_frame confirmed (ConfiguredReceiveLeaves.setPeerEndpointFromSkb_view pid src)
    (endpoint_native pid src confirmed)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
