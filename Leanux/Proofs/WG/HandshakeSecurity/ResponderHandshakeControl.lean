import Leanux.Proofs.WG.HandshakeSecurity.ResponderControlFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.HandshakeControl
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits

/-- The source's session cut needs C1's actual configured and slot facts. The
existential material history belongs only to the native endpoint carrier. -/
def Inv (confirmed : List Nat) (w : WGWorld) : Prop :=
  Authorized confirmed w ∧ HandshakeEntry.Entry w

theorem combine {a : WG.M α} (entry : Preserves HandshakeEntry.Entry a)
    (authorization : Hoare a (Inv confirmed) (fun _ => Authorized confirmed)) :
    Preserves (Inv confirmed) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w amb result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp authorization w amb result v b before run,
    (hoare_iff_run_ambient _ _ _).mp entry w amb result v b before.2 run⟩

theorem authorized {a : WG.M α} (entry : Preserves HandshakeEntry.Entry a)
    (frame : Preserves (Authorized confirmed) a) : Preserves (Inv confirmed) a :=
  combine entry (hoare_consequence frame (fun _ h => h.1) (fun _ _ h => h))

theorem native {a : WG.M α} (entry : Preserves HandshakeEntry.Entry a)
    (frame : Preserves (History.Native confirmed) a) : Preserves (Inv confirmed) a :=
  combine entry (hoare_consequence frame (fun _ h => ⟨h.1, h.2.2⟩) (fun _ _ h => h.1))

theorem store {a : WG.M α} (frame : SameWGStore a) : Preserves (Inv confirmed) a :=
  native ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.store) a frame)
    (native_store frame confirmed)

theorem send {a : WG.M α} (entry : Preserves HandshakeEntry.Entry a)
    (frame : SameView sendView a) : Preserves (Inv confirmed) a :=
  authorized entry (sendView_authorized frame confirmed)

theorem session (H1 : H1ResponderCurrentEdges) (pid : PeerId) :
    Preserves (Inv confirmed) (beginSession pid) := by
  apply combine (HandshakeReceiveSlots.session pid)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w amb result v b before run
  exact session_authorized H1 pid confirmed w v amb b result before.1 before.2.2 run

theorem cookie {a : WG.M α} (frame : SameCookie a) : Preserves (Inv confirmed) a :=
  native ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.cookie) a frame)
    (cookie_native frame confirmed)

theorem modifyPeer (pid : PeerId) (f : Peer → Peer)
    (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (slots : ∀ p, Affiliation.peerCell (f p) = Affiliation.peerCell p)
    (same : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p) :
    Preserves (Inv confirmed) (getPeer pid >>= fun p => setPeer pid (f p)) :=
  native ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.update) pid f configured slots)
    (peerUpdate_native pid f same confirmed)

theorem modifyPeer_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (slots : ∀ p, Affiliation.peerCell (f p) = Affiliation.peerCell p)
    (same : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p)
    (next : ∀ x, Preserves (Inv confirmed) (tail x)) :
    Preserves (Inv confirmed) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (modifyPeer pid f configured slots same) next

theorem modifyDevice (f : Device → Device)
    (configured : ∀ d, ConfiguredIdentity.state (f d) = ConfiguredIdentity.state d)
    (material : ∀ d, ((f d).ifindex, (f d).keypairs) = (d.ifindex, d.keypairs))
    (peer : ∀ d, (f d).nextPeer = d.nextPeer)
    (key : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (keys : ∀ d, (f d).keypairs = d.keypairs)
    (rx : ∀ d, (f d).rxSkbs = d.rxSkbs)
    (peers : ∀ d, (f d).peers = d.peers) : Preserves (Inv confirmed) (modifyDev f) :=
  native ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.modifyDevice) f configured material peer key keys rx peers)
    (modify_native f key peers keys confirmed)

theorem create (pid : PeerId) : Preserves (Inv confirmed) (createResponse pid) :=
  native (HandshakeSendResponse.create_entry pid) (createResponse_native pid confirmed)

theorem initiation (msg : List UInt8) : Preserves (Inv confirmed) (consumeInitiation msg) :=
  native (HandshakeEntry.initiation msg) (initiation_native msg confirmed)

theorem response (msg : List UInt8) : Preserves (Inv confirmed) (consumeResponse msg) :=
  native (HandshakeEntry.response msg) (response_native msg confirmed)

theorem consumeCookie (msg : List UInt8) : Preserves (Inv confirmed) (cookieMessageConsume msg) :=
  native (HandshakeEntry.cookie msg) (cookieConsume_native msg confirmed)

theorem endpoint (pid : PeerId) (src : SkbSource) : Preserves (Inv confirmed) (setPeerEndpointFromSkb pid src) :=
  native (HandshakeEntry.endpoint pid src) (endpoint_native pid src confirmed)

theorem pay (peer : Option PeerId) : Preserves (Inv confirmed) (peerPut peer) :=
  native ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.pay) peer)
    (peerPut_native peer confirmed)

theorem mac (pid : PeerId) (bytes : List UInt8) : Preserves (Inv confirmed) (addMacToPacket pid bytes) :=
  send (HandshakeSendResponse.mac_entry pid bytes)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.addMacToPacket_view) pid bytes)

theorem sendBuffer (pid : PeerId) (bytes : List UInt8) : Preserves (Inv confirmed) (sendBufferToPeer pid bytes) :=
  send ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.send) pid bytes)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.sendBufferToPeer_view) pid bytes)

theorem traversal (pid : PeerId) : Preserves (Inv confirmed) (timersTraversal pid) :=
  send ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.traversal) pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.timersTraversal_view) pid)

theorem sent (pid : PeerId) : Preserves (Inv confirmed) (timersAnyAuthenticatedPacketSent pid) :=
  send ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.sent) pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.timersAnyAuthenticatedPacketSent_view) pid)

theorem derived (pid : PeerId) : Preserves (Inv confirmed) (timersSessionDerived pid) := by
  apply send ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.derived) pid)
  unfold timersSessionDerived
  apply SameView.map
  exact (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.modPeerTimer_view) _ _ _ _

theorem received (pid : PeerId) : Preserves (Inv confirmed) (timersAnyAuthenticatedPacketReceived pid) :=
  send ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.received) pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.delTimer_view) pid .newHandshake)

theorem complete (pid : PeerId) (site : HiddenSite) : Preserves (Inv confirmed) (timersHandshakeComplete pid site) :=
  authorized ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.complete) pid site)
    (authorization_of_frames (pool_of_material (Origins.Retaining.timersHandshakeComplete_material pid site))
      (control_keyEffects (project := id) (allowed := NoPromotion) (timersHandshakeComplete_control pid site)) confirmed)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.HandshakeControl
