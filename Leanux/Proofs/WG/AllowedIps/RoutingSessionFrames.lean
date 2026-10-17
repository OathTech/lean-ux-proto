import Leanux.Proofs.WG.AllowedIps.RoutingHandshakeFrames

/-! Normal-endpoint routing equality for original session creation and response
sending. Keypair/index updates are outside the routing view; peer writes retain
the allowed-IP list obtained from their actual getter. No affiliation or
resident-owner premise is imposed. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem keypairCreate_routing (pid : Option PeerId) : SameView routingView (keypairCreate pid) := by
  routing_handshake_source [keypairCreate] using [setKeypair_routing, modifyDev_routing]
  all_goals rfl

theorem addNewKeypair_routing (pid : PeerId) (kp : KeypairId) :
    SameView routingView (addNewKeypair pid kp) := by
  routing_handshake_source [addNewKeypair,
    _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer] using [keypairPut_routing]

theorem deriveKeys_routing (kp : KeypairId) (initiator : Bool) (ck : List UInt8) :
    SameView routingView (deriveKeys kp initiator ck) := by
  have kdf := fun b c ck data => show SameView routingView _ from
    (Framing.kdf_sameWGWorld b c ck data).factor routingView
  have out := fun xs i => show SameView routingView _ from
    (Framing.kdfOut_sameWGWorld xs i).factor routingView
  routing_handshake_source [deriveKeys] using [kdf, out, setKeypair_routing]

theorem beginSession_routing (pid : PeerId) : SameView routingView (beginSession pid) := by
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have index {α : Type} (a : IndexM α) : Preserves P (monadLift a : WG.M α) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    simpa only [P, routingView, hd, Option.map_some, routingState] using hi
  have peer := fun pid => (getPeer_routing pid).wp (fun view => view = initial)
  have key := fun kp => (getKeypair_routing kp).wp (fun view => view = initial)
  have write := fun kp k => (setKeypair_routing kp k).wp (fun view => view = initial)
  have create := fun word => (keypairCreate_routing word).wp (fun view => view = initial)
  have derive := fun kp initiator ck => (deriveKeys_routing kp initiator ck).wp (fun view => view = initial)
  have zero := (handshakeZero_routing pid).wp (fun view => view = initial)
  have add := fun kp => (addNewKeypair_routing pid kp).wp (fun view => view = initial)
  have word := fun owner => (ownerWord_routing owner).wp (fun view => view = initial)
  have owner := fun owner => (ownerDeref_routing owner).wp (fun view => view = initial)
  change Preserves P _
  unfold beginSession
  simp only [branch, WG.andM, invariant, unsupported]
  repeat' first
    | (allocation_release_lift_from IndexM; exact index _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (rx_retention_head getPeer; exact peer _)
    | (rx_retention_head getKeypair; exact key _)
    | (rx_retention_head setKeypair; exact write _ _)
    | (rx_retention_head keypairCreate; exact create _)
    | (rx_retention_head deriveKeys; exact derive _ _ _)
    | (rx_retention_head handshakeZero; exact zero)
    | (rx_retention_head addNewKeypair; exact add _)
    | (rx_retention_head IndexOwner.peerWord; exact word _)
    | (rx_retention_head IndexOwner.peerDeref; exact owner _)
    | rx_retention_step

theorem createResponse_routing (pid : PeerId) : SameView routingView (createResponse pid) := by
  have kdf := fun b c ck data => show SameView routingView _ from
    (Framing.kdf_sameWGWorld b c ck data).factor routingView
  have out := fun xs i => show SameView routingView _ from
    (Framing.kdfOut_sameWGWorld xs i).factor routingView
  have pub := fun k => show SameView routingView _ from
    (generatePublic_sameWGWorld k).factor routingView
  have eph := fun b e ck h => show SameView routingView _ from
    (messageEphemeral_sameWGWorld b e ck h).factor routingView
  have dh := fun b ck p q => show SameView routingView _ from
    (mixDh_sameWGWorld b ck p q).factor routingView
  routing_handshake_source [createResponse,
    _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain] using [pub, eph, dh, kdf, out]

theorem timersSessionDerived_routing (pid : PeerId) : SameView routingView (timersSessionDerived pid) := by
  routing_handshake_source [timersSessionDerived, Functor.discard] using [modPeerTimer_routing]

theorem sendHandshakeResponse_routing (pid : PeerId) : SameView routingView (sendHandshakeResponse pid) := by
  routing_handshake_source [sendHandshakeResponse] using [createResponse_routing,
    addMacToPacket_routing, beginSession_routing, timersSessionDerived_routing,
    timersTraversal_routing, timersAnyAuthenticatedPacketSent_routing, sendBufferToPeer_routing]

end Leanux.Proofs.WG.AllowedIps
