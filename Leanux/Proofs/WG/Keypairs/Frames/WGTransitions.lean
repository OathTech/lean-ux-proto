import Leanux.Proofs.WG.Keypairs.Frames.WGBase

namespace Leanux.Proofs.WG.Keypairs.WGTransitions
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.KernelFrames Leanux.Proofs.WG.Keypairs.WGFrames

set_option pp.structureInstances false
set_option maxHeartbeats 800000

theorem Packet_protocol_sameSnapshot (pkt : Packet) : SameSnapshot (Leanux.WG.Packet.protocol pkt) := by
  frame_same [Leanux.WG.Packet.protocol] using []

theorem Packet_protocol_spec (P : Snapshot → Prop) (pkt : Packet) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.Packet.protocol pkt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (Packet_protocol_sameSnapshot pkt).wp P

theorem addMacToPacket_sameSnapshot (pid : PeerId) (msg : List UInt8) : SameSnapshot (Leanux.WG.addMacToPacket pid msg) := by
  frame_same [Leanux.WG.addMacToPacket] using [branchExpired_spec, getPeer_spec, setPeer_spec]

theorem addMacToPacket_spec (P : Snapshot → Prop) (pid : PeerId) (msg : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.addMacToPacket pid msg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (addMacToPacket_sameSnapshot pid msg).wp P

theorem cpumaskChooseOnline_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.cpumaskChooseOnline pid) := by
  frame_same [Leanux.WG.cpumaskChooseOnline] using [getPeer_spec, setPeer_spec]

theorem cpumaskChooseOnline_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.cpumaskChooseOnline pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (cpumaskChooseOnline_sameSnapshot pid).wp P

theorem cpumaskNextOnlineFrom_sameSnapshot (lastCpu : Int) : SameSnapshot (Leanux.WG.cpumaskNextOnlineFrom lastCpu) := by
  frame_same [Leanux.WG.cpumaskNextOnlineFrom] using []

theorem cpumaskNextOnlineFrom_spec (P : Snapshot → Prop) (lastCpu : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.cpumaskNextOnlineFrom lastCpu
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (cpumaskNextOnlineFrom_sameSnapshot lastCpu).wp P

theorem endpointFromSkb_sameSnapshot (src : SkbSource) : SameSnapshot (Leanux.WG.endpointFromSkb src) := by
  frame_same [Leanux.WG.endpointFromSkb] using []

theorem endpointFromSkb_spec (P : Snapshot → Prop) (src : SkbSource) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.endpointFromSkb src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (endpointFromSkb_sameSnapshot src).wp P

theorem expireCurrentPeerKeypairs_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.expireCurrentPeerKeypairs pid) := by
  frame_same [Leanux.WG.expireCurrentPeerKeypairs] using [getKeypair_live_spec, getPeer_spec, handshakeZero_spec, indexRemove_spec, requireNotPending_spec, resetLastSentHandshake_spec, setKeypair_live_spec]

theorem expireCurrentPeerKeypairs_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.expireCurrentPeerKeypairs pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (expireCurrentPeerKeypairs_sameSnapshot pid).wp P

theorem handshakeClear_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.handshakeClear pid) := by
  frame_same [Leanux.WG.handshakeClear] using [handshakeZero_spec, indexRemove_spec]

theorem handshakeClear_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.handshakeClear pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (handshakeClear_sameSnapshot pid).wp P

theorem ipTunnelGetDsfield_sameSnapshot (protocol : Nat) (hdr : List UInt8) : SameSnapshot (Leanux.WG.ipTunnelGetDsfield protocol hdr) := by
  frame_same [Leanux.WG.ipTunnelGetDsfield] using []

theorem ipTunnelGetDsfield_spec (P : Snapshot → Prop) (protocol : Nat) (hdr : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.ipTunnelGetDsfield protocol hdr
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ipTunnelGetDsfield_sameSnapshot protocol hdr).wp P

theorem jitterBelowRekeyTimeout_sameSnapshot (site : HiddenSite) : SameSnapshot (Leanux.WG.jitterBelowRekeyTimeout site) :=
  sameSnapshot_of_sameWGKernel (Framing.sameWGKernel_of_sameKernel (Framing.jitterBelowRekeyTimeout_sameKernel site))

theorem jitterBelowRekeyTimeout_spec (P : Snapshot → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.jitterBelowRekeyTimeout site
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (jitterBelowRekeyTimeout_sameSnapshot site).wp P

theorem kdf_sameSnapshot (second third : Bool) (chainingKey data : List UInt8) : SameSnapshot (Leanux.WG.kdf second third chainingKey data) :=
  sameSnapshot_of_sameKernel (Framing.kdf_sameKernel second third chainingKey data)

theorem kdf_spec (P : Snapshot → Prop) (second third : Bool) (chainingKey data : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.kdf second third chainingKey data
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (kdf_sameSnapshot second third chainingKey data).wp P

theorem kdfOut_sameSnapshot (outs : List (List UInt8)) (i : Nat) : SameSnapshot (Leanux.WG.kdfOut outs i) :=
  sameSnapshot_of_sameKernel (Framing.kdfOut_sameKernel outs i)

theorem kdfOut_spec (P : Snapshot → Prop) (outs : List (List UInt8)) (i : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.kdfOut outs i
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (kdfOut_sameSnapshot outs i).wp P

theorem keypairGetCurrent_sameSnapshot  : SameSnapshot (Leanux.WG.keypairGetCurrent ) := by
  frame_same [Leanux.WG.keypairGetCurrent] using []

theorem keypairGetCurrent_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.keypairGetCurrent
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (keypairGetCurrent_sameSnapshot ).wp P

theorem messageDecrypt_sameSnapshot (sealed key hash : List UInt8) : SameSnapshot (Leanux.WG.messageDecrypt sealed key hash) :=
  sameSnapshot_of_sameKernel (Framing.messageDecrypt_sameKernel sealed key hash)

theorem messageDecrypt_spec (P : Snapshot → Prop) (sealed key hash : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.messageDecrypt sealed key hash
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (messageDecrypt_sameSnapshot sealed key hash).wp P

theorem modPeerTimerGuard_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.modPeerTimerGuard pid) := by
  frame_same [Leanux.WG.modPeerTimerGuard] using [getDev_spec, getPeer_spec]

theorem modPeerTimerGuard_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.modPeerTimerGuard pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (modPeerTimerGuard_sameSnapshot pid).wp P

theorem purgeStagedPackets_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.purgeStagedPackets pid) := by
  frame_same [Leanux.WG.purgeStagedPackets] using [getPeer_spec, setPeer_spec]

theorem purgeStagedPackets_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.purgeStagedPackets pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (purgeStagedPackets_sameSnapshot pid).wp P

theorem sendBufferToPeer_sameSnapshot (pid : PeerId) (bytes : List UInt8) : SameSnapshot (Leanux.WG.sendBufferToPeer pid bytes) := by
  frame_same [Leanux.WG.sendBufferToPeer] using [getPeer_spec, hiddenAlloc_snapshot_spec, send4_spec, send6_spec, setPeer_spec]

theorem sendBufferToPeer_spec (P : Snapshot → Prop) (pid : PeerId) (bytes : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendBufferToPeer pid bytes
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendBufferToPeer_sameSnapshot pid bytes).wp P

theorem sendQueuedHandshakeInitiation_sameSnapshot (pid : PeerId) (isRetry : Bool) : SameSnapshot (Leanux.WG.sendQueuedHandshakeInitiation pid isRetry) := by
  frame_same [Leanux.WG.sendQueuedHandshakeInitiation] using [branchExpired_spec, getPeer_spec, peerGet_spec, peerPut_spec, recordQueued_spec, requireNotPending_spec, setPeer_spec]

theorem sendQueuedHandshakeInitiation_spec (P : Snapshot → Prop) (pid : PeerId) (isRetry : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendQueuedHandshakeInitiation pid isRetry
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendQueuedHandshakeInitiation_sameSnapshot pid isRetry).wp P

theorem timersAnyAuthenticatedPacketReceived_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersAnyAuthenticatedPacketReceived pid) := by
  frame_same [Leanux.WG.timersAnyAuthenticatedPacketReceived] using [delTimer_spec]

theorem timersAnyAuthenticatedPacketReceived_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersAnyAuthenticatedPacketReceived pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersAnyAuthenticatedPacketReceived_sameSnapshot pid).wp P

theorem timersAnyAuthenticatedPacketSent_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersAnyAuthenticatedPacketSent pid) := by
  frame_same [Leanux.WG.timersAnyAuthenticatedPacketSent] using [delTimer_spec]

theorem timersAnyAuthenticatedPacketSent_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersAnyAuthenticatedPacketSent pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersAnyAuthenticatedPacketSent_sameSnapshot pid).wp P

theorem timersHandshakeComplete_sameSnapshot (pid : PeerId) (site : HiddenSite := .walltimeLastHandshake) : SameSnapshot (Leanux.WG.timersHandshakeComplete pid site) := by
  frame_same [Leanux.WG.timersHandshakeComplete] using [delTimer_spec, getPeer_spec, hidden_snapshot_spec, setPeer_spec]

theorem timersHandshakeComplete_spec (P : Snapshot → Prop) (pid : PeerId) (site : HiddenSite := .walltimeLastHandshake) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersHandshakeComplete pid site
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersHandshakeComplete_sameSnapshot pid site).wp P

theorem setChain_sameSnapshot (pid : PeerId) (ck hash : List UInt8) : SameSnapshot ((pinned_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash) := by
  frame_same [_private.Leanux.WG.Handshake.«0».Leanux.WG.setChain] using [getPeer_spec, setPeer_spec]

theorem setChain_spec (P : Snapshot → Prop) (pid : PeerId) (ck hash : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (pinned_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setChain_sameSnapshot pid ck hash).wp P

theorem modifyPeer_sameSnapshot (pid : PeerId) (f : Peer → Peer) : SameSnapshot ((pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f) := by
  frame_same [_private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer] using [getPeer_spec, setPeer_spec]

theorem modifyPeer_spec (P : Snapshot → Prop) (pid : PeerId) (f : Peer → Peer) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid f
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (modifyPeer_sameSnapshot pid f).wp P

theorem addNewKeypair_ordinary (pid : PeerId) (newKeypair : KeypairId) : OrdinaryAction (Leanux.WG.addNewKeypair pid newKeypair) := by
  frame_ordinary [Leanux.WG.addNewKeypair] using [getKeypair_live_spec, getPeer_spec, modifyPeer_spec] ordinary [keypairPut_ordinary_spec]

theorem addNewKeypair_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) (newKeypair : KeypairId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.addNewKeypair pid newKeypair
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (addNewKeypair_ordinary pid newKeypair).wp P hp

theorem deriveKeys_sameSnapshot (kp : KeypairId) (initiator : Bool) (chainingKey : List UInt8) : SameSnapshot (Leanux.WG.deriveKeys kp initiator chainingKey) := by
  exact Leanux.Proofs.WG.Keypairs.deriveKeys_sameSnapshot kp initiator chainingKey

theorem deriveKeys_spec (P : Snapshot → Prop) (kp : KeypairId) (initiator : Bool) (chainingKey : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.deriveKeys kp initiator chainingKey
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (deriveKeys_sameSnapshot kp initiator chainingKey).wp P

theorem enqueuePerDeviceAndPeer_sameSnapshot (pid : PeerId) (item : List SkbId) : SameSnapshot (Leanux.WG.enqueuePerDeviceAndPeer pid item) := by
  frame_same [Leanux.WG.enqueuePerDeviceAndPeer] using [cpumaskNextOnlineFrom_spec, getDev_spec, getPeer_spec, queueDeviceWork_spec, setPeer_spec, setTxSkb_spec]

theorem enqueuePerDeviceAndPeer_spec (P : Snapshot → Prop) (pid : PeerId) (item : List SkbId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.enqueuePerDeviceAndPeer pid item
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (enqueuePerDeviceAndPeer_sameSnapshot pid item).wp P

theorem enqueuePerPeerTx_sameSnapshot (item : List SkbId) (state : PacketState) : SameSnapshot (Leanux.WG.enqueuePerPeerTx item state) := by
  frame_same [Leanux.WG.enqueuePerPeerTx] using [peekQueuedUnit_spec, cpumaskChooseOnline_spec, getDev_spec, getKeypair_live_spec, getPeer_spec, peerGet_spec, peerPut_spec, recordQueued_spec, setPeer_spec, getTxSkb_spec, setTxSkb_spec]

theorem enqueuePerPeerTx_spec (P : Snapshot → Prop) (item : List SkbId) (state : PacketState) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.enqueuePerPeerTx item state
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (enqueuePerPeerTx_sameSnapshot item state).wp P

theorem ipTunnelEcnEncap_sameSnapshot (pkt : Packet) : SameSnapshot (Leanux.WG.ipTunnelEcnEncap pkt) := by
  frame_same [Leanux.WG.ipTunnelEcnEncap] using [Packet_protocol_spec, ipTunnelGetDsfield_spec]

theorem ipTunnelEcnEncap_spec (P : Snapshot → Prop) (pkt : Packet) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.ipTunnelEcnEncap pkt
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ipTunnelEcnEncap_sameSnapshot pkt).wp P

theorem keypairsClear_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.keypairsClear pid) := by
  frame_ordinary [Leanux.WG.keypairsClear] using [getPeer_spec, modifyPeer_spec] ordinary [keypairPut_ordinary_spec]

theorem keypairsClear_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.keypairsClear pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (keypairsClear_ordinary pid).wp P hp

theorem messageEphemeral_sameSnapshot (copy : Bool) (e chainingKey hash : List UInt8) : SameSnapshot (Leanux.WG.messageEphemeral copy e chainingKey hash) :=
  sameSnapshot_of_sameKernel (Framing.messageEphemeral_sameKernel copy e chainingKey hash)

theorem messageEphemeral_spec (P : Snapshot → Prop) (copy : Bool) (e chainingKey hash : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.messageEphemeral copy e chainingKey hash
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (messageEphemeral_sameSnapshot copy e chainingKey hash).wp P

theorem mixDh_sameSnapshot (key : Bool) (chainingKey priv pub : List UInt8) : SameSnapshot (Leanux.WG.mixDh key chainingKey priv pub) :=
  sameSnapshot_of_sameKernel (Framing.mixDh_sameKernel key chainingKey priv pub)

theorem mixDh_spec (P : Snapshot → Prop) (key : Bool) (chainingKey priv pub : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.mixDh key chainingKey priv pub
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (mixDh_sameSnapshot key chainingKey priv pub).wp P

theorem mixPrecomputedDh_sameSnapshot (chainingKey precomputed : List UInt8) : SameSnapshot (Leanux.WG.mixPrecomputedDh chainingKey precomputed) :=
  sameSnapshot_of_sameKernel (Framing.mixPrecomputedDh_sameKernel chainingKey precomputed)

theorem mixPrecomputedDh_spec (P : Snapshot → Prop) (chainingKey precomputed : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.mixPrecomputedDh chainingKey precomputed
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (mixPrecomputedDh_sameSnapshot chainingKey precomputed).wp P

theorem modPeerTimer_sameSnapshot (pid : PeerId) (t : PeerTimer) (delay : Nat) : SameSnapshot (Leanux.WG.modPeerTimer pid t delay) := by
  frame_same [Leanux.WG.modPeerTimer] using [armTimer_spec, modPeerTimerGuard_spec]

theorem modPeerTimer_spec (P : Snapshot → Prop) (pid : PeerId) (t : PeerTimer) (delay : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.modPeerTimer pid t delay
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (modPeerTimer_sameSnapshot pid t delay).wp P

theorem receivedWithKeypair_ordinary (pid : PeerId) (received : KeypairId) : OrdinaryAction (Leanux.WG.receivedWithKeypair pid received) := by
  frame_ordinary [Leanux.WG.receivedWithKeypair] using [getPeer_spec, modifyPeer_spec] ordinary [keypairPut_ordinary_spec]

theorem receivedWithKeypair_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) (received : KeypairId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.receivedWithKeypair pid received
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (receivedWithKeypair_ordinary pid received).wp P hp

theorem setPeerEndpointFromSkb_sameSnapshot (pid : PeerId) (src : SkbSource) : SameSnapshot (Leanux.WG.setPeerEndpointFromSkb pid src) := by
  frame_same [Leanux.WG.setPeerEndpointFromSkb] using [endpointFromSkb_spec, setPeerEndpoint_spec]

theorem setPeerEndpointFromSkb_spec (P : Snapshot → Prop) (pid : PeerId) (src : SkbSource) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.setPeerEndpointFromSkb pid src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setPeerEndpointFromSkb_sameSnapshot pid src).wp P

theorem timersDataSent_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersDataSent pid) := by
  frame_same [Leanux.WG.timersDataSent] using [armTimer_spec, getPeer_spec, jitterBelowRekeyTimeout_spec, modPeerTimerGuard_spec]

theorem timersDataSent_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersDataSent pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersDataSent_sameSnapshot pid).wp P

theorem beginSession_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.beginSession pid) := by
  frame_ordinary [Leanux.WG.beginSession] using [deriveKeys_spec, getKeypair_live_spec, getPeer_spec, handshakeZero_spec, indexReplaceHandshake_spec, setKeypair_live_spec] ordinary [addNewKeypair_spec, keypairCreate_ordinary_spec]

theorem beginSession_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.beginSession pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (beginSession_ordinary pid).wp P hp

theorem consumeInitiation_sameSnapshot (msg : List UInt8) : SameSnapshot (Leanux.WG.consumeInitiation msg) := by
  apply sameSnapshot_of_wp
  intro initial
  have h0 := @branch_spec (fun s => s = initial)
  have h1 := @branchCmp_spec (fun s => s = initial)
  have h2 := @getDev_spec (fun s => s = initial)
  have h3 := @getPeer_spec (fun s => s = initial)
  have h4 := @hiddenClock_spec (fun s => s = initial)
  have h5 := @hiddenClock64_spec (fun s => s = initial)
  have h6 := @messageDecrypt_spec (fun s => s = initial)
  have h7 := @messageEphemeral_spec (fun s => s = initial)
  have h8 := @mixDh_spec (fun s => s = initial)
  have h9 := @mixPrecomputedDh_spec (fun s => s = initial)
  have h10 := @peerPut_spec (fun s => s = initial)
  have h11 := @pubkeyLookup_spec (fun s => s = initial)
  have h12 := @setPeer_spec (fun s => s = initial)
  mvcgen -trivial [consumeInitiation, WG.andM, WG.orM, invariant, unsupported, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  all_goals mleave
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [snapshot]
  all_goals trivial

theorem consumeInitiation_spec (P : Snapshot → Prop) (msg : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.consumeInitiation msg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (consumeInitiation_sameSnapshot msg).wp P

theorem consumeResponse_sameSnapshot (msg : List UInt8) : SameSnapshot (Leanux.WG.consumeResponse msg) := by
  frame_same [Leanux.WG.consumeResponse] using [getDev_spec, getPeer_spec, indexLookup_spec, kdfOut_spec, kdf_spec, messageDecrypt_spec, messageEphemeral_spec, mixDh_spec, peerPut_spec, setPeer_spec]

theorem consumeResponse_spec (P : Snapshot → Prop) (msg : List UInt8) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.consumeResponse msg
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (consumeResponse_sameSnapshot msg).wp P

theorem createData_ordinary (pid : PeerId) (item : List SkbId) : OrdinaryAction (Leanux.WG.createData pid item) := by
  frame_ordinary [Leanux.WG.createData] using [enqueuePerDeviceAndPeer_spec, enqueuePerPeerTx_spec, getPeer_spec, peerPut_spec, getTxSkb_spec, freeTxSkb_spec] ordinary [keypairPut_ordinary_spec]

theorem createData_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) (item : List SkbId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.createData pid item
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (createData_ordinary pid item).wp P hp

theorem createInitiation_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.createInitiation pid) := by
  frame_same [Leanux.WG.createInitiation] using [generatePublic_spec, getDev_spec, getPeer_spec, hidden_snapshot_spec, indexInsert_spec, messageEphemeral_spec, mixDh_spec, mixPrecomputedDh_spec, setChain_spec, setPeer_spec]

theorem createInitiation_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.createInitiation pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (createInitiation_sameSnapshot pid).wp P

theorem createResponse_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.createResponse pid) := by
  frame_same [Leanux.WG.createResponse] using [generatePublic_spec, getPeer_spec, hidden_snapshot_spec, indexInsert_spec, kdfOut_spec, kdf_spec, messageEphemeral_spec, mixDh_spec, setChain_spec, setPeer_spec]

theorem createResponse_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.createResponse pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (createResponse_sameSnapshot pid).wp P

theorem queuedExpiredZeroKeyMaterial_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.queuedExpiredZeroKeyMaterial pid) := by
  frame_ordinary [Leanux.WG.queuedExpiredZeroKeyMaterial] using [handshakeClear_spec, peerPut_spec] ordinary [keypairsClear_spec]

theorem queuedExpiredZeroKeyMaterial_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.queuedExpiredZeroKeyMaterial pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (queuedExpiredZeroKeyMaterial_ordinary pid).wp P hp

theorem timersDataReceived_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersDataReceived pid) := by
  frame_same [Leanux.WG.timersDataReceived] using [getDev_spec, getPeer_spec, modPeerTimer_spec, setPeer_spec]

theorem timersDataReceived_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersDataReceived pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersDataReceived_sameSnapshot pid).wp P

theorem timersHandshakeInitiated_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersHandshakeInitiated pid) := by
  frame_same [Leanux.WG.timersHandshakeInitiated] using [jitterBelowRekeyTimeout_spec, modPeerTimer_spec]

theorem timersHandshakeInitiated_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersHandshakeInitiated pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersHandshakeInitiated_sameSnapshot pid).wp P

theorem timersSessionDerived_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersSessionDerived pid) := by
  frame_same [Leanux.WG.timersSessionDerived] using [modPeerTimer_spec]

theorem timersSessionDerived_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersSessionDerived pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersSessionDerived_sameSnapshot pid).wp P

theorem timersTraversal_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.timersTraversal pid) := by
  frame_same [Leanux.WG.timersTraversal] using [getPeer_spec, modPeerTimer_spec]

theorem timersTraversal_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.timersTraversal pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timersTraversal_sameSnapshot pid).wp P

theorem sendHandshakeInitiation_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.sendHandshakeInitiation pid) := by
  frame_same [Leanux.WG.sendHandshakeInitiation] using [addMacToPacket_spec, branchExpired_spec, createInitiation_spec, getPeer_spec, hiddenClock_spec, hiddenClock64_spec, sendBufferToPeer_spec, setPeer_spec, timersAnyAuthenticatedPacketSent_spec, timersHandshakeInitiated_spec, timersTraversal_spec]

theorem sendHandshakeInitiation_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendHandshakeInitiation pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendHandshakeInitiation_sameSnapshot pid).wp P

theorem sendHandshakeResponse_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.sendHandshakeResponse pid) := by
  frame_ordinary [Leanux.WG.sendHandshakeResponse] using [addMacToPacket_spec, createResponse_spec, getPeer_spec, hiddenClock_spec, hiddenClock64_spec, sendBufferToPeer_spec, setPeer_spec, timersAnyAuthenticatedPacketSent_spec, timersSessionDerived_spec, timersTraversal_spec] ordinary [beginSession_spec]

theorem sendHandshakeResponse_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendHandshakeResponse pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendHandshakeResponse_ordinary pid).wp P hp

theorem sendStagedPackets_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.sendStagedPackets pid) := by
  frame_ordinary [Leanux.WG.sendStagedPackets] using [mapM_snapshot_spec, branchExpired_spec, getKeypair_live_spec, getPeer_spec, ipTunnelEcnEncap_spec, keypairGet_snapshot_spec, peerGet_spec, sendQueuedHandshakeInitiation_spec, setKeypair_live_spec, setPeer_spec, newTxSkb_spec] ordinary [createData_spec, keypairPut_ordinary_spec]

theorem sendStagedPackets_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendStagedPackets pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendStagedPackets_ordinary pid).wp P hp

theorem handshakeSendWorker_sameSnapshot (pid : PeerId) : SameSnapshot (Leanux.WG.handshakeSendWorker pid) := by
  frame_same [Leanux.WG.handshakeSendWorker] using [peerPut_spec, sendHandshakeInitiation_spec]

theorem handshakeSendWorker_spec (P : Snapshot → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.handshakeSendWorker pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (handshakeSendWorker_sameSnapshot pid).wp P

theorem sendKeepalive_ordinary (pid : PeerId) : OrdinaryAction (Leanux.WG.sendKeepalive pid) := by
  frame_ordinary [Leanux.WG.sendKeepalive] using [getDev_spec, getPeer_spec, hiddenAlloc_snapshot_spec, setPeer_spec] ordinary [sendStagedPackets_spec]

theorem sendKeepalive_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.WG.sendKeepalive pid
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (sendKeepalive_ordinary pid).wp P hp

end Leanux.Proofs.WG.Keypairs.WGTransitions
