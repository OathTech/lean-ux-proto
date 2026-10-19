import Leanux.Proofs.WG.AuthenticatedEffects.EmissionEnvironmentFrames

/-! UDP admission queues work without emitting a datagram. Its actual later
workers and polls remain observed; these frames cover only native admission. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes TransmitSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private theorem cpu_spec (P : List SentDatagram → Prop) (cpu : Int) :
    Preserves (fun w => P w.sent) (cpumaskNextOnlineFrom cpu) :=
by
  have frame : SameView WGWorld.sent (cpumaskNextOnlineFrom cpu) := by
    sent_frame [cpumaskNextOnlineFrom] using []
  exact frame.wp P

private theorem enqueue_device (id : SkbId) : SameView WGWorld.sent (enqueuePerDeviceAndPeerRx id) := by
  sent_frame [enqueuePerDeviceAndPeerRx,queueDeviceWork] using
    [getRxSkb_sent_spec,setRxSkb_sent_spec,getPeer_sent_spec,setPeer_sent_spec,cpu_spec]
private theorem enqueue_device_spec (P : List SentDatagram → Prop) (id : SkbId) :
    Preserves (fun w => P w.sent) (enqueuePerDeviceAndPeerRx id) := (enqueue_device id).wp P

private theorem enqueue_peer (id : SkbId) (state : PacketState) :
    SameView WGWorld.sent (enqueuePerPeerRx (pure ()) id state : WG.M Unit) := by
  unfold enqueuePerPeerRx
  simp only [monadLift_self]
  sent_frame [IndexOwner.peerDeref,IndexOwner.peerWord] using
    [getRxSkb_sent_spec,setRxSkb_sent_spec,getPeer_sent_spec,setPeer_sent_spec,
      getKeypair_sent_spec,peerGet_sent_spec,peerPut_sent_spec]
private theorem enqueue_peer_spec (P : List SentDatagram → Prop) (id : SkbId) (state : PacketState) :
    Preserves (fun w => P w.sent) (enqueuePerPeerRx (pure ()) id state : WG.M Unit) :=
  (enqueue_peer id state).wp P

private theorem key_get_spec (P : List SentDatagram → Prop) (key : Option KeypairId) :
    Preserves (fun w => P w.sent) (keypairGet key) := by
  have frame : SameView WGWorld.sent (keypairGet key) := by
    sent_frame [keypairGet,refcountIncNotZero] using [getKeypair_sent_spec,setKeypair_sent_spec]
  exact frame.wp P

private theorem index_spec (P : List SentDatagram → Prop) (kinds : List IndexKind) (index : Nat) :
    Preserves (fun w => P w.sent) (indexLookup kinds index) := (indexLookup_sent kinds index).wp P

theorem consume_data (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    SameView WGWorld.sent (consumeData msg src ds) := by
  sent_frame [consumeData,keypairGetNull,newRxSkb,freeRxSkb] using
    [index_spec,key_get_spec,getPeer_sent_spec,keypair_put_spec,peerPut_sent_spec,
      enqueue_device_spec,enqueue_peer_spec,skb_sent_spec]
private theorem consume_data_spec (P : List SentDatagram → Prop) (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves (fun w => P w.sent) (consumeData msg src ds) := (consume_data msg src ds).wp P

private theorem header_spec (P : List SentDatagram → Prop) (msg : List UInt8) :
    Preserves (fun w => P w.sent) (prepareSkbHeader msg) :=
  (prepareSkbHeader_sameWGWorld msg).wp (fun w => P w.sent)
private theorem ds_spec (P : List SentDatagram → Prop) (proto : Nat) (bytes : List UInt8) :
    Preserves (fun w => P w.sent) (ipTunnelGetDsfield proto bytes) :=
  (ipTunnelGetDsfield_sameWGWorld proto bytes).wp (fun w => P w.sent)

theorem receive (msg : List UInt8) (src : SkbSource) : SameView WGWorld.sent (wgReceive msg src) := by
  sent_frame [wgReceive,packetReceive,cpumaskNextOnline,queueDeviceWork] using
    [consume_data_spec,header_spec,ds_spec]

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
