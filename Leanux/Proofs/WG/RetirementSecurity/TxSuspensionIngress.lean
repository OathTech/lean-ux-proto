import Leanux.Proofs.WG.RetirementSecurity.TxWorkIngress

/-! Native ingress may schedule receive/decrypt work but retains suspended
activations. These are source frames, not assumptions about arbitrary ambient
actions. The joint service export uses both facts at the actual UDP entry. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

namespace TxSuspension

theorem allocate_rx (pkt : RxPacket) : Keeps (newRxSkb pkt) := by
  apply skb_lift
  suspension_source [SkbStore.newRx] using []

theorem admit_rx (id : SkbId) : Keeps (enqueuePerDeviceAndPeerRx id) := by
  suspension_source [enqueuePerDeviceAndPeerRx] using [set_rx_packet,rx_packet,peer,branch,set_peer,
    device,cpu_next,modify_device,device_work]

theorem publish_rx_inline (id : SkbId) (state : PacketState) :
    Keeps (enqueuePerPeerRx (Pure.pure () : WG.M Unit) id state) := by
  rw [publication_factor]
  suspension_source [publicationMiddle] using [rx_packet,owner_deref,peer_get,peer,invariant,set_rx_packet,set_peer,peer_put]

theorem consume_data (msg : List UInt8) (src : SkbSource) (ds : Nat) : Keeps (consumeData msg src ds) := by
  suspension_source [consumeData,keypairGetNull,WG.orM] using [index_lookup,invariant,key_get,branch,
    peer,peer_put,key_put,allocate_rx,admit_rx,publish_rx_inline,free_rx]

theorem receive_header (msg : List UInt8) : Keeps (prepareSkbHeader msg) := by
  suspension_source [prepareSkbHeader,validateHeaderLen,WG.andM,WG.orM] using [branch,invariant,unsupported]

theorem dsfield (protocol : Nat) (bytes : List UInt8) : Keeps (ipTunnelGetDsfield protocol bytes) := by
  suspension_source [ipTunnelGetDsfield] using [branch,invariant,unsupported]

theorem receive_cpu : Keeps cpumaskNextOnline := by
  suspension_source [cpumaskNextOnline] using [device,branch,modify_device]

theorem packet_receive (msg : List UInt8) (src : SkbSource) : Keeps (packetReceive msg src) := by
  suspension_source [packetReceive] using [receive_header,branch,unsupported,invariant,device,
    modify_device,receive_cpu,device_work,dsfield,consume_data]

theorem ingress (msg : List UInt8) (src : SkbSource) : Keeps (wgReceive msg src) := by
  suspension_source [wgReceive] using [branch,unsupported,packet_receive]

end TxSuspension

namespace TxWork

theorem ingress_actor (msg : List UInt8) (src : SkbSource) :
    Preserves (At (Covered locals crypt) crypt active) (liftWG (wgReceive msg src)) :=
  At.native (fun _=>serving_ingress msg src) (TxSuspension.ingress msg src)

end TxWork
end Leanux.Proofs.WG.RetirementSecurity
