import Leanux.Proofs.WG.RetirementSecurity.TxWorkDump

/-! Actual full and stepped netlink serialization leaves suspended workers
unchanged. This complements the service proof's real cursor reference releases. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Leanux.Proofs.WG.NetlinkDump

namespace TxSuspension

theorem dump_allowedips (skb : NlSkb) (family masked cidr : Nat) :
    Keeps (getAllowedips skb family masked cidr) := by
  suspension_source [getAllowedips] using [branch]

theorem dump_read_node (node : AipNode) : Keeps (readNode node) := by
  suspension_source [readNode] using [branch,invariant,endian]

theorem dump_peer (pid : PeerId) (ctx : DumpCtx) (skb : NlSkb) : Keeps (getPeerDump pid ctx skb) := by
  suspension_source [getPeerDump] using [peer,device,branch,invariant,aip_node_call,dump_read_node,dump_allowedips]

theorem dump_done (ctx : DumpCtx) : Keeps (wgGetDeviceDone ctx) := by
  suspension_source [wgGetDeviceDone] using [branch,peer_put]

theorem dump_header (d : Device) (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) :
    Keeps (deviceDumpHeaderSource d ctx seq skb) := by
  suspension_source [deviceDumpHeaderSource] using [branch,unsupported]

theorem dump_tail (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    Keeps (deviceDumpTailSource d ctx skb flags attrs) := by
  suspension_source [deviceDumpTailSource,requireNotPending,WG.orM,WG.andM]
    using [peer,branch,invariant,dump_peer,peer_get,peer_put,unsupported]

theorem dump_chunk (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) : Keeps (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  suspension_source [] using [device,dump_header,dump_tail]

theorem dump_socket_get (fd : Nat) : Keeps (getNlSock fd) := by
  suspension_source [getNlSock] using []

theorem dump_socket_set (fd : Nat) (sock : NlSock) : Keeps (setNlSock fd sock) := by
  suspension_source [setNlSock] using []

theorem dump_socket (fd : Nat) : Keeps (netlinkDump fd) := by
  suspension_source [netlinkDump] using [dump_socket_get,dump_socket_set,dump_chunk,dump_done]

theorem dump_start (fd : Nat) (ref : DeviceRef) : Keeps (netlinkDumpStart fd ref) := by
  suspension_source [netlinkDumpStart] using [dump_socket_get,dump_socket_set,lookup_interface,
    branch,invariant,unsupported,dump_socket]

theorem dump_recv (fd : Nat) : Keeps (netlinkRecvmsg fd) := by
  suspension_source [netlinkRecvmsg] using [dump_socket_get,dump_socket_set,dump_socket]

theorem dump_coalesce (messages : List NlMessage) : Keeps (coalesce messages) := by
  suspension_source [coalesce] using [invariant]

theorem dump_device (ref : DeviceRef) : Keeps (wgGetDevice ref) := by
  suspension_source [wgGetDevice] using [dump_start,dump_recv,dump_coalesce,invariant]

end TxSuspension

namespace TxWork

theorem dump_device_actor (ref : DeviceRef) :
    Preserves (At (Covered [] []) [] active) (liftWG (wgGetDevice ref)) :=
  At.native (fun _=>serving_dump_device ref) (TxSuspension.dump_device ref)

theorem dump_start_actor (fd : Nat) (ref : DeviceRef) :
    Preserves (At (Covered [] []) [] active) (liftWG (netlinkDumpStart fd ref)) :=
  At.native (fun _=>serving_dump_start fd ref) (TxSuspension.dump_start fd ref)

theorem dump_recv_actor (fd : Nat) :
    Preserves (At (Covered [] []) [] active) (liftWG (netlinkRecvmsg fd)) :=
  At.native (fun _=>serving_dump_recv fd) (TxSuspension.dump_recv fd)

end TxWork
end Leanux.Proofs.WG.RetirementSecurity
