import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueConfiguration
import Leanux.Proofs.WG.Lifetimes.DumpAccess

/-! The native full and stepped netlink dump paths retain handshake inputs.
Cursor borrowing and reference release are included in the original calls. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Leanux.Proofs.WG.NetlinkDump Queues
set_option maxHeartbeats 600000

theorem dump_cell {action : WG.M α} (same : SameDump action) : SameView view action :=
  same.of_factor (fun s : WGStoreView => s.dev.map (·.handshakeQueue)) view (fun _=>rfl)

theorem dump_done_cell (ctx : DumpCtx) : SameView view (wgGetDeviceDone ctx) := by
  handshake_cell_source [wgGetDeviceDone] using [peerPut_frame]

private theorem dump_tail_cell (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    SameView view (deviceDumpTailSource d ctx skb flags attrs) := by
  have get := fun pid ctx skb => (show SameView view (getPeerDump pid ctx skb) from (getPeerDump_sameWGWorld pid ctx skb).factor view)
  handshake_cell_source [deviceDumpTailSource,requireNotPending] using
    [get,peerGet_frame,peerPut_frame]

theorem dump_chunk_cell (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) :
    SameView view (wgGetDeviceDump ctx seq skb) := by
  have header := fun d ctx seq skb => kernel (deviceDumpHeader_sameWGStore d ctx seq skb)
  rw [wgGetDeviceDump_source]
  handshake_cell_source [] using [header,dump_tail_cell]

theorem dump_socket_cell (fd : Nat) : SameView view (netlinkDump fd) := by
  have get := fun fd => (show SameView view (getNlSock fd) from (getNlSock_sameWGWorld fd).factor view)
  have set := fun fd sock => dump_cell (setNlSock_sameDump fd sock)
  have coalesced := fun xs => (show SameView view (coalesce xs) from (coalesce_sameWGWorld xs).factor view)
  handshake_cell_source [netlinkDump] using [get,set,coalesced,dump_chunk_cell,dump_done_cell]

theorem dump_start_cell (fd : Nat) (ref : DeviceRef) : SameView view (netlinkDumpStart fd ref) := by
  have get := fun fd => (show SameView view (getNlSock fd) from (getNlSock_sameWGWorld fd).factor view)
  have set := fun fd sock => dump_cell (setNlSock_sameDump fd sock)
  have lookup := fun ref => (show SameView view (lookupInterface ref) from (lookupInterface_sameWGWorld ref).factor view)
  handshake_cell_source [netlinkDumpStart] using [get,set,lookup,dump_socket_cell]

theorem dump_receive_cell (fd : Nat) : SameView view (netlinkRecvmsg fd) := by
  have get := fun fd => (show SameView view (getNlSock fd) from (getNlSock_sameWGWorld fd).factor view)
  have set := fun fd sock => dump_cell (setNlSock_sameDump fd sock)
  handshake_cell_source [netlinkRecvmsg] using [get,set,dump_socket_cell]

theorem dump_device_cell (ref : DeviceRef) : SameView view (wgGetDevice ref) := by
  have get := fun fd => (show SameView view (getNlSock fd) from (getNlSock_sameWGWorld fd).factor view)
  have set := fun fd sock => dump_cell (setNlSock_sameDump fd sock)
  have coalesced := fun xs => (show SameView view (coalesce xs) from (coalesce_sameWGWorld xs).factor view)
  handshake_cell_source [wgGetDevice] using [get,set,coalesced,dump_start_cell,dump_receive_cell]

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
