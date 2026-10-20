import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceEnvironment

namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference.Dump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues NetlinkDump

theorem dump_preserves (a : WG.M α) (same : SameDump a) : Framing.Preserves Inv a := by
  apply frame (same.of_factor (fun s : WGStoreView =>
    fun pid => (s.dev.bind fun d => d.peers[pid]?).map Peer.refcount) PeerReference.view ?_)
  intro w
  rfl

macro "peer_reference_driver_dump_steps" : tactic => `(tactic| first
  | (rx_retention_head getPeer; exact read_peer _)
  | (rx_retention_head getPeerDump
     exact dump_preserves _ ((getPeerDump_sameWGWorld _ _ _).factor dumpView))
  | (rx_retention_head getNlSock
     exact dump_preserves _ ((getNlSock_sameWGWorld _).factor dumpView))
  | (rx_retention_head setNlSock; exact dump_preserves _ (setNlSock_sameDump _ _))
  | (rx_retention_head lookupInterface
     exact dump_preserves _ ((lookupInterface_sameWGWorld _).factor dumpView))
  | (rx_retention_head coalesce
     exact dump_preserves _ ((coalesce_sameWGWorld _).factor dumpView))
  | (rx_retention_head peerGet; exact peer_get _)
  | (rx_retention_head peerPut; exact peer_put _)
  | (rx_retention_head ForIn.forIn
     first
     | (apply list_view_spec id Inv; intro x b; change Framing.Preserves Inv _)
     | (apply range_view_spec id Inv; intro x b; change Framing.Preserves Inv _))
  | peer_reference_handshake_step)

theorem wgGetDeviceDone_preserves (ctx : DumpCtx) :
    Framing.Preserves Inv (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' peer_reference_driver_dump_steps

theorem deviceDumpTail_preserves (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    Framing.Preserves Inv (deviceDumpTailSource d ctx skb flags attrs) := by
  unfold deviceDumpTailSource
  simp (config := {zeta := false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' peer_reference_driver_dump_steps

theorem wgGetDeviceDump_preserves (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb)
    :
    Framing.Preserves Inv (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource
       exact dump_preserves _ ((deviceDumpHeader_sameWGStore _ _ _ _).factor dumpStore))
    | (rx_retention_head deviceDumpTailSource; exact deviceDumpTail_preserves _ _ _ _ _)
    | peer_reference_driver_dump_steps

theorem netlinkDump_preserves (fd : Nat) :
    Framing.Preserves Inv (netlinkDump fd) := by
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact wgGetDeviceDump_preserves _ _ _)
    | (rx_retention_head wgGetDeviceDone; exact wgGetDeviceDone_preserves _)
    | peer_reference_driver_dump_steps

theorem netlinkDumpStart_preserves (fd : Nat) (ref : DeviceRef)
    :
    Framing.Preserves Inv (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact netlinkDump_preserves _)
    | peer_reference_driver_dump_steps

theorem netlinkRecvmsg_preserves (fd : Nat) :
    Framing.Preserves Inv (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact netlinkDump_preserves _)
    | peer_reference_driver_dump_steps

theorem wgGetDevice_preserves (ref : DeviceRef) :
    Framing.Preserves Inv (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact netlinkDumpStart_preserves _ _)
    | (rx_retention_head netlinkRecvmsg; exact netlinkRecvmsg_preserves _)
    | peer_reference_driver_dump_steps

theorem dump_preserves_call (call : NetlinkDumpCall) :
    Framing.Preserves Inv call.original := by
  cases call with
  | peer pid ctx skb => exact dump_preserves _ ((getPeerDump_sameWGWorld pid ctx skb).factor dumpView)
  | chunk ctx seq skb => exact wgGetDeviceDump_preserves ctx seq skb
  | done ctx => exact wgGetDeviceDone_preserves ctx
  | dump fd => exact netlinkDump_preserves fd
  | start fd ref => exact netlinkDumpStart_preserves fd ref
  | receive fd => exact netlinkRecvmsg_preserves fd
  | device ref => exact wgGetDevice_preserves ref

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference.Dump
