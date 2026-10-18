import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverUp

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts.Dump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues NetlinkDump

theorem dump_preserves (a : WG.M α) (frame : SameDump a) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) a := by
  have same : SameView (fun w : WGWorld => w.dev) a :=
    frame.of_factor (fun s : WGStoreView => s.dev) _ (fun _ => rfl)
  exact same.wp (fun dev => Carrier confirmed {dev := dev})

macro "responder_driver_dump_steps " confirmed:term : tactic => `(tactic| first
  | (rx_retention_head getPeer; exact carrier_read_peer _ $confirmed)
  | (rx_retention_head getPeerDump
     exact dump_preserves _ ((getPeerDump_sameWGWorld _ _ _).factor dumpView) $confirmed)
  | (rx_retention_head getNlSock
     exact dump_preserves _ ((getNlSock_sameWGWorld _).factor dumpView) $confirmed)
  | (rx_retention_head setNlSock; exact dump_preserves _ (setNlSock_sameDump _ _) $confirmed)
  | (rx_retention_head lookupInterface
     exact dump_preserves _ ((lookupInterface_sameWGWorld _).factor dumpView) $confirmed)
  | (rx_retention_head coalesce
     exact dump_preserves _ ((coalesce_sameWGWorld _).factor dumpView) $confirmed)
  | (rx_retention_head peerGet; exact carrier_peer_get _ $confirmed)
  | (rx_retention_head peerPut; exact carrier_peer_put _ $confirmed)
  | (rx_retention_head ForIn.forIn
     first
     | (apply list_view_spec id (Carrier $confirmed); intro x b; change Framing.Preserves (Carrier $confirmed) _)
     | (apply range_view_spec id (Carrier $confirmed); intro x b; change Framing.Preserves (Carrier $confirmed) _))
  | responder_carrier_handshake_step $confirmed)

theorem wgGetDeviceDone_preserves (ctx : DumpCtx) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' responder_driver_dump_steps confirmed

theorem deviceDumpTail_preserves (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (deviceDumpTailSource d ctx skb flags attrs) := by
  unfold deviceDumpTailSource
  simp (config := {zeta := false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' responder_driver_dump_steps confirmed

theorem wgGetDeviceDump_preserves (ctx : DumpCtx) (seq : Nat) (skb : NlSkb)
    (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource
       exact dump_preserves _ ((deviceDumpHeader_sameWGStore _ _ _ _).factor dumpStore) confirmed)
    | (rx_retention_head deviceDumpTailSource; exact deviceDumpTail_preserves _ _ _ _ _ confirmed)
    | responder_driver_dump_steps confirmed

theorem netlinkDump_preserves (fd : Nat) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (netlinkDump fd) := by
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact wgGetDeviceDump_preserves _ _ _ confirmed)
    | (rx_retention_head wgGetDeviceDone; exact wgGetDeviceDone_preserves _ confirmed)
    | responder_driver_dump_steps confirmed

theorem netlinkDumpStart_preserves (fd : Nat) (ref : DeviceRef)
    (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact netlinkDump_preserves _ confirmed)
    | responder_driver_dump_steps confirmed

theorem netlinkRecvmsg_preserves (fd : Nat) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact netlinkDump_preserves _ confirmed)
    | responder_driver_dump_steps confirmed

theorem wgGetDevice_preserves (ref : DeviceRef) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact netlinkDumpStart_preserves _ _ confirmed)
    | (rx_retention_head netlinkRecvmsg; exact netlinkRecvmsg_preserves _ confirmed)
    | responder_driver_dump_steps confirmed

theorem dump_preserves_call (call : NetlinkDumpCall) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) call.original := by
  cases call with
  | peer pid ctx skb => exact dump_preserves _ ((getPeerDump_sameWGWorld pid ctx skb).factor dumpView) confirmed
  | chunk ctx seq skb => exact wgGetDeviceDump_preserves ctx seq skb confirmed
  | done ctx => exact wgGetDeviceDone_preserves ctx confirmed
  | dump fd => exact netlinkDump_preserves fd confirmed
  | start fd ref => exact netlinkDumpStart_preserves fd ref confirmed
  | receive fd => exact netlinkRecvmsg_preserves fd confirmed
  | device ref => exact wgGetDevice_preserves ref confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts.Dump
