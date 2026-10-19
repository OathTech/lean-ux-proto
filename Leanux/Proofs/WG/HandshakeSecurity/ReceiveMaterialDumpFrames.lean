import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialControlFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution.Dump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues NetlinkDump TransmitSecurity

theorem dump_preserves (a : WG.M α) (frame : SameDump a) (history : List Journal.Event) :
    Framing.Preserves (Carrier history) a := by
  have same : SameView (fun w : WGWorld => w.dev) a :=
    frame.of_factor (fun s : WGStoreView => s.dev) _ (fun _ => rfl)
  exact same.wp (fun dev => Carrier history {dev := dev})

macro "receive_dump_steps " history:term : tactic => `(tactic| first
  | (rx_retention_head getPeer; exact native_carrier (bounded_read_peer _))
  | (rx_retention_head getPeerDump
     exact dump_preserves _ ((getPeerDump_sameWGWorld _ _ _).factor dumpView) $history)
  | (rx_retention_head getNlSock
     exact dump_preserves _ ((getNlSock_sameWGWorld _).factor dumpView) $history)
  | (rx_retention_head setNlSock; exact dump_preserves _ (setNlSock_sameDump _ _) $history)
  | (rx_retention_head lookupInterface
     exact dump_preserves _ ((lookupInterface_sameWGWorld _).factor dumpView) $history)
  | (rx_retention_head coalesce
     exact dump_preserves _ ((coalesce_sameWGWorld _).factor dumpView) $history)
  | (rx_retention_head peerGet; exact native_carrier (ConfigurationFrames.peer_get _))
  | (rx_retention_head peerPut; exact native_carrier (bounded_peer_put _))
  | (rx_retention_head ForIn.forIn
     first
     | (apply list_view_spec id (Carrier $history); intro x b; change Framing.Preserves (Carrier $history) _)
     | (apply range_view_spec id (Carrier $history); intro x b; change Framing.Preserves (Carrier $history) _))
  | (allocation_release_lift_from AmbientM; exact native_carrier (hoare_liftAmbient _ _))
  | (rx_retention_head getDev; exact native_carrier (bounded_store getDev_sameWGStore))
  | (rx_retention_head setPeer; exact native_carrier (bounded_set_peer _ _))
  | rx_retention_step)

theorem wgGetDeviceDone_preserves (ctx : DumpCtx) (history : List Journal.Event) :
    Framing.Preserves (Carrier history) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' receive_dump_steps history

theorem deviceDumpTail_preserves (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) (history : List Journal.Event) :
    Framing.Preserves (Carrier history) (deviceDumpTailSource d ctx skb flags attrs) := by
  unfold deviceDumpTailSource
  simp (config := {zeta := false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' receive_dump_steps history

theorem wgGetDeviceDump_preserves (ctx : DumpCtx) (seq : Nat) (skb : NlSkb)
    (history : List Journal.Event) :
    Framing.Preserves (Carrier history) (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource
       exact dump_preserves _ ((deviceDumpHeader_sameWGStore _ _ _ _).factor dumpStore) history)
    | (rx_retention_head deviceDumpTailSource; exact deviceDumpTail_preserves _ _ _ _ _ history)
    | receive_dump_steps history

theorem netlinkDump_preserves (fd : Nat) (history : List Journal.Event) :
    Framing.Preserves (Carrier history) (netlinkDump fd) := by
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact wgGetDeviceDump_preserves _ _ _ history)
    | (rx_retention_head wgGetDeviceDone; exact wgGetDeviceDone_preserves _ history)
    | receive_dump_steps history

theorem netlinkDumpStart_preserves (fd : Nat) (ref : DeviceRef)
    (history : List Journal.Event) :
    Framing.Preserves (Carrier history) (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact netlinkDump_preserves _ history)
    | receive_dump_steps history

theorem netlinkRecvmsg_preserves (fd : Nat) (history : List Journal.Event) :
    Framing.Preserves (Carrier history) (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact netlinkDump_preserves _ history)
    | receive_dump_steps history

theorem wgGetDevice_preserves (ref : DeviceRef) (history : List Journal.Event) :
    Framing.Preserves (Carrier history) (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact netlinkDumpStart_preserves _ _ history)
    | (rx_retention_head netlinkRecvmsg; exact netlinkRecvmsg_preserves _ history)
    | receive_dump_steps history

theorem dump_preserves_call (call : NetlinkDumpCall) (history : List Journal.Event) :
    Framing.Preserves (Carrier history) call.original := by
  cases call with
  | peer pid ctx skb => exact dump_preserves _ ((getPeerDump_sameWGWorld pid ctx skb).factor dumpView) history
  | chunk ctx seq skb => exact wgGetDeviceDump_preserves ctx seq skb history
  | done ctx => exact wgGetDeviceDone_preserves ctx history
  | dump fd => exact netlinkDump_preserves fd history
  | start fd ref => exact netlinkDumpStart_preserves fd ref history
  | receive fd => exact netlinkRecvmsg_preserves fd history
  | device ref => exact wgGetDevice_preserves ref history

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution.Dump
