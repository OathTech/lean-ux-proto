import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastDeviceConfiguration
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDumpFrames

/-! Dump cursors and reference payments preserve the exact historical
encryption projection, including both allocation frontiers and pending aliases. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Dump
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.WG.NetlinkDump

theorem dump_view {action : WG.M α} (same : SameDump action) : SameView view action :=
  same.of_factor (fun s : WGStoreView => view {dev:=s.dev,netIfindexNext:=s.netIfindexNext}) _ (fun _=>rfl)

macro "encryption_past_dump_frame " initial:term : tactic => `(tactic| first
  | (rx_retention_head getPeerDump; exact (getPeerDump_sameWGWorld _ _ _).wp (fun w => view w = $initial))
  | (rx_retention_head getNlSock; exact (getNlSock_sameWGWorld _).wp (fun w => view w = $initial))
  | (rx_retention_head setNlSock; exact (dump_view (setNlSock_sameDump _ _)).wp (· = $initial))
  | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (fun w => view w = $initial))
  | (rx_retention_head coalesce; exact (coalesce_sameWGWorld _).wp (fun w => view w = $initial))
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (fun w => view w = $initial)
     intro x b
     change Preserves (fun w => view w = $initial) _)
  | (rx_retention_head peerGet; exact (peer_get _).wp (· = $initial))
  | encryption_past_passive $initial)

theorem dump_done_view (ctx : DumpCtx) : SameView view (wgGetDeviceDone ctx) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' encryption_past_dump_frame initial

private theorem dump_tail_view (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    SameView view (deviceDumpTailSource d ctx skb flags attrs) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold deviceDumpTailSource
  simp (config := {zeta := false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' encryption_past_dump_frame initial

theorem dump_chunk_view (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) :
    SameView view (wgGetDeviceDump ctx seq skb) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource; exact ((deviceDumpHeader_sameWGStore _ _ _ _).of_factor
      (fun s : WGStoreView => view {dev:=s.dev,netIfindexNext:=s.netIfindexNext}) _ (fun _=>rfl)).wp (· = initial))
    | (rx_retention_head deviceDumpTailSource; exact (dump_tail_view _ _ _ _ _).wp (· = initial))
    | encryption_past_dump_frame initial

theorem dump_socket_view (fd : Nat) : SameView view (netlinkDump fd) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact (dump_chunk_view _ _ _).wp (· = initial))
    | (rx_retention_head wgGetDeviceDone; exact (dump_done_view _).wp (· = initial))
    | encryption_past_dump_frame initial

theorem dump_start_view (fd : Nat) (ref : DeviceRef) : SameView view (netlinkDumpStart fd ref) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact (dump_socket_view _).wp (· = initial))
    | encryption_past_dump_frame initial

theorem dump_recv_view (fd : Nat) : SameView view (netlinkRecvmsg fd) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact (dump_socket_view _).wp (· = initial))
    | encryption_past_dump_frame initial

theorem dump_device_view (ref : DeviceRef) : SameView view (wgGetDevice ref) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact (dump_start_view _ _).wp (· = initial))
    | (rx_retention_head netlinkRecvmsg; exact (dump_recv_view _).wp (· = initial))
    | encryption_past_dump_frame initial


end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Dump
