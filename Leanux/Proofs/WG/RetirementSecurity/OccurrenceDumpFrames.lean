import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDump

/-! Native full and stepped dump cursors retain every TX packet and the
pending encryption ring while borrowing and returning actual peer references. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceDump
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.WG.NetlinkDump OccurrenceHandshake

macro "occurrence_dump_wire " initial:term : tactic => `(tactic| first
  | (rx_retention_head getPeerDump; exact (getPeerDump_sameWGWorld _ _ _).wp (fun w => txCryptWire w = $initial))
  | (rx_retention_head getNlSock; exact (getNlSock_sameWGWorld _).wp (fun w => txCryptWire w = $initial))
  | (rx_retention_head setNlSock; exact (dump_wire (setNlSock_sameDump _ _)).wp (· = $initial))
  | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (fun w => txCryptWire w = $initial))
  | (rx_retention_head coalesce; exact (coalesce_sameWGWorld _).wp (fun w => txCryptWire w = $initial))
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (fun w => txCryptWire w = $initial)
     intro x b
     change Preserves (fun w => txCryptWire w = $initial) _)
  | (rx_retention_head peerGet; exact ((TxRing.peerGet_frame _).product (TxDisposition.peerGet_packets _)).wp (· = $initial))
  | occurrence_handshake_wire $initial)

theorem dump_done_wire (ctx : DumpCtx) : SameView txCryptWire (wgGetDeviceDone ctx) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' occurrence_dump_wire initial

private theorem dump_tail_wire (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    SameView txCryptWire (deviceDumpTailSource d ctx skb flags attrs) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold deviceDumpTailSource
  simp (config := {zeta := false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' occurrence_dump_wire initial

theorem dump_chunk_wire (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) :
    SameView txCryptWire (wgGetDeviceDump ctx seq skb) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource; exact ((deviceDumpHeader_sameWGStore _ _ _ _).of_factor
      (fun s : WGStoreView => txCryptWire {dev:=s.dev}) _ (fun _=>rfl)).wp (· = initial))
    | (rx_retention_head deviceDumpTailSource; exact (dump_tail_wire _ _ _ _ _).wp (· = initial))
    | occurrence_dump_wire initial

theorem dump_socket_wire (fd : Nat) : SameView txCryptWire (netlinkDump fd) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact (dump_chunk_wire _ _ _).wp (· = initial))
    | (rx_retention_head wgGetDeviceDone; exact (dump_done_wire _).wp (· = initial))
    | occurrence_dump_wire initial

theorem dump_start_wire (fd : Nat) (ref : DeviceRef) : SameView txCryptWire (netlinkDumpStart fd ref) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact (dump_socket_wire _).wp (· = initial))
    | occurrence_dump_wire initial

theorem dump_recv_wire (fd : Nat) : SameView txCryptWire (netlinkRecvmsg fd) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact (dump_socket_wire _).wp (· = initial))
    | occurrence_dump_wire initial

theorem dump_device_wire (ref : DeviceRef) : SameView txCryptWire (wgGetDevice ref) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact (dump_start_wire _ _).wp (· = initial))
    | (rx_retention_head netlinkRecvmsg; exact (dump_recv_wire _).wp (· = initial))
    | occurrence_dump_wire initial


end Leanux.Proofs.WG.RetirementSecurity.OccurrenceDump
