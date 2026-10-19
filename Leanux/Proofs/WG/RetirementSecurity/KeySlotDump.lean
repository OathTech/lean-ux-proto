import Leanux.Proofs.WG.RetirementSecurity.KeySlotTraffic
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDump
import Leanux.Proofs.WG.Lifetimes.DumpAccess

/-! The original dump family preserves live key slots through cursor borrowing
and payment. Full and stepped dumps retain normal errors and source stops. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotDump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.NetlinkDump Queues Queues.RxCredits KeySlotLiveness

theorem dump_frame {action : WG.M α} (same : SameDump action) : Preserves KeySlotLiveness.Inv action :=
  frame (same.of_factor (fun s : WGStoreView=>view {dev:=s.dev}) _ (fun _=>rfl))

macro "key_slot_dump_step" : tactic => `(tactic| first
  | (rx_retention_head getPeerDump; exact (getPeerDump_sameWGWorld _ _ _).wp (KeySlotLiveness.Inv))
  | (rx_retention_head getNlSock; exact (getNlSock_sameWGWorld _).wp (KeySlotLiveness.Inv))
  | (rx_retention_head setNlSock; exact dump_frame (setNlSock_sameDump _ _))
  | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (KeySlotLiveness.Inv))
  | (rx_retention_head coalesce; exact (coalesce_sameWGWorld _).wp (KeySlotLiveness.Inv))
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (KeySlotLiveness.Inv)
     intro x b
     change Preserves (KeySlotLiveness.Inv) _)
  | key_slot_rx_step)

theorem dump_done (ctx : DumpCtx) : Preserves (KeySlotLiveness.Inv) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' key_slot_dump_step

private theorem dump_tail (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    Preserves (KeySlotLiveness.Inv) (deviceDumpTailSource d ctx skb flags attrs) := by
  unfold deviceDumpTailSource
  simp (config := {zeta := false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' key_slot_dump_step

theorem dump_chunk (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) :
    Preserves (KeySlotLiveness.Inv) (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource; exact KeySlotLiveness.store (deviceDumpHeader_sameWGStore _ _ _ _))
    | (rx_retention_head deviceDumpTailSource; exact dump_tail _ _ _ _ _)
    | key_slot_dump_step

theorem dump_socket (fd : Nat) : Preserves (KeySlotLiveness.Inv) (netlinkDump fd) := by
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact dump_chunk _ _ _)
    | (rx_retention_head wgGetDeviceDone; exact dump_done _)
    | key_slot_dump_step

theorem dump_start (fd : Nat) (ref : DeviceRef) : Preserves (KeySlotLiveness.Inv) (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact dump_socket _)
    | key_slot_dump_step

theorem dump_recv (fd : Nat) : Preserves (KeySlotLiveness.Inv) (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact dump_socket _)
    | key_slot_dump_step

theorem dump_device (ref : DeviceRef) : Preserves (KeySlotLiveness.Inv) (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact dump_start _ _)
    | (rx_retention_head netlinkRecvmsg; exact dump_recv _)
    | key_slot_dump_step

theorem dump_call (call : NetlinkDumpCall) : Preserves (KeySlotLiveness.Inv) call.original := by
  cases call with
  | peer pid ctx skb => exact (getPeerDump_sameWGWorld pid ctx skb).wp (KeySlotLiveness.Inv)
  | chunk ctx seq skb => exact dump_chunk ctx seq skb
  | done ctx => exact dump_done ctx
  | dump fd => exact dump_socket fd
  | start fd ref => exact dump_start fd ref
  | receive fd => exact dump_recv fd
  | device ref => exact dump_device ref

end Leanux.Proofs.WG.RetirementSecurity.KeySlotDump
