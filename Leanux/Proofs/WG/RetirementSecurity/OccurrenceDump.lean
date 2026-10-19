import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTraffic
import Leanux.Proofs.WG.Lifetimes.DumpAccess

/-! The original full and stepped native dump family preserves the live TX
frontier through actual cursor borrowing and payment. Normal errors and source
Stops retain their domains; no cursor absence or completion is assumed. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceDump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.NetlinkDump Queues Queues.RxCredits OccurrenceStack OccurrenceConfiguration

theorem dump_wire {action : WG.M α} (same : SameDump action) : SameView txCryptWire action :=
  same.of_factor (fun s : WGStoreView => txCryptWire {dev:=s.dev}) _ (fun _=>rfl)

theorem dump_frame {action : WG.M α} (same : SameDump action) : Preserves (Ready [] []) action :=
  RxPollOccurrences.join (erasesStatePrefix_lift action)
    (dumpLift_preserves_native allocationAmbient allocationDumpStable action same)
    (occurrence_passive (dump_wire same)
      (same.of_factor (fun s : WGStoreView => handoffTxView {dev:=s.dev}) _ (fun _=>rfl)))

macro "occurrence_dump_step" : tactic => `(tactic| first
  | (rx_retention_head getPeerDump; exact (getPeerDump_sameWGWorld _ _ _).wp (Ready [] []))
  | (rx_retention_head getNlSock; exact (getNlSock_sameWGWorld _).wp (Ready [] []))
  | (rx_retention_head setNlSock; exact dump_frame (setNlSock_sameDump _ _))
  | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (Ready [] []))
  | (rx_retention_head coalesce; exact (coalesce_sameWGWorld _).wp (Ready [] []))
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Ready [] [])
     intro x b
     change Preserves (Ready [] []) _)
  | occurrence_config_step)

theorem dump_done (ctx : DumpCtx) : Preserves (Ready [] []) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' occurrence_dump_step

private theorem dump_tail (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    Preserves (Ready [] []) (deviceDumpTailSource d ctx skb flags attrs) := by
  unfold deviceDumpTailSource
  simp (config := {zeta := false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' occurrence_dump_step

theorem dump_chunk (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) :
    Preserves (Ready [] []) (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource; exact RxPollOccurrences.store (deviceDumpHeader_sameWGStore _ _ _ _))
    | (rx_retention_head deviceDumpTailSource; exact dump_tail _ _ _ _ _)
    | occurrence_dump_step

theorem dump_socket (fd : Nat) : Preserves (Ready [] []) (netlinkDump fd) := by
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact dump_chunk _ _ _)
    | (rx_retention_head wgGetDeviceDone; exact dump_done _)
    | occurrence_dump_step

theorem dump_start (fd : Nat) (ref : DeviceRef) : Preserves (Ready [] []) (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact dump_socket _)
    | occurrence_dump_step

theorem dump_recv (fd : Nat) : Preserves (Ready [] []) (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact dump_socket _)
    | occurrence_dump_step

theorem dump_device (ref : DeviceRef) : Preserves (Ready [] []) (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact dump_start _ _)
    | (rx_retention_head netlinkRecvmsg; exact dump_recv _)
    | occurrence_dump_step

theorem dump_call (call : NetlinkDumpCall) : Preserves (Ready [] []) call.original := by
  cases call with
  | peer pid ctx skb => exact (getPeerDump_sameWGWorld pid ctx skb).wp (Ready [] [])
  | chunk ctx seq skb => exact dump_chunk ctx seq skb
  | done ctx => exact dump_done ctx
  | dump fd => exact dump_socket fd
  | start fd ref => exact dump_start fd ref
  | receive fd => exact dump_recv fd
  | device ref => exact dump_device ref

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceDump
