import Leanux.Proofs.WG.RetirementSecurity.TxWorkTraffic
import Leanux.Proofs.WG.RetirementSecurity.TxCoverageDump

/-! Complete native dump cursors preserve TX service while borrowing and
returning peer references. Socket/cursor bookkeeping is factored from the
actual peer-release paths, which may remove empty peers. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.WG.NetlinkDump

theorem serving_dump_frame {action : WG.M α} (same : SameDump action) :
    Preserves (Serving [] [] tx) action :=
  serving_join (passive (TxCovered.Dump.dump_wire same)
    (same.of_factor (fun s : WGStoreView=>handoffTxView {dev:=s.dev}) _ (fun _=>rfl))
    (same.of_factor (fun s : WGStoreView=>queued {dev:=s.dev}) _ (fun _=>rfl)))
    (TxCovered.Dump.dump_frame same)

macro "serving_dump_step" : tactic => `(tactic| first
  | (rx_retention_head getPeerDump; exact serving_store ((getPeerDump_sameWGWorld _ _ _).factor wgStoreView))
  | (rx_retention_head getNlSock; exact serving_store ((getNlSock_sameWGWorld _).factor wgStoreView))
  | (rx_retention_head setNlSock; exact serving_dump_frame (setNlSock_sameDump _ _))
  | (rx_retention_head lookupInterface; exact serving_store ((lookupInterface_sameWGWorld _).factor wgStoreView))
  | (rx_retention_head coalesce; exact serving_store ((coalesce_sameWGWorld _).factor wgStoreView))
  | (rx_retention_head peerGet; exact serving_peer_get _)
  | (rx_retention_head peerPut; exact serving_peer_put _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Serving [] [] _)
     intro item state
     change Preserves (Serving [] [] _) _)
  | serving_metadata_step)

theorem serving_dump_done (ctx : DumpCtx) : Preserves (Serving [] [] tx) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDone
  simp (config:={zeta:=false}) only [branch]
  repeat' serving_dump_step

theorem serving_dump_tail (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    Preserves (Serving [] [] tx) (deviceDumpTailSource d ctx skb flags attrs) := by
  unfold deviceDumpTailSource
  simp (config:={zeta:=false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' serving_dump_step

theorem serving_dump_chunk (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) :
    Preserves (Serving [] [] tx) (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource; exact serving_store (deviceDumpHeader_sameWGStore _ _ _ _))
    | (rx_retention_head deviceDumpTailSource; exact serving_dump_tail _ _ _ _ _)
    | serving_dump_step

theorem serving_dump_socket (fd : Nat) : Preserves (Serving [] [] tx) (netlinkDump fd) := by
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact serving_dump_chunk _ _ _)
    | (rx_retention_head wgGetDeviceDone; exact serving_dump_done _)
    | serving_dump_step

theorem serving_dump_start (fd : Nat) (ref : DeviceRef) :
    Preserves (Serving [] [] tx) (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStart
  simp (config:={zeta:=false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact serving_dump_socket _)
    | serving_dump_step

theorem serving_dump_recv (fd : Nat) : Preserves (Serving [] [] tx) (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact serving_dump_socket _)
    | serving_dump_step

theorem serving_dump_device (ref : DeviceRef) : Preserves (Serving [] [] tx) (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config:={zeta:=false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact serving_dump_start _ _)
    | (rx_retention_head netlinkRecvmsg; exact serving_dump_recv _)
    | serving_dump_step

end Leanux.Proofs.WG.RetirementSecurity.TxWork
