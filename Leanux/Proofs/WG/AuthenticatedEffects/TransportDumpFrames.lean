import Leanux.Proofs.WG.AuthenticatedEffects.TransportLifecycleFrames
import Leanux.Proofs.WG.Packets.PublicationDump

/-! Dump cursor gets and puts can change peer references but retain all RX
cells and their epoch. Native partial dumps and failures keep their scope. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportDump
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues NetlinkDump
open OwnerCompletion (geometry)
set_option maxHeartbeats 600000

private theorem stored {a : WG.M α} (same : SameWGStore a) : SameView geometry a :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.store) same

private theorem socket (fd : Nat) (s : NlSock) : SameView geometry (setNlSock fd s) := by
  apply (setNlSock_sameDump fd s).of_factor
    (fun s : WGStoreView => (s.dev.map fun d => (d.ifindex,d.nextPeer,d.nextKeypairId),
      s.dev.map (·.ifindex),fun id => s.dev.bind fun d => d.rxSkbs[id]?)) _
  intro w
  rfl

macro "transport_dump_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getPeerDump; exact ((getPeerDump_sameWGWorld _ _ _).factor geometry).wp (fun s => s = $initial))
  | (rx_retention_head getNlSock; exact ((getNlSock_sameWGWorld _).factor geometry).wp (fun s => s = $initial))
  | (rx_retention_head setNlSock; exact (socket _ _).wp (fun s => s = $initial))
  | (rx_retention_head lookupInterface; exact ((lookupInterface_sameWGWorld _).factor geometry).wp (fun s => s = $initial))
  | (rx_retention_head coalesce; exact ((coalesce_sameWGWorld _).factor geometry).wp (fun s => s = $initial))
  | completion_traffic $initial)

theorem wgGetDeviceDone_geometry (ctx : DumpCtx) :
    SameView geometry (wgGetDeviceDone ctx) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' transport_dump_step initial

theorem deviceDumpTail_geometry (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    SameView geometry (deviceDumpTailSource d ctx skb flags attrs) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold deviceDumpTailSource
  simp (config := {zeta := false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' transport_dump_step initial

theorem wgGetDeviceDump_geometry (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb)
    :
    SameView geometry (wgGetDeviceDump ctx seq skb) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource
       exact (stored (deviceDumpHeader_sameWGStore _ _ _ _)).wp (fun s => s = initial))
    | (rx_retention_head deviceDumpTailSource; exact (deviceDumpTail_geometry _ _ _ _ _).wp (fun s => s = initial))
    | transport_dump_step initial

theorem netlinkDump_geometry (fd : Nat) :
    SameView geometry (netlinkDump fd) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact (wgGetDeviceDump_geometry _ _ _).wp (fun s => s = initial))
    | (rx_retention_head wgGetDeviceDone; exact (wgGetDeviceDone_geometry _).wp (fun s => s = initial))
    | transport_dump_step initial

theorem netlinkDumpStart_geometry (fd : Nat) (ref : DeviceRef)
    :
    SameView geometry (netlinkDumpStart fd ref) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact (netlinkDump_geometry _).wp (fun s => s = initial))
    | transport_dump_step initial

theorem netlinkRecvmsg_geometry (fd : Nat) :
    SameView geometry (netlinkRecvmsg fd) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact (netlinkDump_geometry _).wp (fun s => s = initial))
    | transport_dump_step initial

theorem wgGetDevice_geometry (ref : DeviceRef) :
    SameView geometry (wgGetDevice ref) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact (netlinkDumpStart_geometry _ _).wp (fun s => s = initial))
    | (rx_retention_head netlinkRecvmsg; exact (netlinkRecvmsg_geometry _).wp (fun s => s = initial))
    | transport_dump_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.TransportDump
