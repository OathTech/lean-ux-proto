import Leanux.Proofs.WG.Packets.PublicationPeerObserved
import Leanux.Proofs.WG.Origins.OwnerControlCalls

/-! Native dump cursors retain older packet publications through their exact
reference gets and puts. The observed contract preserves the same failed journal. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues NetlinkDump

private theorem dump_preserves (a : WG.M α) (frame : SameDump a)
    (history : List RxHistory.Event) : Preserves (Inv history) a :=
  preserves_of_configured a
    (frame.of_factor
      (fun s : WGStoreView => (s.dev.map (·.ifindex),fun id => s.dev.bind fun d => d.rxSkbs[id]?))
      RxDisposition.nativeRxStore (fun _ => rfl))
    (frame.of_factor (fun s : WGStoreView => s.dev.map ConfiguredIdentity.state)
      ConfiguredIdentity.view (fun _ => rfl)) history

private theorem dump_readPeer (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi hr
  exact (Queues.getPeer_normal pid w v p a b hr).1 ▸ hi

macro "publication_dump_steps " history:term : tactic => `(tactic| first
  | (rx_retention_head getPeer; exact dump_readPeer _ $history)
  | (rx_retention_head getPeerDump
     exact dump_preserves _ ((getPeerDump_sameWGWorld _ _ _).factor dumpView) $history)
  | (rx_retention_head getNlSock
     exact dump_preserves _ ((getNlSock_sameWGWorld _).factor dumpView) $history)
  | (rx_retention_head setNlSock; exact dump_preserves _ (setNlSock_sameDump _ _) $history)
  | (rx_retention_head lookupInterface
     exact dump_preserves _ ((lookupInterface_sameWGWorld _).factor dumpView) $history)
  | (rx_retention_head coalesce
     exact dump_preserves _ ((coalesce_sameWGWorld _).factor dumpView) $history)
  | (rx_retention_head peerGet; exact peerGet_preserves _ $history)
  | (rx_retention_head peerPut; exact peerPut_preserves _ $history)
  | publication_removal_step $history)

theorem wgGetDeviceDone_preserves (ctx : DumpCtx) (history : List RxHistory.Event) :
    Preserves (Inv history) (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' publication_dump_steps history

theorem deviceDumpTail_preserves (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) (history : List RxHistory.Event) :
    Preserves (Inv history) (deviceDumpTailSource d ctx skb flags attrs) := by
  unfold deviceDumpTailSource
  simp (config := {zeta := false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' publication_dump_steps history

theorem wgGetDeviceDump_preserves (ctx : DumpCtx) (seq : Nat) (skb : NlSkb)
    (history : List RxHistory.Event) :
    Preserves (Inv history) (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource
       exact dump_preserves _ ((deviceDumpHeader_sameWGStore _ _ _ _).factor dumpStore) history)
    | (rx_retention_head deviceDumpTailSource; exact deviceDumpTail_preserves _ _ _ _ _ history)
    | publication_dump_steps history

theorem netlinkDump_preserves (fd : Nat) (history : List RxHistory.Event) :
    Preserves (Inv history) (netlinkDump fd) := by
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact wgGetDeviceDump_preserves _ _ _ history)
    | (rx_retention_head wgGetDeviceDone; exact wgGetDeviceDone_preserves _ history)
    | publication_dump_steps history

theorem netlinkDumpStart_preserves (fd : Nat) (ref : DeviceRef)
    (history : List RxHistory.Event) :
    Preserves (Inv history) (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact netlinkDump_preserves _ history)
    | publication_dump_steps history

theorem netlinkRecvmsg_preserves (fd : Nat) (history : List RxHistory.Event) :
    Preserves (Inv history) (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact netlinkDump_preserves _ history)
    | publication_dump_steps history

theorem wgGetDevice_preserves (ref : DeviceRef) (history : List RxHistory.Event) :
    Preserves (Inv history) (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact netlinkDumpStart_preserves _ _ history)
    | (rx_retention_head netlinkRecvmsg; exact netlinkRecvmsg_preserves _ history)
    | publication_dump_steps history

theorem dump_preserves_call (call : NetlinkDumpCall) (history : List RxHistory.Event) :
    Preserves (Inv history) call.original := by
  cases call with
  | peer pid ctx skb => exact dump_preserves _ ((getPeerDump_sameWGWorld pid ctx skb).factor dumpView) history
  | chunk ctx seq skb => exact wgGetDeviceDump_preserves ctx seq skb history
  | done ctx => exact wgGetDeviceDone_preserves ctx history
  | dump fd => exact netlinkDump_preserves fd history
  | start fd ref => exact netlinkDumpStart_preserves fd ref history
  | receive fd => exact netlinkRecvmsg_preserves fd history
  | device ref => exact wgGetDevice_preserves ref history

end Leanux.Proofs.WG.PublicationFrontier

namespace Leanux.Proofs.WG.PublicationJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

theorem dump_checked (call : NetlinkDumpCall) :
    Preserves (RxHistory.mixed (liftWGObserver call.observed)) :=
  native_mixed _ _ (OwnerControlCalls.dump_checked call) call.erases
    (PublicationFrontier.dump_preserves_call call)

end Leanux.Proofs.WG.PublicationJoint
