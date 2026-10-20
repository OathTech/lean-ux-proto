import Leanux.Proofs.WG.Config.DumpInvariantFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config.DumpInvariant
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Std.Do

variable {P : WGWorld → Prop}

macro "config_dump_invariant_step " c:term : tactic => `(tactic| first
  | (rx_retention_head getDev; exact frame $c _ (getDev_sameWGStore.factor dumpStore))
  | (rx_retention_head getNlSock; exact frame $c _ ((getNlSock_sameWGWorld _).factor dumpView))
  | (rx_retention_head setNlSock; exact frame $c _ (setNlSock_sameDump _ _))
  | (rx_retention_head lookupInterface; exact frame $c _ ((lookupInterface_sameWGWorld _).factor dumpView))
  | (rx_retention_head coalesce; exact frame $c _ ((coalesce_sameWGWorld _).factor dumpView))
  | (rx_retention_head peerGet; exact ($c).acquire _)
  | (rx_retention_head peerPut; exact ($c).release _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id _
     intro _ _
     change Preserves _ _)
  | rx_retention_step)

theorem done (c : Contracts P) (ctx : DumpCtx) :
    Preserves P (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' config_dump_invariant_step c

private theorem replace (c : Contracts P) (ctx : DumpCtx)
    (next : Option PeerId) (finished : Bool) :
    Preserves P (RxCredits.DumpReservation.replaceSource ctx next finished) := by
  unfold RxCredits.DumpReservation.replaceSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' config_dump_invariant_step c

private theorem finish (c : Contracts P) (seq : UInt32) (ctx : DumpCtx)
    (next : Option PeerId) (skb : NlSkb) (flags : Nat)
    (attrs : List (String × Lean.Json)) (finished : Bool)
    (peers : Option (Array PeerDumpAttrs)) :
    Preserves P (RxCredits.DumpReservation.finishSource seq ctx next skb flags attrs finished peers) := by
  unfold RxCredits.DumpReservation.finishSource
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head RxCredits.DumpReservation.replaceSource; exact replace c _ _ _)
    | config_dump_invariant_step c

theorem tail (c : Contracts P) (d : Device) (ctx : DumpCtx)
    (skb : NlSkb) (flags : Nat) (attrs : List (String × Lean.Json)) :
    Preserves P (NetlinkDump.deviceDumpTailSource d ctx skb flags attrs) := by
  rw [RxCredits.DumpReservation.tail_factor]
  exact preserves_bind ((RxCredits.DumpReservation.walk_frame d ctx skb).wp P)
    (fun _ => finish c _ _ _ _ _ _ _ _)

theorem chunk (c : Contracts P) (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) :
    Preserves P (wgGetDeviceDump ctx seq skb) := by
  rw [NetlinkDump.wgGetDeviceDump_source]
  exact preserves_bind (frame c _ (getDev_sameWGStore.factor dumpStore)) fun d =>
    preserves_bind
      (frame c _ ((deviceDumpHeader_sameWGStore d ctx seq skb).factor dumpStore))
      (fun _ => tail c _ _ _ _ _)

private theorem socket_tail (c : Contracts P) (fd : Nat) (sock : NlSock)
    (skb : NlSkb) :
    Preserves P (RxCredits.DurableHolders.socketTailSource fd sock skb) := by
  unfold RxCredits.DurableHolders.socketTailSource
  repeat' first
    | (rx_retention_head wgGetDeviceDone; exact done c _)
    | config_dump_invariant_step c

theorem socket (c : Contracts P) (fd : Nat) :
    Preserves P (netlinkDump fd) := by
  rw [RxCredits.DurableHolders.netlink_factor]
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact chunk c _ _ _)
    | (rx_retention_head RxCredits.DurableHolders.socketTailSource; exact socket_tail c _ _ _)
    | config_dump_invariant_step c

theorem start (c : Contracts P) (fd : Nat) (ref : DeviceRef) :
    Preserves P (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact socket c _)
    | config_dump_invariant_step c

theorem receive (c : Contracts P) (fd : Nat) :
    Preserves P (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact socket c _)
    | config_dump_invariant_step c

theorem device (c : Contracts P) (ref : DeviceRef) :
    Preserves P (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact start c _ _)
    | (rx_retention_head netlinkRecvmsg; exact receive c _)
    | config_dump_invariant_step c

/-- All seven original result types retain the same invariant on normal return.
Neither a cursor-readiness premise nor a completed-dump premise is required. -/
theorem call (c : Contracts P) (action : NetlinkDumpCall) :
    Preserves P action.original := by
  cases action with
  | peer pid ctx skb => exact (getPeerDump_sameWGWorld pid ctx skb).wp P
  | chunk ctx seq skb => exact chunk c ctx seq skb
  | done ctx => exact done c ctx
  | dump fd => exact socket c fd
  | start fd ref => exact start c fd ref
  | receive fd => exact receive c fd
  | device ref => exact device c ref

end Leanux.Proofs.WG.Config.DumpInvariant
