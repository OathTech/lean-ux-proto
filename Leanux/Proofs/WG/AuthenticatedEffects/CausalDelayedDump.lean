import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedTraffic
import Leanux.Proofs.WG.Packets.PublicationDump

/-! Netlink serialization may borrow and repay peers; it preserves pending
wheel origins and actual send-work order, including partial dump returns. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues NetlinkDump
set_option maxHeartbeats 600000

theorem dump_native (action : WG.M α) (same : SameDump action) : StateSafe (liftWGPrefix action) := by
  apply state_framed
  · intro initial
    apply TimerSlots.retained_exact
    exact same.of_factor
      (fun s pid t => (s.dev.bind fun d => d.peers[pid]?).map
        (fun p => (p.internalId,p.timer t,p.wheel t))) TimerSlots.view (fun _ => rfl)
  · exact same.of_factor (fun s => (s.dev.map Device.sendWorkQueue).getD []) QueuedOccurrences.queue (fun _ => rfl)

macro "causal_delayed_dump_step " h:term : tactic => `(tactic| first
  | (rx_retention_head getPeerDump; exact (getPeerDump_sameWGWorld _ _ _).wp (Inv $h))
  | (rx_retention_head getNlSock; exact (getNlSock_sameWGWorld _).wp (Inv $h))
  | (rx_retention_head setNlSock; exact native_contract _ (dump_native _ (setNlSock_sameDump _ _)) $h)
  | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (Inv $h))
  | (rx_retention_head coalesce; exact (coalesce_sameWGWorld _).wp (Inv $h))
  | (rx_retention_head peerPut; exact native_contract _ (by causal_delayed_native) $h)
  | (rx_retention_head peerGet; exact native_contract _ (by causal_delayed_native) $h)
  | (rx_retention_head getDev; exact native_contract _ (by causal_delayed_native) $h)
  | (rx_retention_head getPeer; exact native_contract _ (by causal_delayed_native) $h)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))
  | (rx_retention_head ForIn.forIn
     first
       | (apply list_view_spec id (Inv $h); intro x state; change Preserves (Inv $h) _)
       | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rx_retention_step)

theorem wgGetDeviceDone_delayed (ctx : DumpCtx) :
    StateSafe (liftWGPrefix (wgGetDeviceDone ctx)) := by
  apply state_native
  intro h
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' causal_delayed_dump_step h

theorem deviceDumpTail_delayed (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    StateSafe (liftWGPrefix (deviceDumpTailSource d ctx skb flags attrs)) := by
  apply state_native
  intro h
  unfold deviceDumpTailSource
  simp (config := {zeta := false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' causal_delayed_dump_step h

theorem wgGetDeviceDump_delayed (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb)
    :
    StateSafe (liftWGPrefix (wgGetDeviceDump ctx seq skb)) := by
  apply state_native
  intro h
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource
       exact native_contract _ (native_store _ (deviceDumpHeader_sameWGStore _ _ _ _)) h)
    | (rx_retention_head deviceDumpTailSource; exact native_contract _ (deviceDumpTail_delayed _ _ _ _ _) h)
    | causal_delayed_dump_step h

theorem netlinkDump_delayed (fd : Nat) :
    StateSafe (liftWGPrefix (netlinkDump fd)) := by
  apply state_native
  intro h
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact native_contract _ (wgGetDeviceDump_delayed _ _ _) h)
    | (rx_retention_head wgGetDeviceDone; exact native_contract _ (wgGetDeviceDone_delayed _) h)
    | causal_delayed_dump_step h

theorem netlinkDumpStart_delayed (fd : Nat) (ref : DeviceRef)
    :
    StateSafe (liftWGPrefix (netlinkDumpStart fd ref)) := by
  apply state_native
  intro h
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact native_contract _ (netlinkDump_delayed _) h)
    | causal_delayed_dump_step h

theorem netlinkRecvmsg_delayed (fd : Nat) :
    StateSafe (liftWGPrefix (netlinkRecvmsg fd)) := by
  apply state_native
  intro h
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact native_contract _ (netlinkDump_delayed _) h)
    | causal_delayed_dump_step h

theorem wgGetDevice_delayed (ref : DeviceRef) :
    StateSafe (liftWGPrefix (wgGetDevice ref)) := by
  apply state_native
  intro h
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact native_contract _ (netlinkDumpStart_delayed _ _) h)
    | (rx_retention_head netlinkRecvmsg; exact native_contract _ (netlinkRecvmsg_delayed _) h)
    | causal_delayed_dump_step h

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
