import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.WG.Keypairs.Frames.EnvWorkers
import Leanux.Proofs.WG.Keypairs.SnapshotRules

/-! Ordinary framing of nonreceive environment work, timers, lifecycle calls
and the fixture's packet construction. -/
namespace Leanux.Proofs.WG.Keypairs.EnvFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs
open KernelFrames WGFrames WGTransitions WGMore WGConfig WGDevice
open Observers SchedulerObservers

set_option maxHeartbeats 400000
set_option pp.structureInstances false

theorem requireNoCryptWork_sameSnapshot  : SameSnapshot Env.requireNoCryptWork :=
  sameSnapshot_of_sameWGKernel (Framing.sameWGKernel_of_sameKernel (Framing.requireNoCryptWork_sameKernel))

theorem requireNoCryptWork_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.requireNoCryptWork
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (requireNoCryptWork_sameSnapshot ).wp P

theorem requireDrained_sameSnapshot (what : String) (queues : List Bool) :
    SameSnapshot (Env.requireDrained what queues) := by
  frame_same [Env.requireDrained] using [getDev_spec]

theorem requireDrained_spec (P : Snapshot → Prop) (what : String) (queues : List Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.requireDrained what queues
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (requireDrained_sameSnapshot what queues).wp P

theorem floodTailEffect_sameSnapshot (stop : Nat) (cuts : List Nat) (last : Option Int64) :
    SameSnapshot (Leanux.floodTailEffect stop cuts last) :=
  sameSnapshot_of_sameWGKernel (Framing.sameWGKernel_of_sameKernel (Framing.floodTailEffect_sameKernel stop cuts last))

theorem floodTailEffect_spec (P : Snapshot → Prop) (stop : Nat) (cuts : List Nat) (last : Option Int64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Leanux.floodTailEffect stop cuts last
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (floodTailEffect_sameSnapshot stop cuts last).wp P

theorem runOneSendWorker_sameSnapshot  : SameSnapshot Env.runOneSendWorker := by
  frame_same [Env.runOneSendWorker, Env.runWorker] using [getDev_spec, getPeer_spec, setPeer_spec, peekUnit_spec, resolveUnit_spec, hidden_snapshot_spec, peekHiddenSite_spec, handshakeSendWorker_spec]

theorem runOneSendWorker_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.runOneSendWorker
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (runOneSendWorker_sameSnapshot ).wp P

theorem timerCallback_ordinary (pid : PeerId) (timer : PeerTimer) : OrdinaryAction (WG.timerCallback pid timer) := by
  frame_ordinary [WG.timerCallback] using [expiredRetransmitHandshake_spec, expiredNewHandshake_spec, expiredZeroKeyMaterial_spec] ordinary [expiredSendKeepalive_spec, expiredSendPersistentKeepalive_spec]

theorem timerCallback_spec (P : Snapshot → Prop) (hp : Stable P) (pid : PeerId) (timer : PeerTimer) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (WG.timerCallback pid timer)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timerCallback_ordinary pid timer).wp P hp

theorem runTimerSection_ordinary (worker : Worker) (body : M Unit)
    (hb : OrdinaryAction body) : OrdinaryAction (Env.runTimerSection worker body) := by
  unfold Env.runTimerSection
  repeat' env_worker_step

theorem runTimerSection_spec (P : Snapshot → Prop) (hp : Stable P)
    (worker : Worker) (body : M Unit) (hb : OrdinaryAction body) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.runTimerSection worker body
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (runTimerSection_ordinary worker body hb).wp P hp

theorem runOneClearWorker_ordinary  : OrdinaryAction Env.runOneClearWorker := by
  unfold Env.runOneClearWorker
  repeat' first
    | (ordinary_head WG.queuedExpiredZeroKeyMaterial; exact queuedExpiredZeroKeyMaterial_ordinary _)
    | env_worker_step

theorem runOneClearWorker_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.runOneClearWorker
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (runOneClearWorker_ordinary ).wp P hp

theorem timerWorker_sameSnapshot (timer : PeerTimer) : SameSnapshot (Env.timerWorker timer) :=
  sameSnapshot_of_sameWGKernel (Framing.sameWGKernel_of_sameKernel (Framing.timerWorker_sameKernel timer))

theorem timerWorker_spec (P : Snapshot → Prop) (timer : PeerTimer) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Env.timerWorker timer)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (timerWorker_sameSnapshot timer).wp P

theorem fireTimer_ordinary (worker : Worker) (jHi : UInt64) : OrdinaryAction (Env.fireTimer worker jHi) := by
  unfold Env.fireTimer
  repeat' first
    | (ordinary_head WG.delTimer; exact (delTimer_sameSnapshot _ _).ordinary)
    | (ordinary_head WG.timerCallback; exact timerCallback_ordinary _ _)
    | (ordinary_head Env.runTimerSection; refine runTimerSection_ordinary _ _ ?_)
    | env_worker_step
  all_goals exact ordinary_throw _


theorem fireTimer_spec (P : Snapshot → Prop) (hp : Stable P) (worker : Worker) (jHi : UInt64) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Env.fireTimer worker jHi)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (fireTimer_ordinary worker jHi).wp P hp

theorem advance_sameSnapshot (ticks : Nat) : SameSnapshot (Env.advance ticks) :=
  sameSnapshot_of_sameWGKernel (Framing.sameWGKernel_of_sameKernel (Framing.advance_sameKernel ticks))

theorem advance_spec (P : Snapshot → Prop) (ticks : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Env.advance ticks)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (advance_sameSnapshot ticks).wp P

theorem requireIdleDevice_sameSnapshot  : SameSnapshot Env.requireIdleDevice := by
  frame_same [Env.requireIdleDevice] using [requireNoCryptWork_spec, getDev_spec]

theorem requireIdleDevice_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.requireIdleDevice
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (requireIdleDevice_sameSnapshot ).wp P

theorem wgUp_ordinary  : OrdinaryAction Env.wgUp := by
  frame_ordinary [Env.wgUp] using [skipCut_spec] ordinary [WGDevice.wgUp_spec]

theorem wgUp_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.wgUp
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgUp_ordinary ).wp P hp

theorem setMtu_sameSnapshot (mtu : Nat) : SameSnapshot (Env.setMtu mtu) := by
  intro w x v hr
  have he := Framing.setMtu_sameEnvScalar mtu w x v hr
  have hp := congrArg (fun k => snapshot {w with k}) he
  simpa [snapshot, Framing.envScalarView, Framing.envScalarKernel,
    Framing.envScalarDevice, Option.bind_map, Function.comp_def] using hp

theorem setMtu_spec (P : Snapshot → Prop) (mtu : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Env.setMtu mtu)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setMtu_sameSnapshot mtu).wp P

theorem routeIntoWg0_sameSnapshot  : SameSnapshot Env.routeIntoWg0 :=
  sameSnapshot_of_sameWGKernel (Framing.sameWGKernel_of_sameKernel (Framing.routeIntoWg0_sameKernel))

theorem routeIntoWg0_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.routeIntoWg0
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (routeIntoWg0_sameSnapshot ).wp P

theorem wgDown_ordinary  : OrdinaryAction Env.wgDown := by
  frame_ordinary [Env.wgDown] using [requireIdleDevice_spec, skipCut_spec] ordinary [WGDevice.wgDown_spec]

theorem wgDown_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.wgDown
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgDown_ordinary ).wp P hp

theorem wgDelete_ordinary  : OrdinaryAction Env.wgDelete := by
  frame_ordinary [Env.wgDelete] using [requireIdleDevice_spec] ordinary [WGDevice.wgDelete_spec]

theorem wgDelete_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.wgDelete
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgDelete_ordinary ).wp P hp

theorem wgDeladdr_sameSnapshot (family : Nat) : SameSnapshot (Env.wgDeladdr family) :=
  sameSnapshot_of_sameWGKernel (Framing.sameWGKernel_of_sameKernel (Framing.wgDeladdr_sameKernel family))

theorem wgDeladdr_spec (P : Snapshot → Prop) (family : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Env.wgDeladdr family)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgDeladdr_sameSnapshot family).wp P

theorem wgDelroute_sameSnapshot (family : Nat) : SameSnapshot (Env.wgDelroute family) :=
  sameSnapshot_of_sameWGKernel (Framing.sameWGKernel_of_sameKernel (Framing.wgDelroute_sameKernel family))

theorem wgDelroute_spec (P : Snapshot → Prop) (family : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Env.wgDelroute family)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgDelroute_sameSnapshot family).wp P

theorem netnsCleanup_sameSnapshot  : SameSnapshot Env.netnsCleanup := by
  frame_same [Env.netnsCleanup, Env.runWorker] using [peekUnit_spec, resolveUnit_spec, hidden_snapshot_spec, peekHiddenSite_spec, netnsPreExit_spec, skipCut_spec]

theorem netnsCleanup_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ Env.netnsCleanup
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (netnsCleanup_sameSnapshot ).wp P

theorem xmitPacket_sameSnapshot (family addr : Nat) (payload : List UInt8) (mtu tos : Nat) : SameSnapshot (Env.xmitPacket family addr payload mtu tos) :=
  sameSnapshot_of_sameWGKernel (Framing.sameWGKernel_of_sameKernel (Framing.xmitPacket_sameKernel family addr payload mtu tos))

theorem xmitPacket_spec (P : Snapshot → Prop) (family addr : Nat) (payload : List UInt8) (mtu tos : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Env.xmitPacket family addr payload mtu tos)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (xmitPacket_sameSnapshot family addr payload mtu tos).wp P

theorem xmitPackets_sameSnapshot (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) : SameSnapshot (Env.xmitPackets family addr payload opts) :=
  sameSnapshot_of_sameWGKernel (Framing.sameWGKernel_of_sameKernel (Framing.xmitPackets_sameKernel family addr payload opts))

theorem xmitPackets_spec (P : Snapshot → Prop) (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Env.xmitPackets family addr payload opts)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (xmitPackets_sameSnapshot family addr payload opts).wp P

theorem xmitMulticastLoop_sameSnapshot (family addr : Nat) : SameSnapshot (Env.xmitMulticastLoop family addr) := by
  frame_same [Env.xmitMulticastLoop] using [loopbackSend_spec]

theorem xmitMulticastLoop_spec (P : Snapshot → Prop) (family addr : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (Env.xmitMulticastLoop family addr)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (xmitMulticastLoop_sameSnapshot family addr).wp P

end Leanux.Proofs.WG.Keypairs.EnvFrames
