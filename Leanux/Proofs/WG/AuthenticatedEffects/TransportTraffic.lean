import Leanux.Proofs.WG.AuthenticatedEffects.TransportDeferred
import Leanux.Proofs.WG.Packets.PublicationTraffic
import Leanux.Proofs.WG.Origins.OwnerTraffic

/-! Actual batch and traffic callers carry the joint publication checks.
Ingress uses the exact native receive contract; each scheduler, worker and
inline poll keeps the committed journal and all prefixes emitted before Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportTraffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins CurrentEnvironment

private theorem lift_store (a : Leanux.M α) (frame : SameProductStore a) :
    TransportChecks.Preserves (liftPrefix a) := TransportChecks.lift_store a frame

private theorem multicast (family addr : Nat) :
    TransportChecks.Preserves (RxHistory.audit (xmitMulticastLoopAudit family addr)) :=
  TransportChecks.audit _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTraffic.«0».Leanux.Proofs.WG.PublicationTraffic.multicast) family addr)

/-- The body remains an arbitrary product observer with its explicit contract. -/
theorem runWorker (worker : Worker) (body : RxHistory.Obs Unit)
    (hb : TransportChecks.Preserves body) : TransportChecks.Preserves (runWorkerPrefix worker body) :=
  runWorkerPrefix_preserves (fun _ _ hi => hi.2) TransportChecks.store worker hb

theorem handshakeReceiveWorker : TransportChecks.Preserves RxHistory.handshakeReceiveWorker :=
  workerLoopPrefix_preserves _ _ (fun _ _ hi => hi.2)
    TransportChecks.receiveStep (TransportChecks.nestedResched _) _ _

private theorem receive (msg : List UInt8) (src : SkbSource) :
    TransportChecks.Preserves (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  TransportChecks.mixed _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTraffic.«0».Leanux.Proofs.WG.PublicationTraffic.receive) msg src)

private theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    TransportChecks.Preserves (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  TransportChecks.mixed _ ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTraffic.«0».Leanux.Proofs.WG.PublicationTraffic.transmit) family addr packets mtu)

macro "transport_traffic_steps" : tactic => `(tactic| first
  | unfold TransportChecks.Preserves
  | (current_env_at wgReceivePrefix; exact receive _ _)
  | (current_env_at wgXmitPrefix; exact transmit _ _ _ _)
  | (environment_at "xmitMulticastLoopAudit"; exact multicast _ _)
  | (current_env_at RxHistory.runCryptWorkers; exact TransportDeferred.runCryptWorkers)
  | (current_env_at RxHistory.runSendWorkers; exact TransportDeferred.runSendWorkers)
  | (current_env_at RxHistory.schedule; exact TransportChecks.schedule _)
  | (current_env_at RxHistory.pollScheduledInline; exact TransportChecks.pollScheduledInline)
  | (current_env_at runWorkerPrefix; apply runWorker)
  | (current_env_at requireNotPending
     exact lift_store _ (liftWG_sameProductStore _ (SameView.pure _ _)))
  | (current_env_at Env.fixtureSend
     exact lift_store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (current_env_at getRouting
     exact lift_store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
  | (current_env_at Env.senderSource; exact lift_store _ (senderSource_sameKernel _ _ _ _))
  | (current_env_at Env.xmitPackets; exact lift_store _ (xmitPackets_sameKernel _ _ _ _))
  | (current_env_at liftM
     exact lift_store _ (fun initial => productRouting_spec _ (fun s => s = initial)))
  | (current_env_at ite; apply PrefixPreserves.ite)
  | transport_deferred_timer_steps)

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    TransportChecks.Preserves (RxHistory.inject family port msg tos ll dest) := by
  change PrefixPreserves TransportChecks.Inv TransportChecks.Safe _
  unfold RxHistory.inject
  repeat' transport_traffic_steps

theorem afterBatch : TransportChecks.Preserves RxHistory.afterBatch := by
  change PrefixPreserves TransportChecks.Inv TransportChecks.Safe _
  unfold RxHistory.afterBatch
  repeat' transport_traffic_steps

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    TransportChecks.Preserves (RxHistory.flood count port family messages) := by
  change PrefixPreserves TransportChecks.Inv TransportChecks.Safe _
  unfold RxHistory.flood
  repeat' first
    | (current_env_at RxHistory.afterBatch; exact afterBatch)
    | transport_traffic_steps

theorem batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    TransportChecks.Preserves (RxHistory.batchItem d cqes item) := by
  change PrefixPreserves TransportChecks.Inv TransportChecks.Safe _
  unfold RxHistory.batchItem
  repeat' transport_traffic_steps

theorem batch (items : List Env.BatchItem) : TransportChecks.Preserves (RxHistory.batch items) := by
  change PrefixPreserves TransportChecks.Inv TransportChecks.Safe _
  unfold RxHistory.batch
  repeat' first
    | (current_env_at RxHistory.afterBatch; exact afterBatch)
    | (current_env_at RxHistory.batchItem; exact batchItem _ _ _)
    | transport_traffic_steps

end Leanux.Proofs.WG.AuthenticatedEffects.TransportTraffic
