import Leanux.Proofs.WG.Packets.PublicationDeferred
import Leanux.Proofs.WG.Packets.PublicationReceive
import Leanux.Proofs.WG.Origins.OwnerTraffic

/-! Actual batch and traffic callers carry the joint publication checks.
Ingress uses the exact native receive contract; each scheduler, worker and
inline poll keeps the committed journal and all prefixes emitted before Stop. -/
namespace Leanux.Proofs.WG.PublicationTraffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins CurrentEnvironment

private theorem lift_store (a : Leanux.M α) (frame : SameProductStore a) :
    PublicationJoint.Preserves (liftPrefix a) := PublicationJoint.lift_store a frame

private theorem multicast (family addr : Nat) :
    PublicationJoint.Preserves (RxHistory.audit (xmitMulticastLoopAudit family addr)) := by
  apply PublicationJoint.combine _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerTraffic.«0».Leanux.Proofs.WG.OwnerTraffic.multicast) family addr)
  apply PublicationAudited.source _ _ (xmitMulticastLoopAudit_erases family addr)
  intro history
  have loop : Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (PublicationFrontier.store_preserves (loopbackSend_kernel [] true) history)
  have ambient {α : Type} (a : AmbientM α) :
      Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  routing_tx_source [Env.xmitMulticastLoop] using [loop,ambient]

/-- The body remains an arbitrary product observer with its explicit contract. -/
theorem runWorker (worker : Worker) (body : RxHistory.Obs Unit)
    (hb : PublicationJoint.Preserves body) : PublicationJoint.Preserves (runWorkerPrefix worker body) :=
  runWorkerPrefix_preserves (fun _ _ hi => hi.safe) PublicationJoint.store worker hb

theorem handshakeReceiveWorker : PublicationJoint.Preserves RxHistory.handshakeReceiveWorker :=
  workerLoopPrefix_preserves _ _ (fun _ _ hi => hi.safe)
    PublicationJoint.receiveStep (PublicationJoint.nestedResched _) _ _

private theorem receive (msg : List UInt8) (src : SkbSource) :
    PublicationJoint.Preserves (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  PublicationJoint.native_mixed _ _ (OwnerReceive.wgReceive_checked msg src)
    (wgReceivePrefix_erases msg src) (PublicationFrontier.wgReceive_preserves msg src)

private theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    PublicationJoint.Preserves (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  PublicationJoint.native_mixed _ _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerTraffic.«0».Leanux.Proofs.WG.OwnerTraffic.transmit) family addr packets mtu)
    (wgXmitPrefix_erases family addr packets mtu) (PublicationFrontier.wgXmit_preserves family addr packets mtu)

macro "publication_traffic_steps" : tactic => `(tactic| first
  | unfold PublicationJoint.Preserves
  | (current_env_at wgReceivePrefix; exact receive _ _)
  | (current_env_at wgXmitPrefix; exact transmit _ _ _ _)
  | (environment_at "xmitMulticastLoopAudit"; exact multicast _ _)
  | (current_env_at RxHistory.runCryptWorkers; exact PublicationDeferred.runCryptWorkers)
  | (current_env_at RxHistory.runSendWorkers; exact PublicationDeferred.runSendWorkers)
  | (current_env_at RxHistory.schedule; exact PublicationJoint.schedule _)
  | (current_env_at RxHistory.pollScheduledInline; exact PublicationJoint.pollScheduledInline)
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
  | publication_deferred_timer_steps)

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PublicationJoint.Preserves (RxHistory.inject family port msg tos ll dest) := by
  change PrefixPreserves PublicationJoint.Inv PublicationJoint.Safe _
  unfold RxHistory.inject
  repeat' publication_traffic_steps

theorem afterBatch : PublicationJoint.Preserves RxHistory.afterBatch := by
  change PrefixPreserves PublicationJoint.Inv PublicationJoint.Safe _
  unfold RxHistory.afterBatch
  repeat' publication_traffic_steps

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    PublicationJoint.Preserves (RxHistory.flood count port family messages) := by
  change PrefixPreserves PublicationJoint.Inv PublicationJoint.Safe _
  unfold RxHistory.flood
  repeat' first
    | (current_env_at RxHistory.afterBatch; exact afterBatch)
    | publication_traffic_steps

theorem batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    PublicationJoint.Preserves (RxHistory.batchItem d cqes item) := by
  change PrefixPreserves PublicationJoint.Inv PublicationJoint.Safe _
  unfold RxHistory.batchItem
  repeat' publication_traffic_steps

theorem batch (items : List Env.BatchItem) : PublicationJoint.Preserves (RxHistory.batch items) := by
  change PrefixPreserves PublicationJoint.Inv PublicationJoint.Safe _
  unfold RxHistory.batch
  repeat' first
    | (current_env_at RxHistory.afterBatch; exact afterBatch)
    | (current_env_at RxHistory.batchItem; exact batchItem _ _ _)
    | publication_traffic_steps

end Leanux.Proofs.WG.PublicationTraffic
