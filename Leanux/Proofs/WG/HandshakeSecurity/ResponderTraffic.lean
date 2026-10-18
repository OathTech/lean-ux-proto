import Leanux.Proofs.WG.HandshakeSecurity.ResponderControls

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Traffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins CurrentEnvironment

private theorem lift_store (a : Leanux.M α) (frame : SameProductStore a) :
    Joint.Preserves (liftPrefix a) := Joint.lift_store a frame

theorem pollScheduledInline (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) :
    Joint.Preserves RxHistory.pollScheduledInline :=
  Joint.from_global _ PublicationJoint.pollScheduledInline (Global.pollScheduledInline H1 slots)

theorem multicast (family addr : Nat) :
    Joint.Preserves (RxHistory.audit (xmitMulticastLoopAudit family addr)) := by
  apply Joint.from_global _
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTraffic.«0».Leanux.Proofs.WG.PublicationTraffic.multicast) family addr)
  apply Global.audited _ _ (xmitMulticastLoopAudit_erases family addr)
  intro confirmed
  have loop : Framing.Preserves (AuditedFrames.State confirmed)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (native_store (loopbackSend_kernel [] true) confirmed)
  have ambient {α : Type} (a : AmbientM α) := AuditedFrames.ambient a confirmed
  routing_tx_source [Env.xmitMulticastLoop] using [loop,ambient]

theorem runWorker (worker : Worker) (body : RxHistory.Obs Unit)
    (hb : Joint.Preserves body) : Joint.Preserves (runWorkerPrefix worker body) :=
  runWorkerPrefix_preserves (fun _ _ hi => hi.safe) Joint.store worker hb

theorem handshakeReceiveWorker (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) : Joint.Preserves RxHistory.handshakeReceiveWorker :=
  workerLoopPrefix_preserves _ _ (fun _ _ hi => hi.safe)
    (Joint.receiveStep H1) (Joint.nestedResched H1 slots _) _ _

macro "responder_traffic_steps " H1:term:max slots:term:max : tactic => `(tactic| first
  | unfold Joint.Preserves
  | (current_env_at wgReceivePrefix; exact Joint.ingress _ _)
  | (current_env_at wgXmitPrefix; exact Joint.transmit _ _ _ _)
  | (environment_at "xmitMulticastLoopAudit"; exact multicast _ _)
  | (current_env_at RxHistory.runCryptWorkers; exact Deferred.runCryptWorkers $H1 $slots)
  | (current_env_at RxHistory.runSendWorkers; exact Deferred.runSendWorkers $H1 $slots)
  | (current_env_at RxHistory.schedule; exact Joint.schedule $H1 $slots _)
  | (current_env_at RxHistory.pollScheduledInline; exact pollScheduledInline $H1 $slots)
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
  | responder_deferred_timer_steps $H1)

theorem inject (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Joint.Preserves (RxHistory.inject family port msg tos ll dest) := by
  change PrefixPreserves Joint.Inv Joint.Safe _
  unfold RxHistory.inject
  repeat' responder_traffic_steps H1 slots

theorem afterBatch (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) : Joint.Preserves RxHistory.afterBatch := by
  change PrefixPreserves Joint.Inv Joint.Safe _
  unfold RxHistory.afterBatch
  repeat' responder_traffic_steps H1 slots

theorem flood (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (count port family : Nat) (messages : List (List UInt8)) :
    Joint.Preserves (RxHistory.flood count port family messages) := by
  change PrefixPreserves Joint.Inv Joint.Safe _
  unfold RxHistory.flood
  repeat' first
    | (current_env_at RxHistory.afterBatch; exact afterBatch H1 slots)
    | responder_traffic_steps H1 slots

theorem batchItem (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    Joint.Preserves (RxHistory.batchItem d cqes item) := by
  change PrefixPreserves Joint.Inv Joint.Safe _
  unfold RxHistory.batchItem
  repeat' responder_traffic_steps H1 slots

theorem batch (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges) (items : List Env.BatchItem) : Joint.Preserves (RxHistory.batch items) := by
  change PrefixPreserves Joint.Inv Joint.Safe _
  unfold RxHistory.batch
  repeat' first
    | (current_env_at RxHistory.afterBatch; exact afterBatch H1 slots)
    | (current_env_at RxHistory.batchItem; exact batchItem H1 slots _ _ _)
    | responder_traffic_steps H1 slots


end Leanux.Proofs.WG.HandshakeSecurity.Responder.Traffic
