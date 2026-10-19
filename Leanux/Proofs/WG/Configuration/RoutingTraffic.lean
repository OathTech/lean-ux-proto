import Leanux.Proofs.WG.Configuration.RoutingDeferred
import Leanux.Proofs.WG.Queues.RxEnvControlsHistory

/-! Original traffic callers transport positional routing through actual
receive, scheduler and poll cuts, retaining arbitrary input histories. -/
namespace Leanux.Proofs.WG.RoutingPosition.Traffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AllowedIps Origins RoutingPosition.Callers

private theorem multicast (initial : FlatTable × FlatTable) (family addr : Nat) :
    Focused initial (RxHistory.audit (xmitMulticastLoopAudit family addr)) :=
  audit initial _ _ (xmitMulticastLoopAudit_erases family addr) (ProjectedRetainsRoutingCall.of_same (xmitMulticastLoop_routing family addr))

macro "routing_traffic_steps " initial:term : tactic => `(tactic| first
  | (routing_env_at wgReceivePrefix
     exact native_mixed $initial _ _ (wgReceivePrefix_erases _ _) (wgReceive_routing _ _))
  | (routing_env_at wgXmitPrefix
     exact native_mixed $initial _ _ (wgXmitPrefix_erases _ _ _ _) (wgXmit_routing _ _ _ _))
  | (routing_deferred_audit_at xmitMulticastLoopAudit; exact multicast $initial _ _)
  | (routing_env_at RxHistory.runCryptWorkers; exact Deferred.runCryptWorkers $initial)
  | (routing_env_at RxHistory.runSendWorkers; exact Deferred.runSendWorkers $initial)
  | (routing_env_at RxHistory.schedule; exact Environment.schedule $initial _)
  | (routing_env_at RxHistory.pollScheduledInline; exact Callers.pollScheduledInline $initial)
  | (routing_env_at runWorkerPrefix; apply Callers.runWorker $initial)
  | (routing_env_at requireNotPending
     exact store $initial _ (liftWG_sameProductStore _ (SameView.pure _ _)))
  | (routing_env_at Env.fixtureSend
     exact store $initial _ (fun state => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (routing_env_at Env.peekNextSite; exact store $initial _ peekNextSite_sameKernel)
  | (routing_env_at getEnv
     exact store $initial _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
  | (routing_env_at getRouting
     exact store $initial _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
  | (routing_env_at Env.senderSource; exact store $initial _ (senderSource_sameKernel _ _ _ _))
  | (routing_env_at Env.xmitPackets; exact store $initial _ (xmitPackets_sameKernel _ _ _ _))
  | (routing_env_at liftM
     exact store $initial _ (fun state => productRouting_spec _ (fun s => s = state)))
  | (routing_env_at Net.Fib.inSocketNs
     exact store $initial _ (fun state => productRouting_spec _ (fun s => s = state)))
  | routing_focus_join
  | routing_focus_join_use
  | routing_focus_reduce
  | routing_deferred_steps $initial)

theorem inject (initial : FlatTable × FlatTable) (family port : Nat)
    (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Focused initial (RxHistory.inject family port msg tos ll dest) := by
  unfold RxHistory.inject
  repeat' routing_traffic_steps initial

theorem afterBatch (initial : FlatTable × FlatTable) : Focused initial RxHistory.afterBatch := by
  unfold RxHistory.afterBatch
  repeat' routing_traffic_steps initial

theorem flood (initial : FlatTable × FlatTable) (count port family : Nat)
    (messages : List (List UInt8)) : Focused initial (RxHistory.flood count port family messages) := by
  unfold RxHistory.flood
  repeat' first
    | (routing_env_at RxHistory.afterBatch; exact afterBatch initial)
    | routing_traffic_steps initial

theorem batchItem (initial : FlatTable × FlatTable) (d : Device) (cqes : List Int)
    (item : Env.BatchItem) : Focused initial (RxHistory.batchItem d cqes item) := by
  unfold RxHistory.batchItem
  repeat' routing_traffic_steps initial

theorem batch (initial : FlatTable × FlatTable) (items : List Env.BatchItem) :
    Focused initial (RxHistory.batch items) := by
  unfold RxHistory.batch
  repeat' first
    | (routing_env_at RxHistory.afterBatch; exact afterBatch initial)
    | (routing_env_at RxHistory.batchItem; exact batchItem initial _ _ _)
    | routing_traffic_steps initial

theorem observe (initial : FlatTable × FlatTable) : Focused initial RxHistory.observe :=
  bind initial _ _ (Deferred.idleTimers initial) (fun _ => store initial _ observeTail_sameKernel)

end Leanux.Proofs.WG.RoutingPosition.Traffic
