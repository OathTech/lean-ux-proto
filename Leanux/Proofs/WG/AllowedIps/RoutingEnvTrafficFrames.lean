import Leanux.Proofs.WG.AllowedIps.RoutingEnvTimersFrames
import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.WG.Environment.BatchSource

/-! Original environment ingress, both flood modes and batch submission retain
routing at normal endpoints. Concrete nested scheduling closes the full receive
worker. Saved device scalars and lists need no current-device equality premise;
all actual getters, record failures and finite exhaustion remain unchanged. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem wgKernel_routing (a : M α) (ha : SameWGKernel a) : SameView routingView a :=
  ha.of_factor (fun k => k.wg.map routingState) routingView (fun _ => rfl)

private theorem workerLoop_routing (worker : Worker) (pid : Option Nat)
    (step : M Bool) (afterItem : M Unit) (bound : Nat) (drained : String)
    (hs : RetainsRoutingCall step) (ha : RetainsRoutingCall afterItem) :
    RetainsRoutingCall (workerLoop worker pid step afterItem bound drained) := by
  have hafter : RetainsRoutingCall (do afterItem; pure false) := by
    apply ProjectedAction.of_wp
    intro s
    have h := ha.wp s
    mvcgen [h]
    subst s
    exact RetainsRouting.refl _
  apply ProjectedAction.of_wp
  intro s
  have hi := (workerIter_routing worker pid step _ hs hafter).wp s
  mvcgen [workerLoop, hi, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try trivial
  all_goals try exact id
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem handshakeReceiveWorker_routing :
    RetainsRoutingCall (handshakeReceiveWorker (Env.nestedResched .receiveWorker)) :=
  workerLoop_routing _ _ _ _ _ _ receiveStep_routing (nestedResched_routing .receiveWorker)

theorem xmitMulticastLoop_routing (family addr : Nat) :
    SameView routingView (Env.xmitMulticastLoop family addr) := by
  apply SameView.of_wp
  intro s
  have hl := (routing_kernel _ (Queues.loopbackSend_kernel [] true)).wp (fun t => t = s)
  mvcgen [Env.xmitMulticastLoop, hl, unsupported]

theorem inject_routing (family port : Nat) (msg : List UInt8) (tos : Nat)
    (ll : Bool) (dest : Nat) : RetainsRoutingCall (Env.inject family port msg tos ll dest) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hn := fun pid => (requireNotPending_routing pid "receiving while a handshake is queued").wp P
  have hf := (routing_kernel _ fixtureSend_sameKernel).wp P
  have hs := (routing_kernel _ (senderSource_sameKernel family dest tos ll)).wp P
  have hw := fun src => (runWorker_routing .netRx _ (wgReceive_routing msg src)).wp s
  have hc := runCryptWorkers_routing.wp s
  have hd := fun queues => (requireDrained_routing "the datagram queued" queues).wp P
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    Env.inject, hn, hf, hs, hw, hc, hd, getDev, getK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try trivial
  all_goals try exact id
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem flood_routing (count port family : Nat) (messages : List (List UInt8)) :
    RetainsRoutingCall (Env.flood count port family messages) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hd := fun stop cuts => (wgKernel_routing _ (KernelFrames.discardFloodRecords_sameWGKernel stop cuts)).wp P
  have hh := fun site => (routing_kernel _ (hidden_sameKernel site)).wp P
  have hs := (routing_kernel _ (senderSource_sameKernel family 0 0 false)).wp P
  have hw := handshakeReceiveWorker_routing.wp s
  have hf := fun stop cuts last => (routing_kernel _ (floodTailEffect_sameKernel stop cuts last)).wp P
  have he := deliverSent_routing.wp P
  have hm := fun (msgs : List (List UInt8)) (src : SkbSource) n m => (modifyDev_routing
    (fun d => {d with handshakeQueue := msgs.map (fun x => (x, src)), handshakeQueueLen := d.handshakeQueueLen + n + m, handshakeLastCpu := 0}) (fun _ => rfl)).wp P
  have hz := (modifyDev_routing (fun d => {d with handshakeQueueLen := 0}) (fun _ => rfl)).wp P
  mvcgen [Env.flood, hd, hh, hs, hw, hf, he, hm, hz, getK, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try trivial
  all_goals try exact id
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem afterBatch_routing : RetainsRoutingCall Env.afterBatch := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hc := runCryptWorkers_routing.wp s
  have hs := runSendWorkers_routing.wp s
  have hw := runOneSendWorker_routing.wp s
  have hsc := (schedule_routing none).wp s
  have hb := (routing_kernel _ recordBudget_sameKernel).wp P
  have hp := (routing_kernel _ peekNextSite_sameKernel).wp P
  have hd := fun qs => (requireDrained_routing "the batch queued" qs).wp P
  have he := deliverSent_routing.wp P
  mvcgen [Env.afterBatch, hc, hs, hw, hsc, hb, hp, hd, he, getDev, getK, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try trivial
  all_goals try exact id
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem batchItem_routing (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    RetainsRoutingCall (Environment.batchItemSource d cqes item) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hf := (routing_kernel _ fixtureSend_sameKernel).wp P
  have hs := fun family => (routing_kernel _ (senderSource_sameKernel family 0 0 false)).wp P
  have hw (msg src) : RetainsRoutingCall (Env.runWorker .netRx (do wgReceive msg src; Env.pollScheduledInline)) := by
    apply runWorker_routing
    apply ProjectedAction.of_wp
    intro t
    have hr := (wgReceive_routing msg src).wp t
    have hp := pollScheduledInline_routing.wp t
    mvcgen [hr, hp]
    subst t
    exact RetainsRouting.refl _
  have hwp := fun msg src => (hw msg src).wp s
  have hl := fun family addr => (routing_kernel _ (routeLookup_sameKernel family 0 addr)).wp P
  have hx := fun family addr payload opts => (routing_kernel _ (xmitPackets_sameKernel family addr payload opts)).wp P
  have hm := fun family addr => (xmitMulticastLoop_routing family addr).wp P
  have ht := fun family addr pkts mtu => (wgXmit_routing family addr pkts mtu).wp s
  mvcgen [Environment.batchItemSource, hf, hs, hwp, hl, hx, hm, ht, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem batch_routing (items : List Env.BatchItem) : RetainsRoutingCall (Env.batch items) := by
  rw [← Environment.batchSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hn := fun pid => (requireNotPending_routing pid "a batch while a handshake is queued").wp P
  have hi := fun d cqes item => (batchItem_routing d cqes item).wp s
  have ha := afterBatch_routing.wp s
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    Environment.batchSource, hn, hi, ha, getK, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try trivial
  all_goals try exact id
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

end Leanux.Proofs.WG.AllowedIps
