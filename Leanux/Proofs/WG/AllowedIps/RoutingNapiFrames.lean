import Leanux.Proofs.WG.AllowedIps.RoutingAdmissionFrames
import Leanux.Proofs.Framing.Batch
import Leanux.Proofs.WG.Lifetimes.BatchNapi

/-! Concrete NET_RX and crypt-worker callbacks. The original captured pending
list, ambiguity choice, records and unsupported cases remain intact. These
normal-endpoint frames permit deletion and require no resident-list premise. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem runWorker_routing (worker : Worker) (body : M Unit)
    (hb : RetainsRoutingCall body) : RetainsRoutingCall (Env.runWorker worker body) := by
  apply ProjectedAction.of_wp
  intro s
  have hbody := hb.wp s
  have hh := fun site => (routing_kernel _ (hidden_sameKernel site)).wp (RetainsRouting s)
  mvcgen [Env.runWorker, hbody, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

private theorem pendingPolls_routing (pending : List PeerId) :
    RetainsRoutingCall (do
      for pid in pending do
        discard <| rxPoll pid NAPI_POLL_WEIGHT (fun xs => xs.forM Env.deliverInner)) := by
  apply ProjectedAction.of_wp
  intro s
  have hp := fun pid => (actualRxPoll_routing pid NAPI_POLL_WEIGHT).wp s
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) (RetainsRouting s)
  have hd (α : Type) := discard_view_spec routingView (α := α) (RetainsRouting s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hd, hp]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem napiSoftirq_routing : RetainsRoutingCall Env.napiSoftirq := by
  apply ProjectedAction.of_wp
  intro s
  have hw := fun pending => (runWorker_routing .netRx _ (pendingPolls_routing pending)).wp s
  have hh := (routing_kernel _ peekHiddenSite_sameKernel).wp (RetainsRouting s)
  mvcgen [Env.napiSoftirq, hw, hh, getDev, getK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

/-- The second actual direct poll site runs without opening a new section. -/
theorem pollScheduledInline_routing : RetainsRoutingCall Env.pollScheduledInline := by
  apply ProjectedAction.of_wp
  intro s
  have hp := fun pid => (actualRxPoll_routing pid NAPI_POLL_WEIGHT).wp s
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) (RetainsRouting s)
  have hd (α : Type) := discard_view_spec routingView (α := α) (RetainsRouting s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hd,
    Env.pollScheduledInline, hp, getDev, getK, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem napiIrqExit_routing : RetainsRoutingCall Env.napiIrqExit := by
  rw [← napiIrqExitSource_eq]
  apply ProjectedAction.of_wp
  intro s
  have hn := napiSoftirq_routing.wp s
  have hc := (routing_kernel _ chooseNapiHere_sameKernel).wp (RetainsRouting s)
  have hh := (routing_kernel _ peekHiddenSite_sameKernel).wp (RetainsRouting s)
  mvcgen [napiIrqExitSource, hn, hc, hh, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem actualEncryptStep_routing : RetainsRoutingCall (encryptStep Env.checksumHelp Env.napiSoftirq) :=
  encryptStep_routing _ _ actualChecksum_routing napiSoftirq_routing

theorem actualEncryptIter_routing :
    RetainsRoutingCall (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
  encryptIter_routing _ _ _ actualChecksum_routing napiSoftirq_routing
    (.of_same (routing_kernel _ (Framing.condResched_sameKernel .encryptWorker)))

theorem actualDecryptStep_routing : RetainsRoutingCall (decryptStep Env.napiSoftirq Env.napiIrqExit) :=
  decryptStep_routing _ _ napiSoftirq_routing napiIrqExit_routing

theorem actualDecryptIter_routing :
    RetainsRoutingCall (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
  decryptIter_routing _ _ _ napiSoftirq_routing napiIrqExit_routing
    (.of_same (routing_kernel _ (Framing.condResched_sameKernel .decryptWorker)))

theorem actualTxIter_routing (pid : PeerId) : RetainsRoutingCall (txIter pid (Env.condResched .txWorker)) :=
  txIter_routing _ _ (.of_same (routing_kernel _ (Framing.condResched_sameKernel .txWorker)))

end Leanux.Proofs.WG.AllowedIps
