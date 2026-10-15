import Leanux.Proofs.WG.AllowedIps.RoutingSchedulerFrames
import Leanux.Proofs.Framing.EnvLeaves
import Leanux.Proofs.WG.Keypairs.Frames.Env

/-! Deferred environment workers retain routing at every normal endpoint.
The captured work queues do not imply residency: original getters establish
fresh setter facts or Stop, and worker cleanup may delete resident peers. The
legacy environment import shares generated matcher declarations under Lean 4.35. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem deliverSent_routing : SameView routingView Env.deliverSent :=
  routing_kernel _ deliverSent_sameKernel

theorem requireNoCryptWork_routing : SameView routingView Env.requireNoCryptWork :=
  routing_kernel _ requireNoCryptWork_sameKernel

theorem requireDrained_routing (what : String) (queues : List Bool) :
    SameView routingView (Env.requireDrained what queues) := by
  apply SameView.of_wp
  intro s
  mvcgen [Env.requireDrained, getDev, getK, invariant, unsupported]

theorem runCryptWorkers_routing : RetainsRoutingCall Env.runCryptWorkers := by
  apply ProjectedAction.of_wp
  intro s
  have hs := (schedule_routing none).wp s
  have hd := deliverSent_routing.wp (RetainsRouting s)
  mvcgen [Env.runCryptWorkers, hs, hd]
  subst s
  exact RetainsRouting.refl _

theorem runOneSendWorker_routing : RetainsRoutingCall Env.runOneSendWorker := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hp := (routing_kernel _ (peekUnit_sameKernel .sendWorker)).wp P
  have hr := fun unit queue => (routing_kernel _ (resolveUnit_sameKernel .sendWorker unit queue)).wp P
  have hm := fun pid => (modifyDev_routing (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}) (fun _ => rfl)).wp P
  have hg := fun pid => routing_getPeer P pid
  have hs := fun pid p => routing_setPeer P pid p
  have hw := fun pid => (runWorker_routing .sendWorker _ (handshakeSendWorker_routing pid)).wp s
  mvcgen [Env.runOneSendWorker, hp, hr, hm, hg, hs, hw, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try trivial
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem runOneClearWorker_routing : RetainsRoutingCall Env.runOneClearWorker := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hp := (routing_kernel _ (peekUnit_sameKernel .clearPeerWorker)).wp P
  have hr := fun unit queue => (routing_kernel _ (resolveUnit_sameKernel .clearPeerWorker unit queue)).wp P
  have hm := fun pid => (modifyDev_routing (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) (fun _ => rfl)).wp P
  have hw := fun pid => (runWorker_routing .clearPeerWorker _ (queuedExpiredZeroKeyMaterial_routing pid)).wp s
  mvcgen [Env.runOneClearWorker, hp, hr, hm, hw, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try trivial
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem runSendWorkers_routing : RetainsRoutingCall Env.runSendWorkers := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hn := requireNoCryptWork_routing.wp P
  have hd := deliverSent_routing.wp P
  have hw := runOneSendWorker_routing.wp s
  have hs := (schedule_routing none).wp s
  have hb := (routing_kernel _ recordBudget_sameKernel).wp P
  have he := (routing_kernel _ (budgetExhausted_sameKernel (α := Unit) "the send work queue")).wp P
  mvcgen [Env.runSendWorkers, hn, hd, hw, hs, hb, he, getDev, getK, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try trivial
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem afterXmit_routing : RetainsRoutingCall Env.afterXmit := by
  apply ProjectedAction.of_wp
  intro s
  have hc := runCryptWorkers_routing.wp s
  have hs := runSendWorkers_routing.wp s
  have hd := fun what queues => (requireDrained_routing what queues).wp (RetainsRouting s)
  mvcgen [Env.afterXmit, hc, hs, hd, getDev, getK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView]
  all_goals try trivial
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

end Leanux.Proofs.WG.AllowedIps
