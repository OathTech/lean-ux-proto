import Leanux.Proofs.WG.AllowedIps.RoutingHandshakeFrames

/-! Concrete original inline flushes preserve routing while permitting resident
peer deletion. The finite drain's exhaustion and record failures remain Stops;
no progress, reference-credit or worker-affiliation premise is imposed. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1200000
set_option pp.structureInstances false

theorem runFlushedSendWork_routing (pid : PeerId) : RetainsRoutingCall (runFlushedSendWork pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hm := (modifyDev_routing (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}) (fun _ => rfl)).wp P
  have hh := fun site => (routing_kernel _ (hidden_sameKernel site)).wp P
  have hw := (handshakeSendWorker_routing pid).wp s
  mvcgen [runFlushedSendWork, hg, hs, hm, hh, hw, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem runFlushedClearWork_routing (pid : PeerId) : RetainsRoutingCall (runFlushedClearWork pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hm := (modifyDev_routing (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) (fun _ => rfl)).wp (RetainsRouting s)
  have hh := fun site => (routing_kernel _ (hidden_sameKernel site)).wp (RetainsRouting s)
  have hw := (queuedExpiredZeroKeyMaterial_routing pid).wp s
  mvcgen [runFlushedClearWork, hm, hh, hw]
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem drainHandshakeSendWq_routing (upTo : Option PeerId) : RetainsRoutingCall (drainHandshakeSendWq upTo) := by
  apply ProjectedAction.of_wp
  intro s
  have hs := fun pid => (runFlushedSendWork_routing pid).wp s
  have hc := fun pid => (runFlushedClearWork_routing pid).wp s
  have hp := fun worker => (routing_kernel _ (Framing.peekUnit_sameKernel worker)).wp (RetainsRouting s)
  have hr := fun worker unit queue => (routing_kernel _ (Framing.resolveUnit_sameKernel worker unit queue)).wp (RetainsRouting s)
  mvcgen [drainHandshakeSendWq, hs, hc, hp, hr, getDev, getK, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals try assumption
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem timersStop_routing (pid : PeerId) : RetainsRoutingCall (timersStop pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hd := fun t => (delTimer_routing pid t).wp (RetainsRouting s)
  have hw := (drainHandshakeSendWq_routing (some pid)).wp s
  mvcgen [timersStop, hd, hw, getDev, getK, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem peerRemoveAfterDead_routing (pid : PeerId) : RetainsRoutingCall (peerRemoveAfterDead pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hg := (getPeer_routing pid).wp (RetainsRouting s)
  have hk := (keypairsClear_routing pid).wp (RetainsRouting s)
  have ht := (timersStop_routing pid).wp s
  have hw := (drainHandshakeSendWq_routing none).wp s
  have hm := (modifyDev_routing (fun d => {d with numPeers := d.numPeers - 1}) (fun _ => rfl)).wp (RetainsRouting s)
  have hp := (peerPut_retainsRouting (some pid)).wp s
  mvcgen [peerRemoveAfterDead, hg, hk, ht, hw, hm, hp, getDev, getK, branch, unsupported, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsRouting.refl _

end Leanux.Proofs.WG.AllowedIps
