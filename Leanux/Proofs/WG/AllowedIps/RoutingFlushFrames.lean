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
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) Q (fun _ w => Q w) :=
    hoare_liftAmbient a Q
  unfold Hoare at ambient
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hm := (modifyDev_routing (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}) (fun _ => rfl)).wp P
  have hw := RetainsRoutingCall.wp (handshakeSendWorker_routing pid) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, getDev, getAmbient, hidden, peekUnit, resolveUnit, invariant, unsupported, branch, AmbientM.invariant, AmbientM.unsupported, AmbientM.branch, runFlushedSendWork, hg, hs, hm, hw, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem runFlushedClearWork_routing (pid : PeerId) : RetainsRoutingCall (runFlushedClearWork pid) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => RetainsRouting s (routingView w))
        (fun _ w => RetainsRouting s (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hm := (modifyDev_routing (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) (fun _ => rfl)).wp (RetainsRouting s)
  have hw := RetainsRoutingCall.wp (queuedExpiredZeroKeyMaterial_routing pid) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, getDev, getAmbient, hidden, peekUnit, resolveUnit, invariant, unsupported, branch, AmbientM.invariant, AmbientM.unsupported, AmbientM.branch, runFlushedClearWork, hm, hw]
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem drainHandshakeSendWq_routing (upTo : Option PeerId) : RetainsRoutingCall (drainHandshakeSendWq upTo) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => RetainsRouting s (routingView w))
        (fun _ w => RetainsRouting s (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hs := fun pid => RetainsRoutingCall.wp (runFlushedSendWork_routing pid) s
  have hc := fun pid => RetainsRoutingCall.wp (runFlushedClearWork_routing pid) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, getDev, getAmbient, hidden, peekUnit, resolveUnit, invariant, unsupported, branch, AmbientM.invariant, AmbientM.unsupported, AmbientM.branch, drainHandshakeSendWq, hs, hc, getDev, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
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
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => RetainsRouting s (routingView w))
        (fun _ w => RetainsRouting s (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hd := fun t => (delTimer_routing pid t).wp (RetainsRouting s)
  have hw := RetainsRoutingCall.wp (drainHandshakeSendWq_routing (some pid)) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, getDev, getAmbient, hidden, peekUnit, resolveUnit, invariant, unsupported, branch, AmbientM.invariant, AmbientM.unsupported, AmbientM.branch, timersStop, hd, hw, getDev, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem peerRemoveAfterDead_routing (pid : PeerId) : RetainsRoutingCall (peerRemoveAfterDead pid) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => RetainsRouting s (routingView w))
        (fun _ w => RetainsRouting s (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := (getPeer_routing pid).wp (RetainsRouting s)
  have hk := (keypairsClear_routing pid).wp (RetainsRouting s)
  have ht := RetainsRoutingCall.wp (timersStop_routing pid) s
  have hw := RetainsRoutingCall.wp (drainHandshakeSendWq_routing none) s
  have hm := (modifyDev_routing (fun d => {d with numPeers := d.numPeers - 1}) (fun _ => rfl)).wp (RetainsRouting s)
  have hp := RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, getDev, getAmbient, hidden, peekUnit, resolveUnit, invariant, unsupported, branch, AmbientM.invariant, AmbientM.unsupported, AmbientM.branch, peerRemoveAfterDead, hg, hk, ht, hw, hm, hp, getDev, branch, unsupported, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsRouting.refl _

end Leanux.Proofs.WG.AllowedIps
