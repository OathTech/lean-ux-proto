import Leanux.Proofs.WG.AllowedIps.RoutingHandshakeFrames

/-! Normal-endpoint routing equality for original session creation and response
sending. Keypair/index updates are outside the routing view; peer writes retain
the allowed-IP list obtained from their actual getter. No affiliation or
resident-owner premise is imposed. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem keypairCreate_routing (pid : Option PeerId) : SameView routingView (keypairCreate pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hs := fun id k => (setKeypair_routing id k).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, keypairCreate, hs, getDev, modifyDev, hiddenAlloc, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState, Option.map_map, Function.comp_def]
  all_goals assumption

theorem addNewKeypair_routing (pid : PeerId) (kp : KeypairId) :
    SameView routingView (addNewKeypair pid kp) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hk := (getKeypair_routing kp).wp (fun t => t = s)
  have hp := fun id => (keypairPut_routing id true).wp (fun t => t = s)
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hg, hs, hk, hp, branch, AmbientM.branch]
  all_goals simp_all

theorem deriveKeys_routing (kp : KeypairId) (initiator : Bool) (ck : List UInt8) :
    SameView routingView (deriveKeys kp initiator ck) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := (getKeypair_routing kp).wp (fun t => t = s)
  have hs := fun k => (setKeypair_routing kp k).wp (fun t => t = s)
  have hk := fun b c ck d => (Framing.kdf_sameWGWorld b c ck d).wp (fun w => routingView w = s)
  have ho := fun xs i => (Framing.kdfOut_sameWGWorld xs i).wp (fun w => routingView w = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, deriveKeys, hg, hs, hiddenClock64, hk, ho]

theorem beginSession_routing (pid : PeerId) : SameView routingView (beginSession pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := (getPeer_routing pid).wp (fun t => t = s)
  have hk := fun id => (getKeypair_routing id).wp (fun t => t = s)
  have hs := fun id k => (setKeypair_routing id k).wp (fun t => t = s)
  have hc := fun word => (keypairCreate_routing word).wp (fun t => t = s)
  have hd := fun k b ck => (deriveKeys_routing k b ck).wp (fun t => t = s)
  have hz := (handshakeZero_routing pid).wp (fun t => t = s)
  have ha := fun k => (addNewKeypair_routing pid k).wp (fun t => t = s)
  have index_spec {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => routingView w = s) (fun _ w => routingView w = s) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    simpa only [routingView, hd, Option.map_some, routingState] using hi
  unfold Hoare at index_spec
  have hw := fun o => (ownerWord_routing o).wp (fun t => t = s)
  have hf := fun o => (ownerDeref_routing o).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, index_spec, hw, hf, beginSession, hg, hk, hs, hc, hd, hz, ha, branch, AmbientM.branch, WG.andM, invariant, AmbientM.invariant, unsupported, AmbientM.unsupported]

theorem createResponse_routing (pid : PeerId) : SameView routingView (createResponse pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hp := fun k => (generatePublic_sameWGWorld k).wp (fun w => routingView w = s)
  have he := fun b e ck h => (messageEphemeral_sameWGWorld b e ck h).wp (fun w => routingView w = s)
  have hd := fun b ck p q => (mixDh_sameWGWorld b ck p q).wp (fun w => routingView w = s)
  have hk := fun b c ck d => (Framing.kdf_sameWGWorld b c ck d).wp (fun w => routingView w = s)
  have ho := fun xs i => (Framing.kdfOut_sameWGWorld xs i).wp (fun w => routingView w = s)
  have index_spec {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => routingView w = s) (fun _ w => routingView w = s) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    simpa only [routingView, hd, Option.map_some, routingState] using hi
  unfold Hoare at index_spec
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  have hw := (ownerDeref_routing (.handshake pid)).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, index_spec, liftM, hidden, hw, hg, hs, hp, he, hd, hk, ho, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView]

theorem timersSessionDerived_routing (pid : PeerId) : SameView routingView (timersSessionDerived pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hm := fun site timer delay => (modPeerTimer_routing site pid timer delay).wp (fun t => t = s)
  have hd (α : Type) := discard_view_spec (m := AmbientM) routingView (α := α) (fun t => t = s)
  mvcgen [timersSessionDerived, hm, hd]

theorem sendHandshakeResponse_routing (pid : PeerId) : SameView routingView (sendHandshakeResponse pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hr := (createResponse_routing pid).wp (fun t => t = s)
  have hm := fun msg => (addMacToPacket_routing pid msg).wp (fun t => t = s)
  have hb := (beginSession_routing pid).wp (fun t => t = s)
  have hd := (timersSessionDerived_routing pid).wp (fun t => t = s)
  have ht := (timersTraversal_routing pid).wp (fun t => t = s)
  have ha := (timersAnyAuthenticatedPacketSent_routing pid).wp (fun t => t = s)
  have hsend := fun msg => (sendBufferToPeer_routing pid msg).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hiddenClock64, sendHandshakeResponse, hg, hs, hr, hm, hb, hd, ht, ha, hsend, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals simp_all

end Leanux.Proofs.WG.AllowedIps
