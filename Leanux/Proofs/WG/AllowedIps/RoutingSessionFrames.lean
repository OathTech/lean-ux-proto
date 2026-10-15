import Leanux.Proofs.WG.AllowedIps.RoutingMaintenanceFrames

/-! Normal-endpoint routing equality for original session creation and response
sending. Keypair/index updates are outside the routing view; peer writes retain
the allowed-IP list obtained from their actual getter. No affiliation or
resident-owner premise is imposed. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem keypairCreate_routing (pid : PeerId) : SameView routingView (keypairCreate pid) := by
  apply SameView.of_wp
  intro s
  have ha := (routing_kernel _ (hiddenAlloc_sameKernel .kzallocKeypair)).wp (fun t => t = s)
  have hs := fun id k => (setKeypair_routing id k).wp (fun t => t = s)
  mvcgen [keypairCreate, ha, hs, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState, Option.map_map, Function.comp_def]
  all_goals assumption

theorem addNewKeypair_routing (pid : PeerId) (kp : KeypairId) :
    SameView routingView (addNewKeypair pid kp) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hk := (getKeypair_routing kp).wp (fun t => t = s)
  have hp := fun id => (keypairPut_routing id true).wp (fun t => t = s)
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  mvcgen [hg, hs, hk, hp, branch]
  all_goals simp_all

theorem deriveKeys_routing (kp : KeypairId) (initiator : Bool) (ck : List UInt8) :
    SameView routingView (deriveKeys kp initiator ck) := by
  apply SameView.of_wp
  intro s
  have hg := (getKeypair_routing kp).wp (fun t => t = s)
  have hs := fun k => (setKeypair_routing kp k).wp (fun t => t = s)
  have hc := (routing_kernel _ (hiddenClock64_sameKernel .deriveKeysBirthdate)).wp (fun t => t = s)
  have hk := fun b c ck d => (routing_kernel _ (Framing.kdf_sameKernel b c ck d)).wp (fun t => t = s)
  have ho := fun xs i => (routing_kernel _ (Framing.kdfOut_sameKernel xs i)).wp (fun t => t = s)
  mvcgen [deriveKeys, hg, hs, hc, hk, ho]

theorem indexReplaceHandshake_routing (pid : PeerId) (kp : KeypairId) :
    SameView routingView (indexReplaceHandshake pid kp) := by
  apply SameView.of_wp
  intro s
  mvcgen [indexReplaceHandshake, indexHashed, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState, Option.map_map, Function.comp_def]
  all_goals assumption

theorem beginSession_routing (pid : PeerId) : SameView routingView (beginSession pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_routing pid).wp (fun t => t = s)
  have hk := fun id => (getKeypair_routing id).wp (fun t => t = s)
  have hs := fun id k => (setKeypair_routing id k).wp (fun t => t = s)
  have hc := (keypairCreate_routing pid).wp (fun t => t = s)
  have hd := fun k b ck => (deriveKeys_routing k b ck).wp (fun t => t = s)
  have hz := (handshakeZero_routing pid).wp (fun t => t = s)
  have ha := fun k => (addNewKeypair_routing pid k).wp (fun t => t = s)
  have hr := fun k => (indexReplaceHandshake_routing pid k).wp (fun t => t = s)
  mvcgen [beginSession, hg, hk, hs, hc, hd, hz, ha, hr, branch, WG.andM, invariant, unsupported]

theorem createResponse_routing (pid : PeerId) : SameView routingView (createResponse pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hh := fun site => (routing_kernel _ (hidden_sameKernel site)).wp (fun t => t = s)
  have hp := fun k => (routing_kernel _ (generatePublic_sameKernel k)).wp (fun t => t = s)
  have he := fun b e ck h => (routing_kernel _ (messageEphemeral_sameKernel b e ck h)).wp (fun t => t = s)
  have hd := fun b ck p q => (routing_kernel _ (mixDh_sameKernel b ck p q)).wp (fun t => t = s)
  have hk := fun b c ck d => (routing_kernel _ (Framing.kdf_sameKernel b c ck d)).wp (fun t => t = s)
  have ho := fun xs i => (routing_kernel _ (Framing.kdfOut_sameKernel xs i)).wp (fun t => t = s)
  have hi := (indexInsert_routing pid .handshake).wp (fun t => t = s)
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  mvcgen [hg, hs, hh, hp, he, hd, hk, ho, hi, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState]

theorem timersSessionDerived_routing (pid : PeerId) : SameView routingView (timersSessionDerived pid) := by
  apply SameView.of_wp
  intro s
  have hm := fun site timer delay => (modPeerTimer_routing site pid timer delay).wp (fun t => t = s)
  have hd (α : Type) := discard_view_spec routingView (α := α) (fun t => t = s)
  mvcgen [timersSessionDerived, hm, hd]

theorem sendHandshakeResponse_routing (pid : PeerId) : SameView routingView (sendHandshakeResponse pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hc := fun site => (routing_kernel _ (hiddenClock64_sameKernel site)).wp (fun t => t = s)
  have hr := (createResponse_routing pid).wp (fun t => t = s)
  have hm := fun msg => (addMacToPacket_routing pid msg).wp (fun t => t = s)
  have hb := (beginSession_routing pid).wp (fun t => t = s)
  have hd := (timersSessionDerived_routing pid).wp (fun t => t = s)
  have ht := (timersTraversal_routing pid).wp (fun t => t = s)
  have ha := (timersAnyAuthenticatedPacketSent_routing pid).wp (fun t => t = s)
  have hsend := fun msg => (sendBufferToPeer_routing pid msg).wp (fun t => t = s)
  mvcgen [sendHandshakeResponse, hg, hs, hc, hr, hm, hb, hd, ht, ha, hsend, branch, invariant]
  all_goals simp_all

end Leanux.Proofs.WG.AllowedIps
