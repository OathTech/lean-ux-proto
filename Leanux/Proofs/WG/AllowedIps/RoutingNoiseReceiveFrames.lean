import Leanux.Proofs.WG.AllowedIps.RoutingSessionFrames
import Leanux.Proofs.Framing.WGCookie
import Leanux.Proofs.WG.AllowedIps.RoutingAcquire

/-! Original incoming Noise and cookie routing frames. Actual peer reference
release may retire a resident slot, so the endpoint relation preserves only
surviving lists. The source getters justify every peer write; no initial
residency, public-key affiliation or reference-credit premise is needed. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem pubkeyLookup_routing (key : Key) : SameView routingView (pubkeyLookup key) :=
  fun _ _ _ hr => (pubkeyLookup_routed key hr).1

theorem cookie_routing (a : M α) (ha : SameCookieKernel a) : SameView routingView a := by
  apply ha.of_factor (fun k : Kernel => k.wg.map routingState) routingView
  intro w
  simp [cookieKernelView, cookieKernel, cookieDevice, routingView,
    Option.map_map, Function.comp_def]
  rfl

theorem consumeInitiation_routing (msg : List UInt8) : RetainsRoutingCall (consumeInitiation msg) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := fun pid => routing_getPeer P pid
  have hs := fun pid p => routing_setPeer P pid p
  have hu := fun peer => (peerPut_retainsRouting peer).wp s
  have hc := fun site => (routing_kernel _ (hiddenClock64_sameKernel site)).wp P
  have he := fun b e ck h => (routing_kernel _ (messageEphemeral_sameKernel b e ck h)).wp P
  have hd := fun b ck p q => (routing_kernel _ (mixDh_sameKernel b ck p q)).wp P
  have hp := fun ck p => (routing_kernel _ (mixPrecomputedDh_sameKernel ck p)).wp P
  have hdec := fun a k h => (routing_kernel _ (messageDecrypt_sameKernel a k h)).wp P
  have hl := fun k => (pubkeyLookup_routing k).wp P
  have hb := fun d b => (routing_kernel _ (sameKernel_branch d b)).wp P
  have hbc := fun d b x y => (routing_kernel _ (branchCmp_sameKernel d b x y)).wp P
  mvcgen [hb, hbc, consumeInitiation, hg, hs, hu, hc, he, hd, hp, hdec, hl,
    getDev, getK, WG.orM, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, routingState]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem consumeResponse_routing (msg : List UInt8) : RetainsRoutingCall (consumeResponse msg) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := fun pid => routing_getPeer P pid
  have hs := fun pid p => routing_setPeer P pid p
  have hu := fun peer => (peerPut_retainsRouting peer).wp s
  have hl := fun ks i => (indexLookup_routing ks i).wp P
  have he := fun b e ck h => (routing_kernel _ (messageEphemeral_sameKernel b e ck h)).wp P
  have hd := fun b ck p q => (routing_kernel _ (mixDh_sameKernel b ck p q)).wp P
  have hdec := fun a k h => (routing_kernel _ (messageDecrypt_sameKernel a k h)).wp P
  have hk := fun b c ck d => (routing_kernel _ (Framing.kdf_sameKernel b c ck d)).wp P
  have ho := fun xs i => (routing_kernel _ (Framing.kdfOut_sameKernel xs i)).wp P
  mvcgen [consumeResponse, hg, hs, hu, hl, he, hd, hdec, hk, ho,
    getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, routingState]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem cookieMessageConsume_routing (msg : List UInt8) :
    RetainsRoutingCall (cookieMessageConsume msg) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hl := (indexLookup_routing [.handshake, .keypair] (u32le msg 4)).wp P
  have hg := fun pid => routing_getPeer P pid
  have hs := fun pid p => routing_setPeer P pid p
  have hu := fun peer => (peerPut_retainsRouting peer).wp s
  have hc := (routing_kernel _ (hiddenClock64_sameKernel .cookieBirthdate)).wp P
  mvcgen [cookieMessageConsume, hl, hg, hs, hu, hc, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, routingState]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

end Leanux.Proofs.WG.AllowedIps
