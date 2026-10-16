import Leanux.Proofs.WG.AllowedIps.RoutingSessionFrames
import Leanux.Proofs.Framing.WGCookie
import Leanux.Proofs.WG.AllowedIps.RoutingAcquire
import Leanux.Proofs.WG.AllowedIps.RoutingAdmissionFrames
import Leanux.Proofs.WG.Lifetimes.CookieAccess

/-! Original incoming Noise and cookie routing frames. Actual peer reference
release may retire a resident slot, so the endpoint relation preserves only
surviving lists. The source getters justify every peer write; no initial
residency, public-key affiliation or reference-credit premise is needed. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem pubkeyLookup_routing (key : Key) : SameView routingView (pubkeyLookup key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact (pubkeyLookup_routed key hr).1

/-- Arbitrary product actions retain the original cookie-masked store premise. -/
theorem cookie_routing (a : Leanux.M α) (ha : SameView productCookieView a) :
    SameView (fun w : World => routingView w.wg) a := by
  apply ha.of_factor (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg)
  intro w
  simp only [productCookieView, cookieStoreView, cookieView, wgOwnedView,
    wgStoreView, cookieDevice, routingView, Option.map_map, Function.comp_def]
  rfl

/-- Concrete cookie calls execute in the WireGuard world. -/
theorem cookie_routing_native (a : WG.M α) (ha : SameCookie a) :
    SameView routingView a := by
  apply ha.of_factor (fun store : WGOwnedView => store.dev.map routingState) routingView
  intro w
  simp only [cookieView, wgOwnedView, wgStoreView, cookieDevice, routingView,
    Option.map_map, Function.comp_def]
  rfl

theorem consumeInitiation_routing (msg : List UInt8) : RetainsRoutingCall (consumeInitiation msg) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => P (routingView w)) (fun _ w => P (routingView w)) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := fun pid => routing_getPeer P pid
  have hs := fun pid p => routing_setPeer P pid p
  have hu := fun peer => RetainsRoutingCall.wp (peerPut_retainsRouting peer) s
  have he := fun b e ck h => (messageEphemeral_sameWGWorld b e ck h).wp (fun w => P (routingView w))
  have hd := fun b ck p q => (mixDh_sameWGWorld b ck p q).wp (fun w => P (routingView w))
  have hp := fun ck p => (mixPrecomputedDh_sameWGWorld ck p).wp (fun w => P (routingView w))
  have hdec := fun a k h => (messageDecrypt_sameWGWorld a k h).wp (fun w => P (routingView w))
  have hl := fun k => (pubkeyLookup_routing k).wp P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hiddenClock64, branch, branchCmp, invariant, consumeInitiation, hg, hs, hu, he, hd, hp, hdec, hl,
    getDev, WG.orM, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem consumeResponse_routing (msg : List UInt8) : RetainsRoutingCall (consumeResponse msg) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => P (routingView w)) (fun _ w => P (routingView w)) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := fun pid => routing_getPeer P pid
  have hs := fun pid p => routing_setPeer P pid p
  have hu := fun peer => RetainsRoutingCall.wp (peerPut_retainsRouting peer) s
  have hl := fun ks i => (indexLookup_routing ks i).wp P
  have he := fun b e ck h => (messageEphemeral_sameWGWorld b e ck h).wp (fun w => P (routingView w))
  have hd := fun b ck p q => (mixDh_sameWGWorld b ck p q).wp (fun w => P (routingView w))
  have hdec := fun a k h => (messageDecrypt_sameWGWorld a k h).wp (fun w => P (routingView w))
  have hk := fun b c ck d => (Framing.kdf_sameWGWorld b c ck d).wp (fun w => P (routingView w))
  have ho := fun xs i => (Framing.kdfOut_sameWGWorld xs i).wp (fun w => P (routingView w))
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hiddenClock64, branch, branchCmp, invariant, consumeResponse, hg, hs, hu, hl, he, hd, hdec, hk, ho,
    getDev, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem cookieMessageConsume_routing (msg : List UInt8) :
    RetainsRoutingCall (cookieMessageConsume msg) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => P (routingView w)) (fun _ w => P (routingView w)) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  have hl := (indexLookup_routing [.handshake, .keypair] (u32le msg 4)).wp P
  have hg := fun pid => routing_getPeer P pid
  have hs := fun pid p => routing_setPeer P pid p
  have hu := fun peer => RetainsRoutingCall.wp (peerPut_retainsRouting peer) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hiddenClock64, branch, branchCmp, invariant, cookieMessageConsume, hl, hg, hs, hu, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

end Leanux.Proofs.WG.AllowedIps
