import Leanux.Proofs.WG.AllowedIps.RoutingGlobal
import Leanux.Proofs.WG.AllowedIps.RoutingDeviceFrames
import Leanux.Proofs.Framing.WGDeviceLifecycle
import Leanux.Proofs.Framing.Prefill

/-! Concrete guarded creation and shutdown frames. Creation uses the original
whole-call endpoint, not an invariant for arbitrary setup. Shutdown permits
resident-peer deletion and keeps the original failed drains and getters. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem routingView_link (w : World) :
    (linkView w).wg.map routingState = routingView w := by
  simp [linkView, linkKernel, linkDevice, WGKernelView.ofKernel,
    routingView, routingState, Option.map_map, Function.comp_def]
  rfl

theorem ratelimiter_routing (a : M α) (ha : SameRatelimiterKernel a) :
    SameView routingView a := by
  exact ha.of_factor (fun k : Kernel => k.wg.map routingState) routingView (fun _ => rfl)

theorem wgCreate_global (hi : GlobalRoutedView (routingView w) xs)
    (hr : wgCreate.run w = .ok (ret, v)) : GlobalRoutedView (routingView v) xs := by
  have hc := (hoare_iff_triple _ _ _).mpr (wgCreate_endpoint (linkView w)) w ret v rfl hr
  rcases hc with he | ⟨hn, he⟩
  · have hv := congrArg (fun s : WGKernelView => s.wg.map routingState) he
    rw [routingView_link, routingView_link] at hv
    exact hv ▸ hi
  · have hnone : routingView w = none := by
      rw [← routingView_link, hn]; rfl
    have hx : xs = ([], []) := by simpa [GlobalRoutedView, hnone] using hi
    subst xs
    have hv := congrArg (fun s : WGKernelView => s.wg.map routingState) he
    rw [routingView_link] at hv
    have hv' : routingView v = some (routingState ({ifindex := 0, ifname := "wg0"} : Device)) := by
      simpa [registeredLink, setupLink, linkDevice, routingState] using hv
    rw [hv']
    exact ⟨_, .empty, .empty, rfl, empty_routing 0 "wg0", flatAgree_empty 32, flatAgree_empty 128⟩

theorem wgCreate_global_completion (initial : FlatTable × FlatTable) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) (liftPrefix wgCreate) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w ret v hi hr
  exact ⟨hi.1, wgCreate_global hi.2 hr⟩

theorem purgeStagedPackets_routing (pid : PeerId) : SameView routingView (purgeStagedPackets pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  mvcgen [purgeStagedPackets, hg, hs, modifyDev, modifyK]
  all_goals dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState, Option.map_map, Option.bind_map, Function.comp_def]
  all_goals exact And.left (by assumption)

theorem wgStop_routing : RetainsRoutingCall wgStop := by
  apply ProjectedAction.of_wp
  intro s
  have hn := fun pid => (requireNotPending_routing pid "wg_stop while a handshake is queued").wp (RetainsRouting s)
  have hp := fun pid => (purgeStagedPackets_routing pid).wp (RetainsRouting s)
  have ht := fun pid => (timersStop_routing pid).wp s
  have hh := fun pid => (handshakeClear_routing pid).wp (RetainsRouting s)
  have hk := fun pid => (keypairsClear_routing pid).wp (RetainsRouting s)
  have hr := fun pid => (resetLastSentHandshake_routing pid).wp (RetainsRouting s)
  have hm := (modifyDev_routing (fun d => {d with handshakeQueue := [], handshakeQueueLen := 0}) (fun _ => rfl)).wp (RetainsRouting s)
  have hs := (socketControl_routing _ (socketReinit_sameSocketKernel none none)).wp (RetainsRouting s)
  mvcgen [wgStop, hn, hp, ht, hh, hk, hr, hm, hs, getDev, getK, branch, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try assumption
  all_goals try exact id
  all_goals try trivial
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem wgDown_routing : RetainsRoutingCall wgDown := by
  apply ProjectedAction.of_wp
  intro s
  have hm := (modifyDev_routing (fun d => {d with running := false}) (fun _ => rfl)).wp (RetainsRouting s)
  have hs := wgStop_routing.wp s
  mvcgen [wgDown, hm, hs]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem initialKernel_global (rlimit : Nat) (net bare foreign stepped seccompChild : Bool) :
    GlobalRoutedView
      ((Runner.initialKernel rlimit net bare foreign stepped seccompChild).wg.map routingState) ([], []) := by
  cases net <;> cases bare
  all_goals first
    | exact rfl
    | exact ⟨_, .empty, .empty, rfl, empty_routing 3 "wg0", flatAgree_empty 32, flatAgree_empty 128⟩

theorem prefill_global (n : Nat) (k out : Kernel)
    (hi : GlobalRoutedView (k.wg.map routingState) xs)
    (hr : Env.seccompPrefill n k = .ok out) :
    GlobalRoutedView (out.wg.map routingState) xs := by
  have he := congrArg (fun s : WGKernelView => s.wg.map routingState) (prefill_wgKernel n k out hr)
  exact he ▸ hi

end Leanux.Proofs.WG.AllowedIps
