import Leanux.Proofs.WG.AllowedIps.RoutingGlobal
import Leanux.Proofs.WG.AllowedIps.RoutingDeviceFrames
import Leanux.Proofs.Framing.WGDeviceLifecycle

/-! Concrete guarded creation and shutdown frames. Creation uses the original
whole-call endpoint, not an invariant for arbitrary setup. Shutdown permits
resident-peer deletion and keeps the original failed drains and getters. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem routingView_link (w : WGWorld) :
    (linkView w).dev.map routingState = routingView w := by
  simp [linkView, linkStore, linkDevice, wgStoreView,
    routingView, routingState, Option.map_map, Function.comp_def]
  rfl

/-- The original arbitrary product action keeps its complete 43-field mask. -/
def ratelimiterProductView (w : World) : ProductStore43 :=
  (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter),
    ratelimiterStore (wgStoreView w.wg))

theorem ratelimiter_routing (a : Leanux.M α)
    (ha : SameView ratelimiterProductView a) :
    SameView (fun w => routingView w.wg) a :=
  ha.of_factor (fun k : ProductStore43 => k.2.2.2.dev.map routingState)
    (fun w => routingView w.wg) (fun _ => rfl)

theorem ratelimiter_routing_native (a : WG.M α) (ha : SameRatelimiter a) :
    SameView routingView a :=
  ha.of_factor (fun k : WGStoreView => k.dev.map routingState) routingView (fun _ => rfl)

theorem wgCreate_global (hi : GlobalRoutedView (routingView w) xs)
    (hr : (wgCreate.run w).run ambient = .ok ((ret, v), ambient')) : GlobalRoutedView (routingView v) xs := by
  have hc := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w ambient ret v ambient' rfl hr
  rcases hc with he | ⟨hn, he⟩
  · have hv := congrArg (fun s : WGStoreView => s.dev.map routingState) he
    rw [routingView_link, routingView_link] at hv
    exact hv ▸ hi
  · have hnone : routingView w = none := by
      rw [← routingView_link, hn]; rfl
    have hx : xs = ([], []) := by simpa [GlobalRoutedView, hnone] using hi
    subst xs
    have hv := congrArg (fun s : WGStoreView => s.dev.map routingState) he
    rw [routingView_link] at hv
    have hv' : routingView v = some (routingState ({ifindex := 0, ifname := "wg0"} : Device)) := by
      simpa [registeredLink, setupLink, linkDevice, routingState] using hv
    rw [hv']
    exact ⟨_, .empty, .empty, rfl, empty_routing 0 "wg0", flatAgree_empty 32, flatAgree_empty 128⟩

theorem wgCreate_global_completion (initial : FlatTable × FlatTable) :
    StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w)
      (CompletionSafe initial) (liftWGPrefix wgCreate) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w ambient ret v ambient' hi hr
  exact ⟨hi.1, wgCreate_global hi.2 hr⟩

theorem purgeStagedPackets_routing (pid : PeerId) : SameView routingView (purgeStagedPackets pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  mvcgen [purgeStagedPackets, hg, hs, modifyDev]
  all_goals dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState, Option.map_map, Option.bind_map, Function.comp_def]
  all_goals exact And.left (by assumption)

theorem wgStop_routing : RetainsRoutingCall wgStop := by
  apply ProjectedAction.of_wp
  intro s
  have hn := fun pid => (requireNotPending_routing pid "wg_stop while a handshake is queued").wp (RetainsRouting s)
  have hp := fun pid => (purgeStagedPackets_routing pid).wp (RetainsRouting s)
  have ht := fun pid => RetainsRoutingCall.wp (timersStop_routing pid) s
  have hh := fun pid => (handshakeClear_routing pid).wp (RetainsRouting s)
  have hk := fun pid => (keypairsClear_routing pid).wp (RetainsRouting s)
  have hr := fun pid => (resetLastSentHandshake_routing pid).wp (RetainsRouting s)
  have hm := (modifyDev_routing (fun d => {d with handshakeQueueLen := 0}) (fun _ => rfl)).wp (RetainsRouting s)
  have hs := (socketControl_routing_native _ (socketReinit_sameSocket none none)).wp (RetainsRouting s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => RetainsRouting s (routingView w))
        (fun _ w => RetainsRouting s (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, wgStop, hn, hp, ht, hh, hk,
    hr, hm, hs, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant,
    unsupported, AmbientM.unsupported]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) :
    PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
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
  have hs := RetainsRoutingCall.wp wgStop_routing s
  mvcgen [wgDown, hm, hs]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem initialWG_global (net bare : Bool) :
    GlobalRoutedView (routingView (Runner.initialWG net bare)) ([], []) := by
  cases net <;> cases bare
  all_goals first
    | exact rfl
    | exact ⟨_, .empty, .empty, rfl, empty_routing 3 "wg0", flatAgree_empty 32, flatAgree_empty 128⟩

end Leanux.Proofs.WG.AllowedIps
