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
  have dropped (n : Nat) := modifyDev_routing
    (fun d => {d with txDropped := d.txDropped + n}) (fun _ => rfl)
  routing_handshake_source [purgeStagedPackets] using [dropped]


theorem wgStop_routing : RetainsRoutingCall wgStop := by
  intro s
  let Q := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have pending := fun pid => (requireNotPending_routing pid "wg_stop while a handshake is queued").wp Q
  have purge := fun pid => (purgeStagedPackets_routing pid).wp Q
  have timers := fun pid => RetainsRoutingCall.wp (timersStop_routing pid) s
  have handshake := fun pid => (handshakeClear_routing pid).wp Q
  have keys := fun pid => (keypairsClear_routing pid).wp Q
  have reset := fun pid => (resetLastSentHandshake_routing pid).wp Q
  have clear := (modifyDev_routing (fun d => {d with handshakeQueueLen := 0})
    (fun _ => rfl)).wp Q
  have socket := (socketControl_routing_native _ (socketReinit_sameSocket none none)).wp Q
  have loop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs b f) :=
    list_view_spec id P xs b f hf
  have main : Preserves P wgStop := by
    unfold wgStop
    simp (config := { zeta := false }) only [branch, unsupported]
    repeat' first
      | (rx_retention_head requireNotPending; exact pending _)
      | (rx_retention_head purgeStagedPackets; exact purge _)
      | (rx_retention_head timersStop; exact timers _)
      | (rx_retention_head handshakeClear; exact handshake _)
      | (rx_retention_head keypairsClear; exact keys _)
      | (rx_retention_head resetLastSentHandshake; exact reset _)
      | (rx_retention_head modifyDev; exact clear)
      | (rx_retention_head socketReinit; exact socket)
      | (rx_retention_head getDev; exact dev)
      | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
      | (rx_retention_head MonadLift.monadLift; exact ambient _)
      | (rx_retention_head ForIn.forIn; apply loop)
      | rx_retention_step
  apply hoare_consequence main
  · intro w h
    change RetainsRouting s (routingView w)
    dsimp only [_root_.id] at h
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h


theorem wgDown_routing : RetainsRoutingCall wgDown := by
  intro s
  have hm := (modifyDev_routing (fun d => {d with running := false})
    (fun _ => rfl)).wp (RetainsRouting s)
  have hs := RetainsRoutingCall.wp wgStop_routing s
  have main := preserves_bind hm (fun _ => hs)
  apply hoare_consequence main
  · intro w h
    dsimp only [_root_.id] at h
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h


theorem initialWG_global (net bare : Bool) :
    GlobalRoutedView (routingView (Runner.initialWG net bare)) ([], []) := by
  cases net <;> cases bare
  all_goals first
    | exact rfl
    | exact ⟨_, .empty, .empty, rfl, empty_routing 3 "wg0", flatAgree_empty 32, flatAgree_empty 128⟩

end Leanux.Proofs.WG.AllowedIps
