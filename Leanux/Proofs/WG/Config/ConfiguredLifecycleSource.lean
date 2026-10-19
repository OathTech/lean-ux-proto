import Leanux.Proofs.WG.Config.ConfiguredOwnerEffects
import Leanux.Proofs.WG.Config.ConfiguredOptionalSource
import Leanux.Proofs.WG.Config.ConfiguredDeviceFrames
import Leanux.Proofs.WG.Config.ConfiguredLifecycleFrames
import Leanux.Proofs.WG.Index.LifecycleDeleteRuleSource
import Leanux.Proofs.WG.Index.LifecycleRuleSource
import Leanux.Proofs.WG.Index.LifecycleCleanupRuleSource
import Leanux.Proofs.WG.Index.LifecycleSource
import Leanux.Proofs.WG.Queues.DeviceAuxEntry
import Leanux.Proofs.WG.Packets.PublicationPoll

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem optionalReady_store {α : Type} (action : WG.M α) (same : SameWGStore action) :
    Preserves OptionalReady action :=
  optionalReady_native action (ProjectedRetainsRoutingCall.of_same (routing_kernel _ same))
    (BaseCoherence.store_view same)

theorem optionalReady_productStore {α : Type} (action : Leanux.M α) (same : SameProductStore action) :
    Preserves (fun w : World=>OptionalReady w.wg) action :=
  optionalReady_product action
    (ProjectedRetainsRoutingCall.of_same
      (same.of_factor (fun s : ProductStore43 => s.2.2.2.dev.map routingState)
        (fun w : World=>routingView w.wg) (fun _=>rfl)))
    (BaseCoherence.product_store_view same)

theorem optionalReady_modify (f : Device → Device)
    (routing : ∀d,routingState (f d)=routingState d)
    (base : ∀d,(f d).peerList=d.peerList ∧ (f d).peerHashtable=d.peerHashtable) :
    Preserves OptionalReady (modifyDev f) :=
  optionalReady_native _ (ProjectedRetainsRoutingCall.of_same (modifyDev_routing f routing))
    (base_modify f base)

theorem optionalReady_socket {α : Type} (action : WG.M α) (same : SameSocket action) :
    Preserves OptionalReady action :=
  optionalReady_native action (ProjectedRetainsRoutingCall.of_same (socketControl_routing_native action same))
    (socket_base action same)

theorem optionalReady_open : Preserves OptionalReady wgOpen :=
  LifecycleSource.open_preserves _
    (optionalReady_store _ getDev_sameWGStore)
    (fun pid=>by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a p v b pre run
      exact (getPeer_normal pid w v p a b run).1 ▸ pre)
    (fun port=>optionalReady_socket _ (socketInit_sameSocket port))
    (fun pid=>optionalReady_native _ (sendStagedPackets_routing pid) (BaseCoherence.staged_view pid))
    (fun pid=>optionalReady_native _ (sendKeepalive_routing pid) (BaseCoherence.keepalive_view pid))

theorem optionalReady_up : Preserves OptionalReady WG.wgUp := by
  unfold WG.wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact optionalReady_open)
    | (rx_retention_head modifyDev; exact optionalReady_modify _ (fun _=>rfl) (fun _=>⟨rfl,rfl⟩))
    | rx_retention_step

theorem optionalReady_stop : Preserves OptionalReady wgStop :=
  optionalReady_native _ wgStop_routing DeviceAuxEntry.stop_base

theorem optionalReady_down : Preserves OptionalReady WG.wgDown :=
  optionalReady_native _ wgDown_routing DeviceAuxEntry.down_base

theorem optionalReady_preexit : Preserves OptionalReady netnsPreExit :=
  LifecycleSource.preexit_preserves _
    (by apply (hoare_iff_run_ambient _ _ _).mpr; intro w a r v b pre run; cases run; exact pre)
    (optionalReady_store _ getDev_sameWGStore)
    (optionalReady_modify _ (fun _=>rfl) (fun _=>⟨rfl,rfl⟩))
    (optionalReady_socket _ (socketReinit_sameSocket none none))
    (fun pid=>optionalReady_native _
      (ProjectedRetainsRoutingCall.of_same (clearPeerEndpointSrc_routing pid))
      (BaseCoherence.clearEndpoint_view pid))

/-- The original guarded create either retains its link view or initializes
empty represented ownership. Refusals and recreation retain the actual source
semantics; no arbitrary setup operation is substituted. -/
theorem optionalReady_create : Preserves OptionalReady WG.wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g ambient result final after prior run
  have effect := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView g))
    g ambient result final after rfl run
  rcases effect with same | ⟨_,fresh⟩
  · have route := congrArg (fun s : WGStoreView => s.dev.map routingState) same
    rw [routingView_link,routingView_link] at route
    have base := congrArg (fun s : WGStoreView => BaseCoherence.view {dev:=s.dev}) same
    rw [(pinned_const _private.Leanux.Proofs.WG.Queues.DeviceAuxEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceAuxEntry.base_link),
      (pinned_const _private.Leanux.Proofs.WG.Queues.DeviceAuxEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceAuxEntry.base_link)] at base
    exact optionalReady_retains g final (route.symm ▸ RetainsRouting.refl _) (congrArg Prod.fst base) prior
  · have route := congrArg (fun s : WGStoreView => s.dev.map routingState) fresh
    rw [routingView_link] at route
    have view : routingView final=some (routingState ({ifindex:=0,ifname:="wg0"} : Device)) := by
      simpa [registeredLink,setupLink,linkDevice,routingState] using route
    intro d present
    have equal : routingState d=routingState ({ifindex:=0,ifname:="wg0"} : Device) := by
      simpa only [routingView,present,Option.map_some,Option.some.injEq] using view
    exact ⟨.empty,.empty,(empty_routing 0 "wg0").of_routingState equal,configuredOwners_empty d⟩

theorem optionalReady_destruct : Preserves OptionalReady wgDestruct := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b _ run d present
  have absent := Index.wgDestruct_absent w a result v b trivial run
  simp [absent] at present

theorem optionalReady_lift {α : Type} (action : WG.M α)
    (keeps : Preserves OptionalReady action) :
    Preserves (fun w : World=>OptionalReady w.wg) (liftWG action) :=
  PublicationPoll.native_product OptionalReady action keeps

theorem optionalReady_envUp : Preserves (fun w : World=>OptionalReady w.wg) Env.wgUp :=
  LifecycleSource.envUp_preserves _ optionalReady_productStore (optionalReady_lift _ optionalReady_up)

theorem optionalReady_envDown : Preserves (fun w : World=>OptionalReady w.wg) Env.wgDown :=
  LifecycleSource.envDown_preserves _ optionalReady_productStore (optionalReady_lift _ optionalReady_down)
    (optionalReady_productStore _ PendingScheduler.requireIdleDevice_store)

theorem optionalReady_cleanup : Preserves (fun w : World=>OptionalReady w.wg) Env.netnsCleanup :=
  LifecycleSource.cleanup_preserves _ optionalReady_productStore (optionalReady_lift _ optionalReady_preexit)

/-- Every normal original deletion preserves optional ownership, including
the absent-device errno path. Later Stops carry no fabricated final device. -/
theorem optionalReady_delete : Preserves (fun w : World=>OptionalReady w.wg) Env.wgDelete :=
  LifecycleSource.envDelete_preserves _ optionalReady_productStore
    (optionalReady_lift _ optionalReady_down) (optionalReady_lift _ optionalReady_destruct)


end Leanux.Proofs.WG.Config.OwnerConfiguration
