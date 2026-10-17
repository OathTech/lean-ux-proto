import Leanux.Proofs.WG.Queues.TxLiveRemoval
import Leanux.Proofs.Framing.WGDeviceLifecycle
import Leanux.Proofs.Framing.WGSocketLifecycle

/-! Native device creation, open and destruction retain the live TX frontier.
Fresh creation establishes an empty physical ring; arbitrary native deletion
callbacks retain explicit contracts at their actual source positions. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem socket_frame {action : WG.M α} (same : SameSocket action) : Preserves Ready action :=
  fields_ready (same.of_factor
    (fun k : WGOwnedView => k.dev.map fun d => (d.nextSkb,d.encryptQueue))
    _ (fun w => by simp only [socketView,socketDevice,wgOwnedView,wgStoreView,Option.map_map,Function.comp_def]))

theorem device_open : Preserves Ready wgOpen := by
  unfold wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact socket_frame (socketInit_sameSocket _))
    | (rx_retention_head sendStagedPackets; exact send _)
    | live_socket_step

theorem device_up : Preserves Ready wgUp := by
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact device_open)
    | live_socket_step

private theorem limiter_uninit : Preserves Ready ratelimiterUninit :=
  fields_ready (ratelimiterUninit_sameRatelimiter.of_factor
    (fun k : WGStoreView => k.dev.map fun d => (d.nextSkb,d.encryptQueue)) _ (fun _ => rfl))

theorem absent (w : WGWorld) (none : w.dev=none) : Ready w := by
  constructor <;> intro d device <;> simp [none] at device

theorem device_destruct : Preserves Ready wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact socket_reinit _ _)
    | (rx_retention_head peerRemoveAll; exact remove_all)
    | (rx_retention_head mayHaveSlept; exact store_ready _ mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit; exact limiter_uninit)
    | (rx_retention_head modify; apply hoare_modify; intro w _; exact absent _ rfl)
    | (rx_retention_head retireDeviceUnits; exact store_ready _ retireDeviceUnits_sameWGStore)
    | live_socket_step

/-- The source callbacks are actual native actions, unrestricted except for
the explicit preservation facts needed at each invocation. -/
theorem device_delete (onDown onUnregister : WG.M Unit)
    (downRule : Preserves Ready onDown) (unregisterRule : Preserves Ready onUnregister) :
    Preserves Ready (wgDelete onDown onUnregister) := by
  unfold wgDelete
  simp (config := {zeta := false}) only [getWG,monadLift_self,skipCut]
  repeat' first
    | exact downRule
    | exact unregisterRule
    | (rx_retention_head wgDown; exact down)
    | (rx_retention_head wgDestruct; exact device_destruct)
    | (rx_retention_head mayHaveSlept; exact store_ready _ mayHaveSlept_sameWGStore)
    | live_socket_step

theorem device_delete_default : Preserves Ready (wgDelete : WG.M Int) :=
  device_delete _ _ (preserves_pure ()) (preserves_pure ())

/-- Existing-device and refusal returns retain their ring. A newly registered
device has the actual freshly initialized ring, independently of old contents. -/
theorem device_create : Preserves Ready wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · apply ready_fields hi
    have fields := congrArg (fun k : WGStoreView => k.dev.map fun d => (d.nextSkb,d.encryptQueue)) same
    simpa only [linkView,linkStore,linkDevice,wgStoreView,Option.map_map,Function.comp_def] using fields
  · have ring (d : Device) (device : v.dev=some d) : d.encryptQueue=PtrRing.init MAX_QUEUED_PACKETS := by
      have fields := congrArg (fun k : WGStoreView => k.dev.map Device.encryptQueue) fresh
      simpa only [linkView,linkStore,linkDevice,wgStoreView,registeredLink,setupLink,
        device,Option.map_some,Option.map_map,Function.comp_def,Option.some.injEq] using fields
    constructor
    · intro d device
      rw [ring d device]
      exact initial_ring _ _
    · intro d device
      rw [ring d device]
      exact ⟨_,[],⟨[],rfl⟩⟩

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
