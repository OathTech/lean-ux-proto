import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialConfigurationFrames
import Leanux.Proofs.Framing.WGDeviceLifecycle
import Leanux.Proofs.WG.Queues.DeviceAuxEntry
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverLifecycleFrames

/-! TX origins survive native stop and namespace exit. Destruction removes
resident obligations; creation starts a new device with an empty packet store. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity TransmitSecurity Responder
set_option maxHeartbeats 600000
set_option pp.structureInstances false

macro "resident_lifecycle_frame" : tactic => `(tactic| first
  | (rx_retention_head purgeStagedPackets; exact purge _)
  | (rx_retention_head timersStop; exact stop_timers _)
  | (rx_retention_head handshakeClear; exact handshake_clear _)
  | (rx_retention_head keypairsClear; exact keys_clear _)
  | (rx_retention_head resetLastSentHandshake; exact reset_handshake _)
  | (rx_retention_head socketReinit; exact socket_frame (socketReinit_sameSocket _ _))
  | resident_configuration_frame)

theorem stop : Preserves (Inv h) wgStop := by
  unfold wgStop requireNotPending
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' resident_lifecycle_frame

theorem down : Preserves (Inv h) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop)
    | resident_lifecycle_frame

theorem pre_exit : Preserves (Inv h) netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' resident_lifecycle_frame

theorem absent (w : WGWorld) (empty : w.dev = none) : Inv h w := by
  intro d device
  rw [empty] at device
  cases device

private theorem limiter : Preserves (Inv h) ratelimiterUninit := by
  have same : SameView (fun w : WGWorld => w.dev) ratelimiterUninit :=
    ratelimiterUninit_sameRatelimiter.of_factor (fun s : WGStoreView => s.dev) _ (fun _ => rfl)
  exact same.wp (fun dev => Inv h {dev:=dev})

theorem destruct : Preserves (Inv h) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head mayHaveSlept; exact store mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit; exact limiter)
    | (rx_retention_head _root_.modify; apply hoare_modify; intro w _; exact absent _ rfl)
    | (rx_retention_head retireDeviceUnits; exact store retireDeviceUnits_sameWGStore)
    | resident_lifecycle_frame

theorem delete (onDown onUnregister : WG.M Unit)
    (downRule : Preserves (Inv h) onDown) (unregisterRule : Preserves (Inv h) onUnregister) :
    Preserves (Inv h) (wgDelete onDown onUnregister) := by
  unfold wgDelete
  simp (config := {zeta := false}) only [getWG,monadLift_self,skipCut]
  repeat' first
    | exact downRule
    | exact unregisterRule
    | (rx_retention_head wgDown; exact down)
    | (rx_retention_head wgDestruct; exact destruct)
    | (rx_retention_head mayHaveSlept; exact store mayHaveSlept_sameWGStore)
    | resident_lifecycle_frame

theorem delete_default : Preserves (Inv h) (wgDelete : WG.M Int) :=
  delete _ _ (preserves_pure ()) (preserves_pure ())

theorem device_create : Preserves (Inv h) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · have fields := congrArg (fun s : WGStoreView => (s.dev.map (·.txSkbs),
        s.dev.map (·.nextKeypairId),s.dev.map (·.keypairs),s.dev.map (·.ifindex))) same
    dsimp only [linkView,linkStore,wgStoreView,linkDevice,Option.map_map,Function.comp_def] at fields
    intro d hd id packet cell
    have old : ∃ e, w.dev = some e ∧ e.txSkbs = d.txSkbs ∧ e.nextKeypairId = d.nextKeypairId ∧
        e.keypairs = d.keypairs ∧ e.ifindex = d.ifindex := by
      cases hw : w.dev with
      | none => simp [hd,hw] at fields
      | some e =>
        refine ⟨e,rfl,?_,?_,?_,?_⟩
        · simpa only [hd,hw,Option.map_some,Option.some.injEq,linkDevice] using congrArg Prod.fst fields.symm
        · simpa only [hd,hw,Option.map_some,Option.some.injEq,linkDevice] using congrArg (fun x => x.2.1) fields.symm
        · simpa only [hd,hw,Option.map_some,Option.some.injEq,linkDevice] using congrArg (fun x => x.2.2.1) fields.symm
        · simpa only [hd,hw,Option.map_some,Option.some.injEq,linkDevice] using congrArg (fun x => x.2.2.2) fields.symm
    obtain ⟨e,he,packets,front,keys,epoch⟩ := old
    have prior := before e he id packet (packets.symm ▸ cell)
    refine ⟨front ▸ prior.1,?_⟩
    obtain ⟨core,certificate,retains⟩ := prior.2
    refine ⟨core,epoch ▸ certificate,?_⟩
    intro current resident
    apply retains current
    simpa only [pool,hd,he,Option.bind_some,keys] using resident
  · intro d hd id packet stored
    have fields := congrArg (fun s : WGStoreView => s.dev.map (·.txSkbs)) fresh
    have empty : d.txSkbs = {} := by
      simpa only [linkView,linkStore,wgStoreView,linkDevice,registeredLink,setupLink,hd,
        Option.map_some,Option.some.injEq] using fields
    simp [empty] at stored

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Responder

theorem bounds_stop : Preserves Bounds wgStop :=
  bounds_join RxCredits.DeviceAuxEntry.stop_configured RxCredits.DeviceAuxEntry.stop_slots

theorem bounds_down : Preserves Bounds wgDown :=
  bounds_join RxCredits.DeviceAuxEntry.down_configured RxCredits.DeviceAuxEntry.down_slots

theorem bounds_create : Preserves Bounds wgCreate :=
  bounds_join RxCredits.DeviceAuxEntry.create_configured RxCredits.DeviceAuxEntry.create_slots

theorem bounds_absent (w : WGWorld) (empty : w.dev = none) : Bounds w := by
  constructor
  · intro s hs
    simp only [ConfiguredIdentity.view,empty,Option.map_none] at hs
    cases hs
  · apply CurrentSlots.inv_iff w |>.mpr
    intro d pid peer kid device
    rw [empty] at device
    cases device

theorem bounds_destruct : Preserves Bounds wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact bounds_forget (DriverCuts.carrier_socket (socketReinit_sameSocket _ _)))
    | (rx_retention_head peerRemoveAll; exact bounds_remove_all)
    | (rx_retention_head mayHaveSlept; exact bounds_store mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit; exact bounds_forget DriverCuts.carrier_limiter)
    | (rx_retention_head modify; apply hoare_modify; intro w _; exact bounds_absent _ rfl)
    | (rx_retention_head retireDeviceUnits; exact bounds_store retireDeviceUnits_sameWGStore)
    | (solve | resident_configuration_bounds)
    | rx_retention_step

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
