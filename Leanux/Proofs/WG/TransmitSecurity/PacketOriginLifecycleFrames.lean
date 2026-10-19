import Leanux.Proofs.WG.TransmitSecurity.PacketOriginConfigurationFrames
import Leanux.Proofs.Framing.WGDeviceLifecycle

/-! TX origins survive native stop and namespace exit. Destruction removes
resident obligations; creation starts a new device with an empty packet store. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option maxHeartbeats 600000
set_option pp.structureInstances false

macro "origin_lifecycle_frame" : tactic => `(tactic| first
  | (rx_retention_head purgeStagedPackets; exact frame (snapshot_wire (OccurrenceTimers.purge_wire _)))
  | (rx_retention_head timersStop; exact frame (snapshot_wire (OccurrenceRemoval.timers_stop_wire _)))
  | (rx_retention_head handshakeClear; exact frame (snapshot_wire (OccurrenceKeys.handshake_clear_wire _)))
  | (rx_retention_head keypairsClear; exact frame (snapshot_wire (OccurrenceKeys.clear_wire _)))
  | (rx_retention_head resetLastSentHandshake; exact frame (snapshot_wire (OccurrenceCreation.reset_wire _)))
  | (rx_retention_head socketReinit; exact frame (snapshot_wire (OccurrenceConfiguration.socket_wire (socketReinit_sameSocket _ _))))
  | origin_configuration_frame)

theorem stop : Preserves (Inv h) wgStop := by
  unfold wgStop requireNotPending
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' origin_lifecycle_frame

theorem down : Preserves (Inv h) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop)
    | origin_lifecycle_frame

theorem pre_exit : Preserves (Inv h) netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' origin_lifecycle_frame

theorem absent (w : WGWorld) (empty : w.dev = none) : Inv h w := by
  intro generation atEpoch
  simp only [epoch,empty,Option.map_none] at atEpoch
  cases atEpoch

private theorem limiter : Preserves (Inv h) ratelimiterUninit :=
  frame (snapshot_wire (ratelimiterUninit_sameRatelimiter.of_factor
    (fun s : WGStoreView => txCryptWire {dev:=s.dev}) _ (fun _=>rfl)))

theorem destruct : Preserves (Inv h) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head mayHaveSlept; exact store mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit; exact limiter)
    | (rx_retention_head _root_.modify; apply hoare_modify; intro w _; exact absent _ rfl)
    | (rx_retention_head retireDeviceUnits; exact store retireDeviceUnits_sameWGStore)
    | origin_lifecycle_frame

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
    | origin_lifecycle_frame

theorem delete_default : Preserves (Inv h) (wgDelete : WG.M Int) :=
  delete _ _ (preserves_pure ()) (preserves_pure ())

theorem device_create : Preserves (Inv h) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · apply before.retains
    apply Retains.of_snapshot
    change (epoch v,PacketMaterial.view v) = (epoch w,PacketMaterial.view w)
    apply Prod.ext
    · have fields := congrArg (fun s : WGStoreView => s.dev.map (·.ifindex)) same
      simpa only [epoch,linkView,linkStore,wgStoreView,linkDevice,Option.map_map,Function.comp_def] using fields
    · funext id
      have fields := congrArg (fun s : WGStoreView =>
        (s.dev.bind fun d => d.txSkbs[id]?).map PacketMaterial.material) same
      simpa only [PacketMaterial.view,TxDisposition.txPackets,linkView,linkStore,
        wgStoreView,linkDevice,Option.bind_map,Function.comp_def] using fields
  · intro _ _ id packet cell
    obtain ⟨d,hd,stored⟩ := Option.bind_eq_some_iff.mp cell
    have fields := congrArg (fun s : WGStoreView => s.dev.map (·.txSkbs)) fresh
    have empty : d.txSkbs = {} := by
      simpa only [linkView,linkStore,wgStoreView,linkDevice,registeredLink,setupLink,hd,
        Option.map_some,Option.some.injEq] using fields
    simp [empty] at stored

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins.NativeFrames
