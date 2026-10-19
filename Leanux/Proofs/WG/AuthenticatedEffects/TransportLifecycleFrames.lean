import Leanux.Proofs.WG.AuthenticatedEffects.TransportConfigurationFrames

/-! Lifecycle uses exact receive-store frames until destruction, which removes
all live packet obligations. A new device starts with no crypted receive cells. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportLifecycle
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration TransportPublication
open OwnerCompletion (geometry)
set_option maxHeartbeats 600000

theorem socket_geometry (a : WG.M α) (frame : SameSocket a) : SameView geometry a := by
  apply frame.of_factor
    (fun s : WGOwnedView => (s.dev.map fun d => (d.ifindex,d.nextPeer,d.nextKeypairId),
      s.dev.map (·.ifindex),fun id => s.dev.bind fun d => d.rxSkbs[id]?)) _
  intro w
  simp only [socketView,socketDevice,wgOwnedView,wgStoreView,geometry,RxCredits.rxView,
    Option.map_map,Option.bind_map,Function.comp_def]

theorem reset_geometry (pid : PeerId) : SameView geometry (resetLastSentHandshake pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold resetLastSentHandshake
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' completion_step initial

theorem stop_geometry : SameView geometry wgStop := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold wgStop
  simp (config := {zeta := false}) only [branch,unsupported,requireNotPending]
  repeat' first
    | (rx_retention_head purgeStagedPackets
       exact ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTimers.«0».Leanux.Proofs.WG.PublicationFrontier.purge_geometry) _).wp (fun s => s = initial))
    | (rx_retention_head timersStop; exact (TransportRemoval.timersStop_geometry _).wp (fun s => s = initial))
    | (rx_retention_head handshakeClear
       exact ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationClear.«0».Leanux.Proofs.WG.PublicationFrontier.handshakeClear_geometry) _).wp (fun s => s = initial))
    | (rx_retention_head keypairsClear
       exact ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationClear.«0».Leanux.Proofs.WG.PublicationFrontier.keypairsClear_geometry) _).wp (fun s => s = initial))
    | (rx_retention_head resetLastSentHandshake; exact (reset_geometry _).wp (fun s => s = initial))
    | (rx_retention_head socketReinit; exact (socket_geometry _ (socketReinit_sameSocket _ _)).wp (fun s => s = initial))
    | completion_step initial

theorem down_geometry : SameView geometry wgDown := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop_geometry.wp (fun s => s = initial))
    | completion_step initial

theorem preExit_rx : SameView RxDisposition.nativeRxStore netnsPreExit := by
  apply SameView.factor (view := geometry) (f := Prod.snd)
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketReinit; exact (socket_geometry _ (socketReinit_sameSocket _ _)).wp (fun s => s = initial))
    | (rx_retention_head clearPeerEndpointSrc
       exact ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTimers.«0».Leanux.Proofs.WG.PublicationFrontier.clearEndpoint_geometry) _).wp (fun s => s = initial))
    | completion_step initial

theorem absent (history : List TransportDriver.OriginEvent) (w : WGWorld) (empty : w.dev = none) : Inv history w := by
  intro id pkt cell _
  simp [RxDisposition.nativeRxStore,empty] at cell

private theorem limiter_rx : SameView RxDisposition.nativeRxStore ratelimiterUninit :=
  ratelimiterUninit_sameRatelimiter.of_factor
    (fun s : WGStoreView => (s.dev.map (·.ifindex),fun id => s.dev.bind fun d => d.rxSkbs[id]?)) _ (fun _ => rfl)

macro "transport_lifecycle_step " history:term : tactic => `(tactic| first
  | (allocation_release_head getDev; exact TransportPublication.store_preserves getDev_sameWGStore $history)
  | (allocation_release_head getPeer; exact preserves_of_rx _ (TransportPublication.getPeer_rx _) $history)
  | (allocation_release_head modifyDev; apply TransportPublication.modifyDev_preserves; all_goals intros; rfl)
  | (allocation_release_head get
     exact hoare_consequence (hoare_get (Inv $history)) (fun _ hi => hi) (fun _ _ hi => hi.2))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Inv $history))
  | allocation_release_step)

theorem destruct (history : List TransportDriver.OriginEvent) : Preserves (Inv history) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact preserves_of_rx _ (TransportConfiguration.socket_rx _ (socketReinit_sameSocket _ _)) history)
    | (rx_retention_head peerRemoveAll; exact preserves_of_rx _ (TransportRemoval.removeAll_geometry.factor Prod.snd) history)
    | (rx_retention_head mayHaveSlept; exact TransportPublication.store_preserves mayHaveSlept_sameWGStore history)
    | (rx_retention_head ratelimiterUninit; exact preserves_of_rx _ limiter_rx history)
    | (rx_retention_head modify; apply hoare_modify; intro w hi; exact absent history _ rfl)
    | (rx_retention_head retireDeviceUnits; exact TransportPublication.store_preserves retireDeviceUnits_sameWGStore history)
    | transport_lifecycle_step history

theorem delete (onDown onUnregister : WG.M Unit) (history : List TransportDriver.OriginEvent)
    (down : Preserves (Inv history) onDown) (unregister : Preserves (Inv history) onUnregister) :
    Preserves (Inv history) (wgDelete onDown onUnregister) := by
  unfold wgDelete
  simp (config := {zeta := false}) only [getWG,monadLift_self,skipCut]
  repeat' first
    | exact down
    | exact unregister
    | (rx_retention_head wgDown; exact preserves_of_rx _ (down_geometry.factor Prod.snd) history)
    | (rx_retention_head wgDestruct; exact destruct history)
    | (rx_retention_head mayHaveSlept; exact TransportPublication.store_preserves mayHaveSlept_sameWGStore history)
    | transport_lifecycle_step history

theorem create (history : List TransportDriver.OriginEvent) : Preserves (Inv history) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w)) w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · apply hi.sameRx
    have fields := congrArg (fun s : WGStoreView =>
      (s.dev.map (·.ifindex),fun (id : SkbId) => s.dev.bind fun d => d.rxSkbs[id]?)) same
    simpa only [RxDisposition.nativeRxStore,linkView,linkStore,wgStoreView,linkDevice,
      Option.map_map,Option.bind_map,Function.comp_def] using fields
  · intro id pkt cell _
    obtain ⟨d,hd,packet⟩ := Option.bind_eq_some_iff.mp cell
    have fields := congrArg (fun s : WGStoreView => s.dev.map (·.rxSkbs)) fresh
    have empty : d.rxSkbs = {} := by
      simpa only [linkView,linkStore,wgStoreView,linkDevice,registeredLink,setupLink,hd,
        Option.map_some,Option.some.injEq] using fields
    simp [empty] at packet

end Leanux.Proofs.WG.AuthenticatedEffects.TransportLifecycle
