import Leanux.Proofs.WG.Packets.PublicationRemoval
import Leanux.Proofs.WG.Packets.PublicationTimers
import Leanux.Proofs.WG.Packets.PublicationHandshakeReceive
import Leanux.Proofs.WG.Origins.OwnerDeviceCreation

/-! Device lifecycle retains older packet publications at actual native
endpoints. Destruction erases obligations and successful creation starts with
an empty receive store. Native notifier callbacks remain arbitrary actions. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

theorem socket_preserves (a : WG.M α) (frame : SameSocket a) (history : List RxHistory.Event) :
    Preserves (Inv history) a := by
  apply preserves_of_configured a
  · apply frame.of_factor
      (fun s : WGOwnedView => (s.dev.map (·.ifindex),fun id => s.dev.bind fun d => d.rxSkbs[id]?))
      RxDisposition.nativeRxStore
    intro w
    simp only [socketView,socketDevice,wgOwnedView,wgStoreView,RxDisposition.nativeRxStore,
      Option.map_map,Option.bind_map,Function.comp_def]
  · apply frame.of_factor (fun s : WGOwnedView => s.dev.map ConfiguredIdentity.state)
      ConfiguredIdentity.view
    intro w
    simp only [socketView,socketDevice,wgOwnedView,wgStoreView,ConfiguredIdentity.view,
      ConfiguredIdentity.state,Option.map_map,Function.comp_def]
    rfl

private theorem resetHandshake (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (resetLastSentHandshake pid) := by
  apply preserves_of_configured _ ?_ (ConfiguredIdentity.resetHandshake pid) history
  apply SameView.factor (view := OwnerCompletion.geometry) (f := Prod.snd)
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold resetLastSentHandshake
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' completion_step initial

theorem wgUp_preserves (history : List RxHistory.Event) : Preserves (Inv history) wgUp := by
  unfold wgUp wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact socket_preserves _ (socketInit_sameSocket _) history)
    | (rx_retention_head sendStagedPackets; exact sendStagedPackets_preserves _ history)
    | (rx_retention_head sendKeepalive
       exact sendKeepalive_preserves _ history)
    | publication_removal_step history

theorem wgStop_preserves (history : List RxHistory.Event) : Preserves (Inv history) wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [branch,unsupported,requireNotPending]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact purgeStagedPackets_preserves _ history)
    | (rx_retention_head timersStop; exact timersStop_preserves _ history)
    | (rx_retention_head handshakeClear; exact handshakeClear_preserves _ history)
    | (rx_retention_head keypairsClear; exact keypairsClear_preserves _ history)
    | (rx_retention_head resetLastSentHandshake; exact resetHandshake _ history)
    | (rx_retention_head socketReinit; exact socket_preserves _ (socketReinit_sameSocket _ _) history)
    | publication_removal_step history

theorem wgDown_preserves (history : List RxHistory.Event) : Preserves (Inv history) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact wgStop_preserves history)
    | publication_removal_step history

private theorem limiterUninit (history : List RxHistory.Event) :
    Preserves (Inv history) ratelimiterUninit := by
  apply preserves_of_configured _
  · exact ratelimiterUninit_sameRatelimiter.of_factor
      (fun s : WGStoreView => (s.dev.map (·.ifindex),fun id => s.dev.bind fun d => d.rxSkbs[id]?))
      _ (fun _ => rfl)
  · exact ratelimiterUninit_sameRatelimiter.of_factor
      (fun s : WGStoreView => s.dev.map ConfiguredIdentity.state) _ (fun _ => rfl)

theorem wgDestruct_preserves (history : List RxHistory.Event) : Preserves (Inv history) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact socket_preserves _ (socketReinit_sameSocket _ _) history)
    | (rx_retention_head peerRemoveAll; exact peerRemoveAll_preserves history)
    | (rx_retention_head mayHaveSlept; exact store_preserves mayHaveSlept_sameWGStore history)
    | (rx_retention_head ratelimiterUninit; exact limiterUninit history)
    | (rx_retention_head modify; apply hoare_modify; intro w hi; exact Inv.absent history _ rfl)
    | (rx_retention_head retireDeviceUnits; exact store_preserves retireDeviceUnits_sameWGStore history)
    | publication_removal_step history

theorem wgDelete_preserves (onDown onUnregister : WG.M Unit) (history : List RxHistory.Event)
    (down : Preserves (Inv history) onDown) (unregister : Preserves (Inv history) onUnregister) :
    Preserves (Inv history) (wgDelete onDown onUnregister) := by
  unfold wgDelete
  simp (config := {zeta := false}) only [getWG,monadLift_self,skipCut]
  repeat' first
    | exact down
    | exact unregister
    | (rx_retention_head get
       exact hoare_consequence (hoare_get (Inv history))
         (fun _ hi => hi) (fun _ _ hi => hi.2))
    | (rx_retention_head wgDown; exact wgDown_preserves history)
    | (rx_retention_head wgDestruct; exact wgDestruct_preserves history)
    | (rx_retention_head mayHaveSlept; exact store_preserves mayHaveSlept_sameWGStore history)
    | publication_removal_step history

theorem wgCreate_preserves (history : List RxHistory.Event) : Preserves (Inv history) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w ambient result v finalAmbient rfl hr
  rcases endpoint with same | ⟨_,fresh⟩
  · have packets : RxDisposition.nativeRxStore v = RxDisposition.nativeRxStore w := by
      have fields := congrArg (fun s : WGStoreView =>
        (s.dev.map (·.ifindex),fun (id : SkbId) => s.dev.bind fun d => d.rxSkbs[id]?)) same
      simpa only [RxDisposition.nativeRxStore,linkView,linkStore,wgStoreView,linkDevice,
        Option.map_map,Option.bind_map,Function.comp_def] using fields
    have front : frontier v = frontier w := by
      have fields := congrArg (fun s : WGStoreView => s.dev.map fun d => (d.ifindex,d.nextPeer)) same
      simpa only [frontier,linkView,linkStore,wgStoreView,linkDevice,
        Option.map_map,Function.comp_def] using fields
    have peers : CurrentIdentity.peerView v = CurrentIdentity.peerView w := by
      have fields := congrArg (fun s : WGStoreView => CurrentIdentity.peerView {dev := s.dev}) same
      simpa only [CurrentIdentity.peerView,linkView,linkStore,wgStoreView,linkDevice,
        Option.map_map,Option.bind_map,Function.comp_def] using fields
    apply hi.transport_cells
    · intro id pkt cell _
      exact ⟨packets ▸ cell,
        congrArg (fun epoch : Option Nat => (epoch.getD 0,id+1)) (congrArg Prod.fst packets)⟩
    · exact FrontiersLe.of_eq front
    · apply PublicationCompletion.peers_fields
      intro pid ident current
      simpa only [peers] using current
  · apply Inv.no_crypted history
    intro d hd id pkt hp crypted
    have fields := congrArg (fun s : WGStoreView => s.dev.map (·.rxSkbs)) fresh
    have empty : d.rxSkbs = {} := by
      simpa only [linkView,linkStore,wgStoreView,linkDevice,registeredLink,setupLink,hd,
        Option.map_some,Option.some.injEq] using fields
    simp [empty] at hp

theorem netnsPreExit_preserves (history : List RxHistory.Event) :
    Preserves (Inv history) netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head get
       exact hoare_consequence (hoare_get (Inv history))
         (fun _ hi => hi) (fun _ _ hi => hi.2))
    | (rx_retention_head socketReinit; exact socket_preserves _ (socketReinit_sameSocket _ _) history)
    | (rx_retention_head clearPeerEndpointSrc; exact clearPeerEndpointSrc_preserves _ history)
    | publication_removal_step history

end Leanux.Proofs.WG.PublicationFrontier
