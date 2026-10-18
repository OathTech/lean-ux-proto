import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverTraffic

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem carrier_stop (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [branch,unsupported,requireNotPending]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact carrier_purge _ confirmed)
    | (rx_retention_head timersStop
       exact carrier_join confirmed (ConfiguredRemoval.stopTimers _) (stopTimers_native H1 _ confirmed))
    | (rx_retention_head handshakeClear
       exact carrier_frame confirmed (ConfiguredMaintenance.handshakeClear_view _) (handshakeClear_native _ confirmed))
    | (rx_retention_head keypairsClear
       exact carrier_frame confirmed (ConfiguredMaintenance.keypairsClear_view _) (keypairsClear_native H1 _ confirmed))
    | (rx_retention_head resetLastSentHandshake
       exact carrier_frame confirmed (ConfiguredIdentity.resetHandshake _) (resetHandshake_native _ confirmed))
    | (rx_retention_head socketReinit; exact carrier_socket (socketReinit_sameSocket _ _) confirmed)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Carrier confirmed)
       intro x b
       change Framing.Preserves (Carrier confirmed) _)
    | responder_carrier_handshake_step confirmed

theorem carrier_down (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact carrier_stop H1 confirmed)
    | responder_carrier_handshake_step confirmed

theorem carrier_limiter (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) ratelimiterUninit :=
  carrier_frame confirmed
    (ratelimiterUninit_sameRatelimiter.of_factor
      (fun s : WGStoreView => s.dev.map ConfiguredIdentity.state) _ (fun _ => rfl))
    (limiter_native confirmed)

theorem carrier_destruct (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact carrier_socket (socketReinit_sameSocket _ _) confirmed)
    | (rx_retention_head peerRemoveAll; exact carrier_remove_all H1 confirmed)
    | (rx_retention_head mayHaveSlept; exact carrier_store mayHaveSlept_sameWGStore confirmed)
    | (rx_retention_head ratelimiterUninit; exact carrier_limiter confirmed)
    | (rx_retention_head modify
       apply hoare_modify
       intro w _
       constructor
       · intro s hs; cases hs
       · exact native_no_peers confirmed _ (by intro d hd; cases hd))
    | (rx_retention_head retireDeviceUnits; exact carrier_store retireDeviceUnits_sameWGStore confirmed)
    | responder_carrier_handshake_step confirmed

private theorem configured_link (w : WGWorld) :
    (linkView w).dev.map ConfiguredIdentity.state = ConfiguredIdentity.view w := by
  simp only [linkView,linkStore,linkDevice,wgStoreView,ConfiguredIdentity.view,
    ConfiguredIdentity.state,Option.map_map,Function.comp_def]
  rfl

theorem carrier_device_create (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) wgCreate := by
  apply carrier_join confirmed _ (create_native confirmed)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · have configured := congrArg (fun s : WGStoreView => s.dev.map ConfiguredIdentity.state) same
    rw [configured_link,configured_link] at configured
    exact fun s hs => hi s (configured.symm.trans hs)
  · have configured := congrArg (fun s : WGStoreView => s.dev.map ConfiguredIdentity.state) fresh
    rw [configured_link] at configured
    intro s hs
    rw [configured] at hs
    simp only [registeredLink,setupLink,Option.map_some,Option.some.injEq] at hs
    subst s
    constructor <;> simp [ConfiguredIdentity.state,linkDevice]

theorem carrier_pre_exit (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head get
       exact hoare_consequence (hoare_get (Carrier confirmed)) (fun _ hi => hi) (fun _ _ hi => hi.2))
    | (rx_retention_head socketReinit; exact carrier_socket (socketReinit_sameSocket _ _) confirmed)
    | (rx_retention_head clearPeerEndpointSrc; exact carrier_clear_endpoint _ confirmed)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Carrier confirmed)
       intro x b
       change Framing.Preserves (Carrier confirmed) _)
    | responder_carrier_handshake_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
