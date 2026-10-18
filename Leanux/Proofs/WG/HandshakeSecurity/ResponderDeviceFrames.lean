import Leanux.Proofs.WG.HandshakeSecurity.ResponderDeviceConfiguration

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins Origins.Retaining

theorem native_no_peers (confirmed : List Nat) (w : WGWorld)
    (empty : ∀ d, w.dev = some d → d.peers = {}) : History.Native confirmed w := by
  constructor
  · intro pid core resident _
    obtain ⟨d,hd,rest⟩ := Option.bind_eq_some_iff.mp resident
    simp [empty d hd] at rest
  · apply CurrentSlots.inv_iff w |>.mpr
    intro d pid p kid hd hp _
    simp [empty d hd] at hp

theorem up_native (confirmed : List Nat) : Preserves (History.Native confirmed) wgUp := by
  unfold wgUp wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact socket_native (socketInit_sameSocket _) confirmed)
    | (rx_retention_head sendStagedPackets; exact staged_native _ confirmed)
    | (rx_retention_head sendKeepalive; exact keepalive_native _ confirmed)
    | responder_config_step confirmed

theorem stop_native (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Preserves (History.Native confirmed) wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [branch, unsupported, requireNotPending]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact purge_native _ confirmed)
    | (rx_retention_head timersStop; exact stopTimers_native H1 _ confirmed)
    | (rx_retention_head handshakeClear; exact handshakeClear_native _ confirmed)
    | (rx_retention_head keypairsClear; exact keypairsClear_native H1 _ confirmed)
    | (rx_retention_head resetLastSentHandshake; exact resetHandshake_native _ confirmed)
    | (rx_retention_head socketReinit; exact socket_native (socketReinit_sameSocket _ _) confirmed)
    | responder_config_step confirmed

theorem down_native (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Preserves (History.Native confirmed) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop_native H1 confirmed)
    | responder_config_step confirmed

theorem limiter_native (confirmed : List Nat) :
    Preserves (History.Native confirmed) ratelimiterUninit := by
  have frame : SameView (fun w : WGWorld => w.dev) ratelimiterUninit :=
    ratelimiterUninit_sameRatelimiter.of_factor (fun s : WGStoreView => s.dev) _ (fun _ => rfl)
  exact frame.wp (fun dev => History.Native confirmed {dev := dev})

theorem destruct_native (H1 : H1ResponderCurrentEdges) (confirmed : List Nat) :
    Preserves (History.Native confirmed) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported, invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact socket_native (socketReinit_sameSocket _ _) confirmed)
    | (rx_retention_head peerRemoveAll; exact removeAll_native H1 confirmed)
    | (rx_retention_head mayHaveSlept; exact native_store mayHaveSlept_sameWGStore confirmed)
    | (rx_retention_head ratelimiterUninit; exact limiter_native confirmed)
    | (rx_retention_head modify; apply hoare_modify; intro w hi
       exact native_no_peers confirmed _ (by intro d hd; cases hd))
    | (rx_retention_head retireDeviceUnits; exact native_store retireDeviceUnits_sameWGStore confirmed)
    | responder_config_step confirmed

theorem create_native (confirmed : List Nat) : Preserves (History.Native confirmed) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · have curr := congrArg (fun s : WGStoreView => current {dev := s.dev}) same
    have fields := congrArg (fun s : WGStoreView => CurrentSlots.fields {dev := s.dev}) same
    refine ⟨hi.1.frame ?_, CurrentSlots.fields_transport hi.2 ?_⟩
    · funext pid
      cases hv : v.dev <;> cases hw : w.dev
      all_goals first
        | (solve | simp [current, hv, hw])
        | simpa [current, linkView, linkStore, linkDevice, wgStoreView, hv, hw] using congrFun curr pid
    · unfold CurrentSlots.fields RxCredits.keyWords at fields ⊢
      simpa only [linkView, linkStore, linkDevice, wgStoreView,
        Option.map_map, Option.bind_map, Function.comp_def] using fields
  · apply native_no_peers confirmed v
    intro d hd
    have peers := congrArg (fun s : WGStoreView => s.dev.map (·.peers)) fresh
    simpa only [linkView, linkStore, linkDevice, wgStoreView, setupLink, registeredLink,
      hd, Option.map_some, Option.some.injEq] using peers

theorem preExit_native (confirmed : List Nat) :
    Preserves (History.Native confirmed) netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head get
       exact hoare_consequence (hoare_get (History.Native confirmed))
         (fun _ hi => hi) (fun _ _ hi => hi.2))
    | (rx_retention_head socketReinit; exact socket_native (socketReinit_sameSocket _ _) confirmed)
    | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint_native _ confirmed)
    | responder_config_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder
