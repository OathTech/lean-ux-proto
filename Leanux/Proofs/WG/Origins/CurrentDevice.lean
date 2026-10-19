import Leanux.Proofs.WG.Origins.CurrentLifecycle
import Leanux.Proofs.WG.Peers.ConfiguredAllowedIps

/-! Native device teardown and creation preserve configured peer identities and
same-receipt current-key support on normal returns. Deletion is permitted;
record failures and source guards remain Stops. A freshly created empty device
needs no new historical receipt. -/
namespace Leanux.Proofs.WG.CurrentLifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

private theorem purgeStaged_view (pid : PeerId) :
    SameView ConfiguredIdentity.view (purgeStagedPackets pid) := by
  intro initial
  unfold purgeStagedPackets
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  repeat' configured_step initial

private theorem socketReinit_preserves (new4 new6 : Option Nat)
    (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (socketReinit new4 new6) := by
  apply ConfiguredHandshake.current_preserves
  · apply (socketReinit_sameSocket new4 new6).of_factor
      (fun s : WGOwnedView => s.dev.map ConfiguredIdentity.state) ConfiguredIdentity.view
    intro w
    simp only [socketView,socketDevice,wgOwnedView,wgStoreView,ConfiguredIdentity.view,
      ConfiguredIdentity.state,Option.map_map,Function.comp_def]
    rfl
  · exact Origins.Retaining.of_view (Origins.Retaining.socketControl_material
      (project := id) _ ((socketReinit_sameSocket new4 new6).factor WGOwnedView.toWGStoreView))

private theorem ratelimiterUninit_preserves (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) ratelimiterUninit :=
  ConfiguredHandshake.current_preserves _
    (ratelimiterUninit_sameRatelimiter.of_factor
      (fun s : WGStoreView => s.dev.map ConfiguredIdentity.state) _ (fun _ => rfl))
    (Origins.Retaining.of_view (Origins.Retaining.ratelimiter_material
      (project := id) ratelimiterUninit_sameRatelimiter)) history

/-- Both passes use the source's saved peer list. Clearing the trie preserves
identity fields; marking dead and final release preserve the invariants. -/
theorem peerRemoveAll_preserves (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.free
       exact ConfiguredHandshake.current_preserves _ ConfiguredIdentity.allowedipsFree_view
         (Origins.Retaining.of_view Origins.Retaining.allowedipsFree_material) history)
    | (rx_retention_head peerMakeDead; exact markDead_preserves _ history)
    | (rx_retention_head peerRemoveAfterDead; exact peerRemoveAfterDead_preserves _ history)
    | current_lifecycle_step history

theorem wgStop_preserves (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [branch,unsupported,requireNotPending]
  repeat' first
    | (rx_retention_head purgeStagedPackets
       exact ConfiguredHandshake.current_preserves _ (purgeStaged_view _)
         (Origins.Retaining.of_view (Origins.Retaining.purgeStagedPackets_material _)) history)
    | (rx_retention_head timersStop; exact timersStop_preserves _ history)
    | (rx_retention_head handshakeClear
       exact ConfiguredHandshake.current_preserves _ (ConfiguredMaintenance.handshakeClear_view _)
         (Origins.Retaining.of_view (Origins.Retaining.handshakeClear_material _)) history)
    | (rx_retention_head keypairsClear
       exact ConfiguredHandshake.current_preserves _ (ConfiguredMaintenance.keypairsClear_view _)
         (Origins.Retaining.keypairsClear_material _) history)
    | (rx_retention_head resetLastSentHandshake
       exact ConfiguredHandshake.current_preserves _ (ConfiguredIdentity.resetHandshake _)
         (Origins.Retaining.of_view (Origins.Retaining.resetLastSentHandshake_material _)) history)
    | (rx_retention_head socketReinit; exact socketReinit_preserves _ _ history)
    | current_lifecycle_step history

theorem wgDown_preserves (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact wgStop_preserves history)
    | current_lifecycle_step history

/-- Successful destruction may erase the entire device. No premise excludes
queued work: those source paths retain their actual unsupported/invariant Stops. -/
theorem wgDestruct_preserves (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact socketReinit_preserves _ _ history)
    | (rx_retention_head peerRemoveAll; exact peerRemoveAll_preserves history)
    | (rx_retention_head mayHaveSlept
       exact ConfiguredHandshake.current_preserves _
         (ConfiguredIdentity.sameWG (project := id) mayHaveSlept_sameWGStore)
         (Origins.Retaining.of_view (Origins.sameView_of_sameWG
           (project := id) mayHaveSlept_sameWGStore)) history)
    | (rx_retention_head ratelimiterUninit; exact ratelimiterUninit_preserves history)
    | (rx_retention_head modify
       apply hoare_modify
       intro w _
       constructor
       · intro s hs
         simp [ConfiguredIdentity.view] at hs
       · exact CurrentIdentity.Inv.absent history _ rfl)
    | (rx_retention_head retireDeviceUnits
       exact ConfiguredHandshake.current_preserves _
         (ConfiguredIdentity.sameWG (project := id) retireDeviceUnits_sameWGStore)
         (Origins.Retaining.of_view (Origins.sameView_of_sameWG
           (project := id) retireDeviceUnits_sameWGStore)) history)
    | current_lifecycle_step history

/-- The actual native notifier callbacks remain arbitrary, with their own
preservation obligations at their source positions. -/
theorem wgDelete_preserves (history : List SessionOrigin.Receipt)
    (onDown onUnregister : WG.M Unit)
    (down : Preserves (Inv history) onDown)
    (unregister : Preserves (Inv history) onUnregister) :
    Preserves (Inv history) (wgDelete onDown onUnregister) := by
  unfold wgDelete
  simp (config := {zeta := false}) only [getWG,monadLift_self,skipCut]
  repeat' first
    | exact down
    | exact unregister
    | (rx_retention_head get
       exact hoare_consequence (hoare_get (Inv history)) (fun _ h => h) (fun _ _ h => h.2))
    | (rx_retention_head wgDown; exact wgDown_preserves history)
    | (rx_retention_head wgDestruct; exact wgDestruct_preserves history)
    | (rx_retention_head mayHaveSlept
       exact ConfiguredHandshake.current_preserves _
         (ConfiguredIdentity.sameWG (project := id) mayHaveSlept_sameWGStore)
         (Origins.Retaining.of_view (Origins.sameView_of_sameWG
           (project := id) mayHaveSlept_sameWGStore)) history)
    | current_lifecycle_step history

theorem wgDelete_default_preserves (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (wgDelete : WG.M Int) :=
  wgDelete_preserves history _ _ (preserves_pure ()) (preserves_pure ())

private theorem configuredView_link (w : WGWorld) :
    (linkView w).dev.map ConfiguredIdentity.state = ConfiguredIdentity.view w := by
  simp only [linkView,linkStore,linkDevice,wgStoreView,ConfiguredIdentity.view,
    ConfiguredIdentity.state,Option.map_map,Function.comp_def]
  rfl

/-- Existing-device/refusal endpoints retain their previous support. A new
registered device has no peers or keys and needs no receipt at its new epoch. -/
theorem wgCreate_preserves (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w ambient result v ambient' rfl hr
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp
    Origins.Retaining.wgCreate_material w ambient result v ambient' hr
  rcases endpoint with he | ⟨_,he⟩
  · have configured := congrArg (fun s : WGStoreView => s.dev.map ConfiguredIdentity.state) he
    rw [configuredView_link,configuredView_link] at configured
    exact ⟨fun s hs => hi.1 s (configured.symm.trans hs),
      hi.2.retain (CurrentIdentity.retains_of_configured_view material configured)⟩
  · constructor
    · have configured := congrArg (fun s : WGStoreView => s.dev.map ConfiguredIdentity.state) he
      rw [configuredView_link] at configured
      intro s hs
      rw [configured] at hs
      simp only [registeredLink,setupLink,Option.map_some,Option.some.injEq] at hs
      subst s
      constructor <;> simp [ConfiguredIdentity.state,linkDevice]
    · apply CurrentIdentity.Inv.empty_keys history v
      intro d hd
      have keys := congrArg (fun s : WGStoreView => s.dev.map (fun d => d.keypairs)) he
      simpa only [linkView,linkStore,wgStoreView,linkDevice,registeredLink,setupLink,
        hd,Option.map_some,Option.some.injEq] using keys

end Leanux.Proofs.WG.CurrentLifecycle
