import Leanux.Proofs.WG.RetirementSecurity.KeySlotDevice
import Leanux.Proofs.Framing.WGDeviceLifecycle

/-! Native device controls preserve slot liveness. Creation has empty peers;
destruction removes their obligations. No packet-credit or drain completion
is inferred from these projected lifecycle endpoints. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem open_device : Preserves (InvExcept pending) wgOpen := by
  unfold wgOpen
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact socket_frame (socketInit_sameSocket _))
    | (rx_retention_head sendStagedPackets; exact staged _)
    | (rx_retention_head sendKeepalive; exact keepalive _)
    | key_slot_rx_step

theorem up : Preserves (InvExcept pending) wgUp := by
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact open_device)
    | key_slot_rx_step

theorem stop : Preserves (InvExcept pending) wgStop := by
  unfold wgStop requireNotPending
  simp (config := {zeta:=false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact purge _)
    | (rx_retention_head timersStop; exact timers_stop _)
    | (rx_retention_head handshakeClear; exact handshake_clear _)
    | (rx_retention_head keypairsClear; exact clear _)
    | (rx_retention_head resetLastSentHandshake; exact reset _)
    | (rx_retention_head socketReinit; exact socket_frame (socketReinit_sameSocket _ _))
    | key_slot_rx_step

theorem down : Preserves (InvExcept pending) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop)
    | key_slot_rx_step

theorem no_device (w : WGWorld) (absent : w.dev=none) : InvExcept pending w := by
  intro pid p found
  simp [peerAt,absent] at found

theorem destruct : Preserves (InvExcept pending) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta:=false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact socket_frame (socketReinit_sameSocket _ _))
    | (rx_retention_head peerRemoveAll; exact all_peers)
    | (rx_retention_head mayHaveSlept; exact store mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit
       exact frame (ratelimiterUninit_sameRatelimiter.of_factor (fun s=>view {dev:=s.dev}) view (fun _=>rfl)))
    | (rx_retention_head _root_.modify; apply hoare_modify; intro w _; exact no_device _ rfl)
    | (rx_retention_head retireDeviceUnits; exact store retireDeviceUnits_sameWGStore)
    | key_slot_rx_step

theorem delete (onDown onUnregister : WG.M Unit)
    (downRule : Preserves (InvExcept pending) onDown)
    (unregisterRule : Preserves (InvExcept pending) onUnregister) :
    Preserves (InvExcept pending) (wgDelete onDown onUnregister) := by
  unfold wgDelete
  simp (config := {zeta:=false}) only [getWG,monadLift_self,skipCut]
  repeat' first
    | exact downRule
    | exact unregisterRule
    | (rx_retention_head wgDown; exact down)
    | (rx_retention_head wgDestruct; exact destruct)
    | (rx_retention_head mayHaveSlept; exact store mayHaveSlept_sameWGStore)
    | key_slot_rx_step

theorem delete_default : Preserves (InvExcept pending) (wgDelete : WG.M Int) :=
  delete _ _ (preserves_pure ()) (preserves_pure ())

theorem create_device : Preserves (InvExcept pending) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,new⟩
  · apply transport before
    funext pid
    simpa only [linkView,linkStore,linkDevice,wgStoreView,view,peerAt,
      Option.bind_map,Function.comp_def] using
      congrArg (fun s : WGStoreView=>view {dev:=s.dev} pid) same
  · intro pid p found
    obtain ⟨d,device,stored⟩ := Option.bind_eq_some_iff.mp found
    have empty : d.peers={} := by
      simpa only [linkView,linkStore,linkDevice,wgStoreView,registeredLink,setupLink,
        device,Option.map_some,Option.map_map,Function.comp_def,Option.some.injEq] using
        congrArg (fun s : WGStoreView=>s.dev.map Device.peers) new
    simp [empty] at stored

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
