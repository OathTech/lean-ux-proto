import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTimerEnvironment
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerControlFrames

/-! Original opening and namespace controls preserve exact peer-reference
accounting, including actual staging, keepalive and socket effects. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Controls
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders ControlFrames

macro "retired_control_native" : tactic => `(tactic| first
  | (rx_retention_head getDev; exact stored getDev_sameWGStore)
  | (rx_retention_head getPeer; exact TimerFrames.read_boundary _)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))
  | (rx_retention_head modifyDev
     apply modifyDevice
     intro w
     cases w with
     | mk dev => cases dev <;> rfl)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (ExactBoundary _ _)
     intro _ _
     change Preserves (ExactBoundary _ _) _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rx_retention_step)

theorem opened : Preserves (ExactBoundary cs loans) wgOpen := by
  unfold wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact socket (socketInit_sameSocket _))
    | (rx_retention_head sendStagedPackets; exact ExactBoundary.staged _)
    | (rx_retention_head sendKeepalive; exact TimerCallbacks.keepalive_boundary _)
    | retired_control_native

theorem up : Preserves (ExactBoundary cs loans) WG.wgUp := by
  unfold WG.wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact opened)
    | retired_control_native

theorem endpoint (pid : PeerId) : Preserves (ExactBoundary cs loans) (clearPeerEndpointSrc pid) := by
  have cache : Preserves (ExactBoundary cs loans) (dstCacheResetNow pid) := by
    unfold dstCacheResetNow
    apply preserves_bind (ConfigurationUpdate.dstReset_boundary pid)
    intro _
    exact TimerFrames.modify_boundary pid (fun p => {p with dstCache := {p.dstCache with slot := none}})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl)
  unfold clearPeerEndpointSrc
  rw [←bind_assoc]
  exact preserves_bind (TimerFrames.modify_boundary pid
    (fun p => {p with endpoint := p.endpoint.map fun e => {e with src := 0,srcIf := 0}})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl)) (fun _ => cache)

theorem preExit : Preserves (ExactBoundary cs loans) WG.netnsPreExit := by
  unfold WG.netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketReinit; exact socket (socketReinit_sameSocket _ _))
    | (rx_retention_head clearPeerEndpointSrc; exact endpoint _)
    | retired_control_native

macro "retired_control_product" : tactic => `(tactic| first
  | (rx_retention_head Env.pendingDevice; exact product _ (pendingDevice_sameKernel _ _))
  | (rx_retention_head getWG; exact product _ (fun initial => productGetWG_spec (fun s => s=initial)))
  | (rx_retention_head modifyEnv; exact editEnv _)
  | (rx_retention_head getRouting
     exact product _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w result v run; cases run; rfl))
  | (rx_retention_head modifyRouting; exact routing _)
  | (allocation_release_lift_from Net.M; exact routing _)
  | (allocation_release_lift_from AmbientM; exact ambient _)
  | rx_retention_step)

theorem env_up : Preserves (fun w : World => ExactBoundary cs loans w.wg) Env.wgUp := by
  unfold Env.wgUp
  simp (config := {zeta := false}) only [skipCut]
  repeat' first
    | (allocation_release_lift_from WG.M; exact ExactBoundary.lift _ up)
    | retired_control_product

theorem cleanup : Preserves (fun w : World => ExactBoundary cs loans w.wg) Env.netnsCleanup := by
  unfold Env.netnsCleanup
  simp (config := {zeta := false}) only [unsupported,invariant,peekUnit,resolveUnit,skipCut]
  repeat' first
    | (rx_retention_head Env.runWorker; apply TimerEnvironment.worker)
    | (allocation_release_lift_from WG.M; exact ExactBoundary.lift _ preExit)
    | retired_control_product

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Controls
