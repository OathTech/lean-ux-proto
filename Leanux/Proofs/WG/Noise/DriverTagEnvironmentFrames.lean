import Leanux.Proofs.WG.Index.LifecycleRuleSource
import Leanux.Proofs.WG.Noise.DriverTagSilentFrames
import Leanux.Proofs.WG.Noise.DriverTagPeerConfigurationFrames
import Leanux.Proofs.WG.Noise.DriverTagProductSource
import Leanux.Proofs.WG.Noise.DriverTagControlCompleteSource
import Leanux.Proofs.WG.Noise.DriverTagSchedulerSource
import Leanux.Proofs.WG.Noise.PendingEnvironmentFrames
import Leanux.Proofs.WG.Noise.PendingTicketDeviceFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.DriverTags.Environment
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Std.Do

/-! Frames: actual non-owner lifecycle calls retain surviving raw tags.
Existing exact creation and typed subsystem contracts are projected directly. -/
macro "driver_lifecycle_wg_step " entry:term : tactic => `(tactic| first
  | (rx_retention_head getDev; exact Silent.of_frame $entry _ (store_frame getDev_sameWGStore))
  | (rx_retention_head getPeer; exact Silent.of_frame $entry _ (getPeer_frame _))
  | (rx_retention_head get; exact Silent.of_frame $entry _ read_frame)
  | (rx_retention_head modifyDev
     apply Silent.of_frame $entry
     apply modifyDev_frame
     intro d
     rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rx_retention_step)

theorem open_native (entry : TagMap) :
    Preserves (Silent.Retained entry) wgOpen :=
  Noise.LifecycleSource.open_preserves _
    (Silent.of_frame entry _ (store_frame getDev_sameWGStore))
    (fun pid => Silent.of_frame entry _ (getPeer_frame pid))
    (fun port => Silent.of_frame entry _ (socket_frame (socketInit_sameSocket port)))
    (fun pid => Configuration.staged_preserves pid entry)
    (fun pid => Configuration.keepalive_preserves pid entry)
theorem up_native (entry : TagMap) :
    Preserves (Silent.Retained entry) WG.wgUp := by
  unfold WG.wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact open_native entry)
    | driver_lifecycle_wg_step entry

theorem preexit_native (entry : TagMap) :
    Preserves (Silent.Retained entry) netnsPreExit :=
  Noise.LifecycleSource.preexit_preserves _
    (Silent.of_frame entry _ read_frame)
    (Silent.of_frame entry _ (store_frame getDev_sameWGStore))
    (Silent.of_frame entry _ (modifyDev_frame _ (fun _=>rfl)))
    (Silent.of_frame entry _ (socket_frame (socketReinit_sameSocket _ _)))
    (fun pid => Silent.of_frame entry _ (clearPeerEndpointSrc_frame pid))
theorem link_tags (g : WGWorld) : responseTagMap (linkView g).dev = tagView g := by
  funext pid
  cases device : g.dev <;>
    simp [linkView,linkStore,linkDevice,wgStoreView,tagView,responseTagMap,device]

theorem create_native (entry : TagMap) :
    Preserves (Silent.Retained entry) WG.wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g ambient result final after prior run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView g))
    g ambient result final after rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · have tags := congrArg (fun s : WGStoreView => responseTagMap s.dev) same
    rw [link_tags,link_tags] at tags
    change TagsRetained entry (tagView final)
    rw [tags]
    exact prior
  · have tags := congrArg (fun s : WGStoreView => responseTagMap s.dev) fresh
    rw [link_tags] at tags
    intro pid tag present
    rw [tags] at present
    simp [registeredLink,setupLink,responseTagMap,linkDevice] at present

theorem lift_native {α : Type} (entry : TagMap) (action : WG.M α)
    (kept : ∀ initial, Preserves (Silent.Retained initial) action) :
    Preserves (fun w : World => Silent.Retained entry w.wg) (monadLift action : Leanux.M α) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w value final prior run
  apply prior.trans
  exact native_product_retained action (fun g ambient result final after execution =>
    (hoare_iff_run_ambient _ _ _).mp (kept (tagView g))
      g ambient result final after (TagsRetained.refl _) execution) w value final run

theorem inetdev_store : SameProductStore Env.inetdevDestroy :=
  pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.inetdevDestroy_store

theorem routing {α : Type} (entry : TagMap) (action : Net.M α) :
    Preserves (fun w : World => Silent.Retained entry w.wg) (monadLift action : Leanux.M α) :=
  Silent.product_store entry _ (fun initial => productRouting_spec action (fun s => s = initial))

theorem fixture_modify (entry : TagMap) (f : EnvWorld → EnvWorld) :
    Preserves (fun w : World => Silent.Retained entry w.wg) (modifyEnv f) :=
  Silent.product_store entry _ (by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w result final run
    cases run
    rfl)

macro "driver_lifecycle_env_step " entry:term : tactic => `(tactic| first
  | (rx_retention_head getWG; exact Silent.product_store $entry _
      (fun initial => productGetWG_spec (fun s => s = initial)))
  | (rx_retention_head getRouting; exact Silent.product_store $entry _ (by
      apply (ProjectedAction.iff_run _ _ _).mpr
      intro w result final run
      cases run
      rfl))
  | (rx_retention_head modifyRouting; exact Silent.product_store $entry _
      (fun initial => productRouting_spec _ (fun s => s = initial)))
  | (rx_retention_head modifyEnv; exact fixture_modify $entry _)
  | (rx_retention_head Env.inetdevDestroy; exact Silent.product_store $entry _ inetdev_store)
  | (first
       | rx_retention_head liftWG
       | allocation_release_lift_from WG.M
     apply lift_native $entry
     intro initial
     first
     | (rx_retention_head WG.wgUp; exact up_native initial)
     | (rx_retention_head netnsPreExit; exact preexit_native initial)
     | (rx_retention_head getDev; exact Silent.of_frame initial _ (store_frame getDev_sameWGStore))
     | (rx_retention_head mayHaveSlept; exact Silent.of_frame initial _ (store_frame mayHaveSlept_sameWGStore)))
  | (allocation_release_lift_from Net.M; exact routing $entry _)
  | (rx_retention_head skipCut; exact productAmbient_spec (AmbientM.skipCut _) _ (fun _ _ prior => prior))
  | (rx_retention_head unsupported; exact productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ prior => prior))
  | (rx_retention_head peekUnit; exact productAmbient_spec (AmbientM.peekUnit _) _ (fun _ _ prior => prior))
  | (rx_retention_head resolveUnit; exact productAmbient_spec (AmbientM.resolveUnit _ _ _) _ (fun _ _ prior => prior))
  | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ _ (fun _ _ prior => prior))
  | rx_retention_step)

theorem envUp_native (entry : TagMap) :
    Preserves (fun w : World => Silent.Retained entry w.wg) Env.wgUp :=
  Noise.LifecycleSource.envUp_preserves _
    (fun action same => Silent.product_store entry action same)
    (lift_native entry _ up_native)
theorem cleanup_native (entry : TagMap) :
    Preserves (fun w : World => Silent.Retained entry w.wg) Env.netnsCleanup := by
  unfold Env.netnsCleanup
  repeat' first
    | (rx_retention_head Env.runWorker
       apply TimerDiscipline.runWorker_kernel_contract _ _
         (fun wg _ _ _ => Silent.Retained entry wg)
         (fun wg _ _ _ => Silent.Retained entry wg)
       change Preserves (fun w : World => Silent.Retained entry w.wg) _)
    | driver_lifecycle_env_step entry

end Leanux.Proofs.WG.Noise.DriverTags.Environment
