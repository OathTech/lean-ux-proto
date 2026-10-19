import Leanux.Proofs.WG.RetirementSecurity.OccurrenceLifecycle
import Leanux.Proofs.WG.Origins.OwnerControlCalls
import Leanux.Proofs.Framing.EnvOperations

/-! Original environment controls preserve physical TX ownership at actual
empty-local caller boundaries, including device deletion and netns cleanup. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceControls
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits OccurrenceStack OccurrenceHandshake OccurrenceConfiguration

theorem product_store {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (fun w : World => Ready [] [] w.wg) action := OccurrenceDecrypt.product_store same

private theorem product_ambient (action : AmbientM α) :
    Preserves (fun w : World => Ready [] [] w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi)

private theorem product_routing (action : Net.M α) :
    Preserves (fun w : World => Ready [] [] w.wg) (monadLift action : Leanux.M α) :=
  product_store (fun initial => productRouting_spec action (fun s => s = initial))

private theorem product_env (f : EnvWorld → EnvWorld) :
    Preserves (fun w : World => Ready [] [] w.wg) (modifyEnv f) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases run
  exact hi

private theorem idle : Preserves (fun w : World => Ready [] [] w.wg) Env.requireIdleDevice :=
  product_store (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store)

private theorem inet_destroy : Preserves (fun w : World => Ready [] [] w.wg) Env.inetdevDestroy :=
  product_store (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store)

macro "occurrence_control_step" : tactic => `(tactic| first
  | (rx_retention_head getWG; exact product_store (fun initial => productGetWG_spec (fun s => s = initial)))
  | (rx_retention_head getRouting
     exact product_store (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w result v run; cases run; rfl))
  | (rx_retention_head modifyEnv; exact product_env _)
  | (rx_retention_head modifyRouting; exact product_routing _)
  | (rx_retention_head Env.requireIdleDevice; exact idle)
  | (rx_retention_head Env.inetdevDestroy; exact inet_destroy)
  | (allocation_release_lift_from Net.M; exact product_routing _)
  | (allocation_release_lift_from AmbientM; exact product_ambient _)
  | rx_retention_step)

theorem env_up : Preserves (fun w : World => Ready [] [] w.wg) Env.wgUp := by
  unfold Env.wgUp
  simp (config := {zeta := false}) only [skipCut]
  repeat' first
    | (allocation_release_lift_from WG.M; exact PublicationPoll.native_product (Ready [] []) _ OccurrenceLifecycle.up)
    | occurrence_control_step

theorem env_down : Preserves (fun w : World => Ready [] [] w.wg) Env.wgDown := by
  unfold Env.wgDown
  simp (config := {zeta := false}) only [skipCut]
  repeat' first
    | (allocation_release_lift_from WG.M; exact PublicationPoll.native_product (Ready [] []) _ OccurrenceLifecycle.down)
    | occurrence_control_step

theorem device_delete_product (onDown onUnregister : Leanux.M Unit)
    (downRule : Preserves (fun w : World => Ready [] [] w.wg) onDown)
    (unregisterRule : Preserves (fun w : World => Ready [] [] w.wg) onUnregister) :
    Preserves (fun w : World => Ready [] [] w.wg) (WG.wgDelete onDown onUnregister) := by
  unfold WG.wgDelete
  simp (config := {zeta := false}) only [skipCut]
  repeat' first
    | exact downRule
    | exact unregisterRule
    | (allocation_release_lift_from WG.M; first
        | exact PublicationPoll.native_product (Ready [] []) _ (RxPollOccurrences.store getDev_sameWGStore)
        | exact PublicationPoll.native_product (Ready [] []) _ OccurrenceLifecycle.down
        | exact PublicationPoll.native_product (Ready [] []) _ (RxPollOccurrences.store mayHaveSlept_sameWGStore)
        | exact PublicationPoll.native_product (Ready [] []) _ OccurrenceLifecycle.destruct)
    | occurrence_control_step

theorem env_delete : Preserves (fun w : World => Ready [] [] w.wg) Env.wgDelete := by
  unfold Env.wgDelete
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head WG.wgDelete; apply device_delete_product)
    | occurrence_control_step

theorem pre_exit : Preserves (Ready [] []) WG.netnsPreExit := by
  unfold WG.netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketReinit; exact socket_reinit _ _)
    | (rx_retention_head clearPeerEndpointSrc; exact OccurrenceTimers.clear_endpoint _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Ready [] [])
       intro x b
       change Preserves (Ready [] []) _)
    | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
    | occurrence_config_step

theorem worker_control (kind : Worker) (body : Leanux.M Unit)
    (keeps : Preserves (fun w : World => Ready [] [] w.wg) body) :
    Preserves (fun w : World => Ready [] [] w.wg) (Env.runWorker kind body) := by
  unfold Env.runWorker
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | exact keeps
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact product_ambient _)
    | occurrence_control_step

theorem env_cleanup : Preserves (fun w : World => Ready [] [] w.wg) Env.netnsCleanup := by
  unfold Env.netnsCleanup
  simp (config := {zeta := false}) only [unsupported,peekUnit,resolveUnit,skipCut]
  repeat' first
    | (rx_retention_head Env.runWorker; apply worker_control)
    | (allocation_release_lift_from WG.M; exact PublicationPoll.native_product (Ready [] []) _ pre_exit)
    | occurrence_control_step

theorem env_mtu (n : Nat) : Preserves (fun w : World => Ready [] [] w.wg) (Env.setMtu n) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have same := (ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w result v run
  have geometry :=  envScalar_identity_metadata w v same
  have wire : txCryptWire v.wg = txCryptWire w.wg := by
    simpa only [envScalarView,envScalarStore,envScalarDevice,productStoreView,wgStoreView,
      txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,Option.map_map,Option.bind_map,Function.comp_def] using
      congrArg (fun s : ProductStore43 => txCryptWire {dev:=s.2.2.2.dev}) same
  have queues : txQueueContents v.wg = txQueueContents w.wg := by
    funext pid
    simpa only [envScalarView,envScalarStore,envScalarDevice,productStoreView,wgStoreView,
      txQueueContents,handoffTxView,Option.bind_map,Function.comp_def] using
      congrArg (fun s : ProductStore43 => txQueueContents {dev:=s.2.2.2.dev} pid) same
  exact ⟨⟨before.1.choose,before.1.choose_spec.congr (congrArg Prod.fst geometry) (congrArg Prod.snd geometry)⟩,
    before.2.1.queueContents queues (congrArg Prod.snd wire),
    before.2.2.frame_packets (congrArg Prod.fst wire)
      (fun _ owned=>owned.queueContents queues) (congrArg Prod.snd wire)⟩

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceControls
