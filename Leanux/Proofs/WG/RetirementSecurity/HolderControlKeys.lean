import Leanux.Proofs.WG.RetirementSecurity.HolderOuterLifecycle
import Leanux.Proofs.WG.Queues.HolderEntryControls

/-! The original environment controls transport exact key credit together
with the peer/slot support needed at shutdown's reference-paying calls. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderLifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem boundary_store (entry : HolderBoundary.Entry temporary carriers loans w)
    (same : wgStoreView v=wgStoreView w) : HolderBoundary.Entry temporary carriers loans v := by
  have peer := HolderEntryFrames.store entry.2.1 same
  exact ⟨⟨HolderPoll.keys_store entry.1.1 same,entry.1.2.1.store same,peer.2.2⟩,
    peer,KeySlotLiveness.store_transport same entry.2.2⟩

theorem up_boundary : Preserves (HolderBoundary.Entry temporary carriers loans) wgUp := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp up w a result v b entry.1 run,
    (hoare_iff_run_ambient _ _ _).mp DeviceAuxEntry.up w a result v b entry.2.1 run,
    (hoare_iff_run_ambient _ _ _).mp (KeySlotLiveness.up (pending:=[])) w a result v b entry.2.2 run⟩

theorem pre_exit_points : SameView ownershipPointView netnsPreExit := by
  intro initial
  change Preserves (fun w=>ownershipPointView w=initial) _
  unfold netnsPreExit
  simp (config:={zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head socketReinit; exact (HolderDevice.socket_points (socketReinit_sameSocket _ _)).wp (·=initial))
    | (rx_retention_head clearPeerEndpointSrc; exact (HolderDevice.clear_endpoint_points _).wp (·=initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec ownershipPointView (·=initial)
       intro x b
       change Preserves (fun w=>ownershipPointView w=initial) _)
    | ownership_source_step initial

theorem pre_exit : Preserves (HolderBoundary.Entry temporary carriers loans) netnsPreExit := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  have peer := (hoare_iff_run_ambient _ _ _).mp HolderEntryControls.preExit_entry w a result v b entry.2.1 run
  exact ⟨⟨(hoare_iff_run_ambient _ _ _).mp (HolderDevice.points_keys pre_exit_points) w a result v b entry.1.1 run,
    Allocated.native (DeviceControlCall.erases .preExit) (DeviceControlCall.allocation .preExit)
      entry.1.2.1 a b run,peer.2.2⟩,peer,
    (hoare_iff_run_ambient _ _ _).mp KeySlotControls.pre_exit w a result v b entry.2.2 run⟩

theorem product_store {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  exact boundary_store entry (congrArg (fun s : ProductStore43=>s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp same w result v run))

private theorem ambient (action : AmbientM α) :
    Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ entry=>entry)

private theorem routing (action : Net.M α) :
    Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) (monadLift action : Leanux.M α) :=
  product_store (fun initial=>productRouting_spec action (fun s=>s=initial))

private theorem edit_env (f : EnvWorld→EnvWorld) :
    Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) (modifyEnv f) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  cases run
  exact entry

macro "holder_control_step" : tactic => `(tactic| first
  | (rx_retention_head Env.pendingDevice; exact product_store (pendingDevice_sameKernel _ _))
  | (rx_retention_head getWG; exact product_store (fun initial=>productGetWG_spec (fun s=>s=initial)))
  | (rx_retention_head modifyEnv; exact edit_env _)
  | (rx_retention_head getRouting
     exact product_store (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w result v run; cases run; rfl))
  | (rx_retention_head modifyRouting; exact routing _)
  | (rx_retention_head Env.requireIdleDevice; exact product_store
      (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store))
  | (allocation_release_lift_from Net.M; exact routing _)
  | (allocation_release_lift_from AmbientM; exact ambient _)
  | rx_retention_step)

theorem env_up : Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) Env.wgUp := by
  unfold Env.wgUp
  simp (config:={zeta:=false}) only [skipCut]
  repeat' first
    | (allocation_release_lift_from WG.M; exact PublicationPoll.native_product _ _ up_boundary)
    | holder_control_step

theorem env_down : Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) Env.wgDown := by
  unfold Env.wgDown
  simp (config:={zeta:=false}) only [skipCut]
  repeat' first
    | (allocation_release_lift_from WG.M; exact PublicationPoll.native_product _ _ down)
    | holder_control_step
  exact product_store (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store)

theorem worker (kind : Worker) (body : Leanux.M Unit)
    (keeps : Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) body) :
    Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) (Env.runWorker kind body) := by
  unfold Env.runWorker
  simp (config:={zeta:=false}) only [hidden]
  repeat' first
    | exact keeps
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | holder_control_step

theorem env_cleanup : Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) Env.netnsCleanup := by
  unfold Env.netnsCleanup
  simp (config:={zeta:=false}) only [unsupported,invariant,peekUnit,resolveUnit,skipCut]
  repeat' first
    | (rx_retention_head Env.runWorker; apply worker)
    | (allocation_release_lift_from WG.M; exact PublicationPoll.native_product _ _ pre_exit)
    | holder_control_step

end Leanux.Proofs.WG.RetirementSecurity.HolderLifecycle
