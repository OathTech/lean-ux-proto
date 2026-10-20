import Leanux.Proofs.WG.Queues.HolderEntryFrames
import Leanux.Proofs.WG.Origins.OwnerRemaining
import Leanux.Proofs.WG.Queues.SlotTimers
import Leanux.Proofs.WG.Queues.BatchAccount

/-! The original quiet environment controls retain the supplied outer entry.
Native lifecycle effects and the existing owner journal are joined on the same
execution; no state is asserted after a Stop. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderEntryControls
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

private theorem lift_native (action : WG.M α) (keeps : Preserves (DeviceAuxEntry.Entry cs loans) action) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  have nativeRun := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) action w v result run
  exact (hoare_iff_run_ambient _ _ _).mp keeps w.wg w.ambient result v.wg v.ambient hi nativeRun

private theorem ambient (action : AmbientM α) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi=>hi)

private theorem routing (action : Net.M α) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (monadLift action : Leanux.M α) :=
  HolderEntryFrames.product (fun initial=>productRouting_spec action (fun s=>s=initial))

private theorem editEnv (f : EnvWorld→EnvWorld) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (modifyEnv f) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases run
  exact hi

macro "holder_entry_product_step" : tactic => `(tactic| first
  | (rx_retention_head getWG; exact HolderEntryFrames.product (fun initial=>productGetWG_spec (fun s=>s=initial)))
  | (rx_retention_head modifyEnv; exact editEnv _)
  | (rx_retention_head getRouting
     exact HolderEntryFrames.product (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w result v run; cases run; rfl))
  | (rx_retention_head modifyRouting; exact routing _)
  | (allocation_release_lift_from Net.M; exact routing _)
  | (allocation_release_lift_from AmbientM; exact ambient _)
  | rx_retention_step)

theorem up_entry : Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) Env.wgUp := by
  unfold Env.wgUp
  simp (config := {zeta := false}) only [skipCut]
  repeat' first
    | (allocation_release_lift_from WG.M; exact lift_native WG.wgUp DeviceAuxEntry.up)
    | holder_entry_product_step

theorem down_entry : Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) Env.wgDown := by
  unfold Env.wgDown
  simp (config := {zeta := false}) only [skipCut]
  repeat' first
    | (allocation_release_lift_from WG.M; exact lift_native WG.wgDown DeviceAuxEntry.down)
    | (rx_retention_head Env.requireIdleDevice; exact HolderEntryFrames.product
        (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store))
    | holder_entry_product_step

private theorem socket_entry (new4 new6 : Option Nat) :
    Preserves (DeviceAuxEntry.Entry cs loans) (socketReinit new4 new6) := by
  apply HolderEntryFrames.native
  apply (socketReinit_sameSocket new4 new6).of_factor
    (fun s : WGOwnedView=>HolderEntryFrames.fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8})
  intro w
  unfold HolderEntryFrames.fields CurrentSlots.fields HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  unfold BaseCoherence.view BaseCoherence.slots BaseCoherence.rows ConfiguredIdentity.view ConfiguredIdentity.state
  simp only [socketView,socketDevice,wgOwnedView,wgStoreView,
    Option.map_map,Option.map_bind,Option.bind_map,Function.comp_def,rxView]

private theorem endpoint_entry (pid : PeerId) : Preserves (DeviceAuxEntry.Entry cs loans) (clearPeerEndpointSrc pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (DeviceStages.clearEndpoint pid) w a result v b hi.1 run,
    HolderStopPhysical.optional_cell hi.2.1
      ((ProjectedAction.iff_run_ambient _ _ _).mp
        ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerPhysical.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimerPhysical.endpoint_cell) pid)
        w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotTimers.«0».Leanux.Proofs.WG.CurrentSlots.Timer.endpoint) pid)
      w a result v b hi.2.2 run⟩

theorem preExit_entry : Preserves (DeviceAuxEntry.Entry cs loans) WG.netnsPreExit := by
  unfold WG.netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ hi=>hi) (fun _ _ hi=>hi.2))
    | (rx_retention_head getDev; exact HolderEntryFrames.native (getDev_sameWGStore.of_factor
        (fun s : WGStoreView=>HolderEntryFrames.fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8}) _ (fun _=>rfl)))
    | (rx_retention_head socketReinit; exact socket_entry _ _)
    | (rx_retention_head clearPeerEndpointSrc; exact endpoint_entry _)
    | (rx_retention_head modifyDev
       apply hoare_modify
       intro w hi
       apply HolderEntryFrames.transport hi
       unfold HolderEntryFrames.fields CurrentSlots.fields HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
       unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
       unfold BaseCoherence.view BaseCoherence.slots BaseCoherence.rows ConfiguredIdentity.view ConfiguredIdentity.state
       cases hd:w.dev <;> simp [hd,rxView])
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (DeviceAuxEntry.Entry cs loans)
       intro _ _
       change Preserves (DeviceAuxEntry.Entry cs loans) _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem worker_entry (kind : Worker) (body : Leanux.M Unit)
    (keeps : Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) body) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (Env.runWorker kind body) := by
  unfold Env.runWorker
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | exact keeps
    | (rx_retention_head modifyAmbient; unfold modifyAmbient; exact ambient _)
    | holder_entry_product_step

/-- Namespace teardown clears carrier/socket/endpoint fields but neither
destroys the device nor discards any charged holder. -/
theorem cleanup_entry : Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) Env.netnsCleanup := by
  unfold Env.netnsCleanup Env.pendingDevice
  simp (config := {zeta := false}) only [unsupported,invariant,getAmbient,peekUnit,resolveUnit,skipCut]
  repeat' first
    | (rx_retention_head Env.runWorker; apply worker_entry)
    | (allocation_release_lift_from WG.M; exact lift_native WG.netnsPreExit preExit_entry)
    | holder_entry_product_step

/-- The original audit executes once. Its normal endpoint entry and stopped
owner journal are obtained from that same run with arbitrary prior history. -/
theorem audit (action : AuditM α) (original : Leanux.M α)
    (erase : ErasesPrefix action original)
    (keeps : Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) original)
    (owner : OwnerChecks.Preserves (RxHistory.audit action)) :
    PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.audit action) := by
  intro w h hi
  obtain ⟨suffix,hist,safe,post⟩ := owner w h hi.2
  refine ⟨suffix,hist,safe,?_⟩
  cases run : (runPrefix (RxHistory.audit action) w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at post
    have actual := ((RxHistory.audit_erases erase) w h).symm.trans run
    exact ⟨(hoare_iff_run _ _ _).mp keeps w out.1 out.2 hi.1 actual,post⟩

theorem up : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.audit envWgUpAudit) :=
  audit _ _ envWgUpAudit_erases up_entry OwnerControlCalls.up

theorem down : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.audit envWgDownAudit) :=
  audit _ _ envWgDownAudit_erases down_entry OwnerControlCalls.down

theorem mtu (n : Nat) : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.audit (setMtuAudit n)) :=
  audit _ _ (setMtuAudit_erases n) (HolderEntryFrames.mtu n) (OwnerControlCalls.mtu n)

theorem route : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.audit routeIntoWg0Audit) :=
  audit _ _ routeIntoWg0Audit_erases (HolderEntryFrames.product routeIntoWg0_sameKernel) OwnerRemaining.route

theorem deladdr (family : Nat) : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.audit (wgDeladdrAudit family)) :=
  audit _ _ (wgDeladdrAudit_erases family) (HolderEntryFrames.product (wgDeladdr_sameKernel family)) (OwnerRemaining.deladdr family)

theorem delroute (family : Nat) : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.audit (wgDelrouteAudit family)) :=
  audit _ _ (wgDelrouteAudit_erases family) (HolderEntryFrames.product (wgDelroute_sameKernel family)) (OwnerRemaining.delroute family)

theorem cleanup : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.audit envNetnsCleanupAudit) :=
  audit _ _ envNetnsCleanupAudit_erases cleanup_entry OwnerControlCalls.netnsCleanup

theorem multicast (family addr : Nat) : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
    (RxHistory.audit (xmitMulticastLoopAudit family addr)) :=
  audit _ _ (xmitMulticastLoopAudit_erases family addr)
    (HolderEntryFrames.product ((pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) family addr))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerTraffic.«0».Leanux.Proofs.WG.OwnerTraffic.multicast) family addr)

end Leanux.Proofs.WG.Queues.RxCredits.HolderEntryControls
