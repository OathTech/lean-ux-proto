import Leanux.Proofs.WG.Queues.HolderEntryFrames
import Leanux.Proofs.WG.Queues.DumpCallers
import Leanux.Proofs.WG.Queues.BaseCoherenceConfiguration
import Leanux.Proofs.WG.Origins.OwnerSyscalls

/-! Full and stepped dump callers exchange their actual funded cursor while
retaining the outer structural, physical and nullable-slot entry. Normal errno
returns are included; a stopped observer supplies only its reached journal. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderDumpEntry
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders NetlinkDump

private def Extra (w : WGWorld) : Prop :=
  BaseCoherence.Inv w ∧ HolderDeviceCreate.OptionalPhysical w ∧ CurrentSlots.Inv w

private theorem extra_dev (hi : Extra w) (same : v.dev=w.dev) : Extra v := by
  refine ⟨BaseCoherence.transport hi.1 ?_,HolderStopPhysical.optional_cell hi.2.1 ?_,
    CurrentSlots.fields_transport hi.2.2 ?_⟩
  · exact congrArg (fun d : Option Device=>BaseCoherence.view {dev:=d}) same
  · exact congrArg (fun d : Option Device=>RxRing.nativeCell {dev:=d}) same
  · exact congrArg (fun d : Option Device=>CurrentSlots.fields {dev:=d}) same

private theorem dump_extra (action : WG.M α) (frame : SameDump action) :
    Preserves Extra action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact extra_dev hi (congrArg WGStoreView.dev
    ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b run))

private theorem peerGet_extra (pid : PeerId) : Preserves Extra (peerGet pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨BaseCoherence.transport hi.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.peerGet_view pid) w a result v b run),
    HolderStopPhysical.optional_cell hi.2.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp (RxRing.peerGet_frame pid) w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.fields_preserves (CurrentSlots.peerGet_fields pid))
      w a result v b hi.2.2 run⟩

private theorem peerPut_extra (pid : Option PeerId) : Preserves Extra (peerPut pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨BaseCoherence.transport hi.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.peerPut_view pid) w a result v b run),
    HolderStopPhysical.optional_cell hi.2.1
    ((ProjectedAction.iff_run_ambient _ _ _).mp (RxRing.peerPut_frame pid) w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.peerPut_preserves pid) w a result v b hi.2.2 run⟩

private theorem read_extra (pid : PeerId) : Preserves Extra (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  simpa only [(getPeer_normal pid w v p a b run).1] using hi

macro "dump_extra_step" : tactic => `(tactic| first
  | (rx_retention_head getDev; exact dump_extra _ (getDev_sameWGStore.factor dumpStore))
  | (rx_retention_head getPeer; exact read_extra _)
  | (rx_retention_head peerGet; exact peerGet_extra _)
  | (rx_retention_head peerPut; exact peerPut_extra _)
  | (rx_retention_head getPeerDump; exact dump_extra _ ((getPeerDump_sameWGWorld _ _ _).factor dumpView))
  | (rx_retention_head getNlSock; exact dump_extra _ ((getNlSock_sameWGWorld _).factor dumpView))
  | (rx_retention_head setNlSock; exact dump_extra _ (setNlSock_sameDump _ _))
  | (rx_retention_head lookupInterface; exact dump_extra _ ((lookupInterface_sameWGWorld _).factor dumpView))
  | (rx_retention_head coalesce; exact dump_extra _ ((coalesce_sameWGWorld _).factor dumpView))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id Extra
     intro _ _
     change Preserves Extra _)
  | rx_retention_step)

private theorem done_extra (ctx : DumpCtx) : Preserves Extra (wgGetDeviceDone ctx) := by
  unfold wgGetDeviceDone
  simp (config := {zeta := false}) only [branch]
  repeat' dump_extra_step

private theorem tail_extra (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    Preserves Extra (deviceDumpTailSource d ctx skb flags attrs) := by
  unfold deviceDumpTailSource
  simp (config := {zeta := false}) only [WG.orM,WG.andM,requireNotPending,branch,invariant,unsupported]
  repeat' dump_extra_step

private theorem chunk_extra (ctx : DumpCtx) (seq : UInt32) (skb : NlSkb) :
    Preserves Extra (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  repeat' first
    | (rx_retention_head deviceDumpHeaderSource; exact dump_extra _ ((deviceDumpHeader_sameWGStore _ _ _ _).factor dumpStore))
    | (rx_retention_head deviceDumpTailSource; exact tail_extra _ _ _ _ _)
    | dump_extra_step

private theorem socket_extra (fd : Nat) : Preserves Extra (netlinkDump fd) := by
  unfold netlinkDump
  repeat' first
    | (rx_retention_head wgGetDeviceDump; exact chunk_extra _ _ _)
    | (rx_retention_head wgGetDeviceDone; exact done_extra _)
    | dump_extra_step

private theorem start_extra (fd : Nat) (ref : DeviceRef) : Preserves Extra (netlinkDumpStart fd ref) := by
  unfold netlinkDumpStart
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head netlinkDump; exact socket_extra _)
    | dump_extra_step

private theorem recv_extra (fd : Nat) : Preserves Extra (netlinkRecvmsg fd) := by
  unfold netlinkRecvmsg
  repeat' first
    | (rx_retention_head netlinkDump; exact socket_extra _)
    | dump_extra_step

private theorem device_extra (ref : DeviceRef) : Preserves Extra (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact start_extra _ _)
    | (rx_retention_head netlinkRecvmsg; exact recv_extra _)
    | dump_extra_step

private theorem extra_lift (action : WG.M α) (keeps : Preserves Extra action) :
    Preserves (fun w : World=>Extra w.wg) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  exact (hoare_iff_run_ambient _ _ _).mp keeps w.wg w.ambient result v.wg v.ambient hi
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
      action w v result run)

private theorem extra_ambient (action : AmbientM α) :
    Preserves (fun w : World=>Extra w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi=>hi)

private theorem extra_fs (action : FS.M α) :
    Preserves (fun w : World=>Extra w.wg) (liftFS action) :=
  productFS_spec action _ (fun _ _ _ _ hi=>hi)

macro "dump_product_step" : tactic => `(tactic| first
  | (allocation_release_lift_from AmbientM; exact extra_ambient _)
  | (allocation_release_lift_from FS.M; exact extra_fs _)
  | rx_retention_step)

private theorem get_product (ref : DeviceRef) :
    Preserves (fun w : World=>Extra w.wg) (dispatch (.wgGet ref)) := by
  simp only [dispatch,netlinkRequest,socketCall,socketCallOn]
  simp (config := {zeta := false}) only [skipCut,modifyAmbient]
  repeat' dump_product_step
  all_goals exact extra_lift (wgGetDevice ref) (device_extra ref)

private theorem start_product (ref : DeviceRef) :
    Preserves (fun w : World=>Extra w.wg) (dispatch (.wgGetStart ref)) := by
  simp only [dispatch,socketCallOn]
  simp (config := {zeta := false}) only [skipCut,skipCutExactly]
  repeat' dump_product_step
  · exact extra_lift (getNlSock DUMP_FD)
      (dump_extra _ ((getNlSock_sameWGWorld DUMP_FD).factor dumpView))
  · exact extra_lift _ (dump_extra _ (setNlSock_sameDump _ _))
  all_goals exact extra_lift (netlinkDumpStart DUMP_FD ref) (start_extra DUMP_FD ref)

private theorem recv_product :
    Preserves (fun w : World=>Extra w.wg) (dispatch .wgGetRecv) := by
  simp only [dispatch,socketCallOn]
  simp (config := {zeta := false}) only [skipCut,unsupported,modifyAmbient]
  repeat' dump_product_step
  all_goals exact extra_lift (netlinkRecvmsg DUMP_FD) (recv_extra DUMP_FD)

private theorem join (call : Syscall)
    (account : Preserves (fun w : World=>Boundary cs loans w.wg) (dispatch call))
    (extra : Preserves (fun w : World=>Extra w.wg) (dispatch call)) :
    PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch call) := by
  intro w h hi
  obtain ⟨suffix,hist,safe,post⟩ := OwnerSyscalls.dispatch call w h hi.2
  refine ⟨suffix,hist,safe,?_⟩
  cases run : (runPrefix (RxHistory.syscallDispatch call) w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at post
    have actual := ((RxHistory.syscallDispatch_erases call) w h).symm.trans run
    have funded := (hoare_iff_run _ _ _).mp account w out.1 out.2 hi.1.1.1 actual
    have kept := (hoare_iff_run _ _ _).mp extra w out.1 out.2
      ⟨hi.1.1.2.1,hi.1.2.1,hi.1.2.2⟩ actual
    exact ⟨⟨⟨funded,kept.1,HolderAuxiliary.owner_configured post⟩,kept.2⟩,post⟩

/-- The full dump keeps its actual 4096-step bound and exchanges only its
source-funded cursor. No initial cursor absence or completion is assumed. -/
theorem dispatchGet (ref : DeviceRef) :
    PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgGet ref)) := by
  apply join _ ?_ (get_product ref)
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  obtain ⟨holders,funded,stable⟩ := hi
  obtain ⟨next,kept,stable⟩ := dispatchGet_funded ref w v funded stable run
  exact ⟨holders.withCursor 7 next,kept,stable⟩

/-- Starting the stepped socket retains its actual autobind and busy guard. -/
theorem dispatchStart (ref : DeviceRef) :
    PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgGetStart ref)) := by
  apply join _ ?_ (start_product ref)
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  obtain ⟨holders,funded,stable⟩ := hi
  obtain ⟨next,kept,stable⟩ := dispatchStart_funded ref w v funded stable run
  exact ⟨holders.withCursor DUMP_FD next,kept,stable⟩

/-- The actual receive may continue, finish, or reject a dump chunk; every
normal endpoint accounts for its reached cursor and retains the owner checks. -/
theorem dispatchRecv :
    PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
      (RxHistory.syscallDispatch .wgGetRecv) := by
  apply join _ ?_ recv_product
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  obtain ⟨holders,funded,stable⟩ := hi
  obtain ⟨next,kept,stable⟩ := dispatchRecv_funded w v funded stable run
  exact ⟨holders.withCursor DUMP_FD next,kept,stable⟩

end Leanux.Proofs.WG.Queues.RxCredits.HolderDumpEntry
