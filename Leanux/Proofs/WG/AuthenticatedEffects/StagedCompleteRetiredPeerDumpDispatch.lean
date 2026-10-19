import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDumpCallers
import Leanux.Proofs.WG.Lifetimes.SyscallDispatchAudit

/-! The actual dispatcher wrappers retain the exact dump account through
fdget/fdput, autobind and serialization. Only the selected socket cursor may
change, using the same native account already proved for start and receive. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Dump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem during_lift (h : DurableHolders) (fd : Nat) (action : WG.M α)
    (ha : Preserves (During h fd carriers loans) action) :
    Preserves (fun w : World => During h fd carriers loans w.wg) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact (hoare_iff_run_ambient _ _ _).mp ha w.wg w.ambient x v.wg v.ambient hi
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
      action w v x run)

private theorem during_ambient (h : DurableHolders) (fd : Nat) (action : AmbientM α) :
    Preserves (fun w : World => During h fd carriers loans w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi)

/-- The original socket wrapper keeps its actual fdget/fdput behavior and
permits an arbitrary product callback satisfying the displayed invariant. -/
theorem socketCallOn_during (h : DurableHolders) (cursor fd : Nat) (body : Leanux.M Int)
    (hb : Preserves (fun w : World => During h cursor carriers loans w.wg) body) :
    Preserves (fun w : World => During h cursor carriers loans w.wg) (socketCallOn fd body) := by
  unfold socketCallOn
  apply preserves_bind (productFS_spec (fdget fd : FS.M Fd) _ (fun _ _ _ _ hi => hi))
  intro f
  split
  · exact preserves_pure _
  · apply preserves_bind hb
    intro ret
    exact preserves_bind (productFS_spec (fdput f : FS.M Unit) _ (fun _ _ _ _ hi => hi))
      (fun _ => preserves_pure ret)

/-- Both actual socket calls and the allocation-cut stream remain in place.
The body ranges over the full product monad. -/
theorem netlinkRequest_during (h : DurableHolders) (fd : Nat) (body : Leanux.M Int)
    (hb : Preserves (fun w : World => During h fd carriers loans w.wg) body) :
    Preserves (fun w : World => During h fd carriers loans w.wg) (netlinkRequest body) := by
  unfold netlinkRequest socketCall
  apply preserves_bind
  · apply socketCallOn_during
    exact preserves_bind (during_ambient h fd (AmbientM.skipCut allocCuts)) (fun _ =>
      preserves_bind hb (fun ret =>
      preserves_bind (during_ambient h fd (AmbientM.skipCut allocCuts)) (fun _ =>
      preserves_pure ret)))
  intro ret
  exact preserves_bind (socketCallOn_during h fd _ _ (preserves_pure 0))
    (fun _ => preserves_pure ret)

theorem dispatchGet_during (h : DurableHolders) (ref : DeviceRef) :
    Preserves (fun w : World => During h 7 carriers loans w.wg) (dispatch (.wgGet ref)) := by
  simp only [dispatch]
  apply netlinkRequest_during
  apply preserves_bind (during_lift h 7 (wgGetDevice ref) (device_during h ref))
  intro result
  cases result with
  | error e => exact preserves_pure e
  | ok device =>
    exact preserves_bind (during_ambient h 7 (modify fun w => {w with extraOut := [("device",device)]}))
      (fun _ => preserves_pure 0)

theorem dispatchRecv_during (h : DurableHolders) :
    Preserves (fun w : World => During h DUMP_FD carriers loans w.wg) (dispatch .wgGetRecv) := by
  simp only [dispatch]
  apply socketCallOn_during
  apply preserves_bind (during_ambient h DUMP_FD (AmbientM.skipCut allocCuts))
  intro _
  apply preserves_bind (during_lift h DUMP_FD (netlinkRecvmsg DUMP_FD) (receive_during h DUMP_FD))
  intro result
  cases result with
  | none => exact during_ambient h DUMP_FD (AmbientM.unsupported _)
  | some messages =>
    apply preserves_bind (during_ambient h DUMP_FD (AmbientM.skipCut allocCuts))
    intro _
    split
    · apply preserves_bind (during_ambient h DUMP_FD (AmbientM.unsupported _))
      intro _
      exact preserves_bind (during_ambient h DUMP_FD (modify fun w =>
        {w with extraOut := [("messages",Lean.Json.arr (messages.map (·.toJson)).toArray)]}))
        (fun _ => preserves_pure 0)
    · exact preserves_bind (during_ambient h DUMP_FD (modify fun w =>
        {w with extraOut := [("messages",Lean.Json.arr (messages.map (·.toJson)).toArray)]}))
        (fun _ => preserves_pure 0)

/-- Starting the stepped dump retains the actual first-use autobind check.
Its socket update preserves the saved cursor, and only the ensuing native dump
start may exchange that funded reservation. -/
theorem dispatchStart_during (h : DurableHolders) (ref : DeviceRef) :
    Preserves (fun w : World => During h DUMP_FD carriers loans w.wg)
      (dispatch (.wgGetStart ref)) := by
  let P := fun w : World => During h DUMP_FD carriers loans w.wg
  have tail : Preserves P (do
      liftWG (netlinkDumpStart DUMP_FD ref)
      skipCut allocCuts
      pure (0 : Int) : Leanux.M Int) :=
    preserves_bind (during_lift h DUMP_FD _ (start_during h DUMP_FD ref))
      (fun _ => preserves_bind (during_ambient h DUMP_FD (AmbientM.skipCut allocCuts))
      (fun _ => preserves_pure 0))
  have getter : Hoare (liftWG (getNlSock DUMP_FD)) P
      (fun sock w => P w ∧ sock = socketAt DUMP_FD w.wg) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w sock v hi run
    change Except.ok (socketAt DUMP_FD w.wg,w) = Except.ok (sock,v) at run
    cases run
    exact ⟨hi,rfl⟩
  simp only [dispatch]
  apply socketCallOn_during
  apply preserves_bind (during_ambient h DUMP_FD (AmbientM.skipCut allocCuts))
  intro _
  apply hoare_bind _ _ getter
  intro sock
  split
  · apply hoare_bind _ _ (productAmbient_spec
      (AmbientM.skipCutExactly .netlinkAutobindPort 1 allocCuts)
      (fun w : World => P w ∧ sock = socketAt DUMP_FD w.wg) (fun _ _ hi => hi))
    intro _
    apply hoare_bind _ _ (show Hoare (liftWG (setNlSock DUMP_FD {sock with bound := true}))
      (fun w : World => P w ∧ sock = socketAt DUMP_FD w.wg) (fun _ => P) from by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi run
      change Except.ok ((),{w with wg := writeSocket DUMP_FD {sock with bound := true} w.wg}) =
        Except.ok (x,v) at run
      cases run
      obtain ⟨next,account⟩ := hi.1
      have same : activeCursor {sock with bound := true} = activeCursor (socketAt DUMP_FD w.wg) := by
        change activeCursor sock = activeCursor (socketAt DUMP_FD w.wg)
        exact congrArg activeCursor hi.2
      have kept := socket_write account DUMP_FD {sock with bound := true} same
      exact ⟨next,kept⟩)
    intro _
    exact tail
  · exact hoare_consequence tail (fun _ hi => hi.1) (fun _ _ hi => hi)


theorem boundary_dispatch_get (ref : DeviceRef) :
    Preserves (fun w : World => ExactBoundary carriers loans w.wg) (dispatch (.wgGet ref)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  obtain ⟨holders,account⟩ := before
  obtain ⟨next,kept⟩ := (hoare_iff_run _ _ _).mp (dispatchGet_during holders ref)
    w result v (during_initial account 7) run
  exact ⟨holders.withCursor 7 next,kept⟩

theorem boundary_dispatch_start (ref : DeviceRef) :
    Preserves (fun w : World => ExactBoundary carriers loans w.wg) (dispatch (.wgGetStart ref)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  obtain ⟨holders,account⟩ := before
  obtain ⟨next,kept⟩ := (hoare_iff_run _ _ _).mp (dispatchStart_during holders ref)
    w result v (during_initial account DUMP_FD) run
  exact ⟨holders.withCursor DUMP_FD next,kept⟩

theorem boundary_dispatch_receive :
    Preserves (fun w : World => ExactBoundary carriers loans w.wg) (dispatch .wgGetRecv) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  obtain ⟨holders,account⟩ := before
  obtain ⟨next,kept⟩ := (hoare_iff_run _ _ _).mp (dispatchRecv_during holders)
    w result v (during_initial account DUMP_FD) run
  exact ⟨holders.withCursor DUMP_FD next,kept⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Dump
