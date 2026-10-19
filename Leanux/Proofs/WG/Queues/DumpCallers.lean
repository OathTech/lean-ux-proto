import Leanux.Proofs.WG.Queues.DumpSockets
import Leanux.Proofs.WG.Lifetimes.SyscallDispatchAudit

/-! The original whole dump caller retains every holder other than its selected
socket cursor, which is exchanged only by the actual start/receive calls. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

/-- One socket may exchange its cursor. Other holders and caller loans remain
in the same combined account throughout the original bounded dump loop. -/
def DuringDump (h : DurableHolders) (fd : Nat) (cs : Ledger)
    (loans : Reservations) (w : WGWorld) : Prop :=
  ∃ next : Option Owner, (h.withCursor fd next).Funded cs loans w ∧ StableRx cs w

theorem duringDump_initial (h : DurableHolders) (fd : Nat)
    (hi : h.Funded cs loans w) (stable : StableRx cs w) :
    DuringDump h fd cs loans w := by
  exact ⟨h.cursorAt fd, by simpa only [withCursor_current] using And.intro hi stable⟩

theorem netlinkDumpStart_during (h : DurableHolders) (fd : Nat) (ref : DeviceRef) :
    Preserves (DuringDump h fd cs loans) (netlinkDumpStart fd ref) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  obtain ⟨old,funded,stable⟩ := hi
  cases x
  obtain ⟨next,kept,stable⟩ := netlinkDumpStart_funded fd ref funded stable a b run
  exact ⟨next,by simpa only [withCursor_twice] using kept,stable⟩

theorem netlinkRecvmsg_during (h : DurableHolders) (fd : Nat) :
    Preserves (DuringDump h fd cs loans) (netlinkRecvmsg fd) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  obtain ⟨old,funded,stable⟩ := hi
  obtain ⟨next,kept,stable⟩ := netlinkRecvmsg_funded fd funded stable a b run
  exact ⟨next,by simpa only [withCursor_twice] using kept,stable⟩

/-- Coalescing may reject malformed chunks, but a normal result retains the
exact native state and therefore the complete supplied holder account. -/
theorem coalesce_funded (messages : List NlMessage) (h : DurableHolders) :
    Preserves (fun w => h.Funded cs loans w ∧ StableRx cs w) (coalesce messages) :=
  (coalesce_sameWGWorld messages).wp (fun w : WGWorld => h.Funded cs loans w ∧ StableRx cs w)

/-- This is the actual 4096-step caller, including the original message
termination tests and final coalescing. No completion or empty-queue premise is
assumed; the contract describes normal endpoints only. -/
theorem wgGetDevice_during (h : DurableHolders) (ref : DeviceRef) :
    Preserves (DuringDump h 7 cs loans) (wgGetDevice ref) := by
  unfold wgGetDevice
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',invariant]
  repeat' first
    | (rx_retention_head netlinkDumpStart; exact netlinkDumpStart_during h _ _)
    | (rx_retention_head netlinkRecvmsg; exact netlinkRecvmsg_during h _)
    | (rx_retention_head coalesce; exact (coalesce_sameWGWorld _).wp (DuringDump h 7 cs loans))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (DuringDump h 7 cs loans)
       intro _ _
       change Preserves (DuringDump h 7 cs loans) _)
    | rx_retention_step

theorem wgGetDevice_funded (ref : DeviceRef) {h : DurableHolders}
    (hi : h.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((wgGetDevice ref).run w).run a = .ok ((result,v),b)) :
    DuringDump h 7 cs loans v :=
  (hoare_iff_run_ambient _ _ _).mp (wgGetDevice_during h ref)
    w a result v b (duringDump_initial h 7 hi stable) run

/-- The unchanged lifetime observer has the same result and actual native
endpoint for every incoming history, including normal errno results. -/
theorem wgGetDevice_observed_funded (ref : DeviceRef) {h : DurableHolders}
    (hi : h.Funded cs loans w) (stable : StableRx cs w)
    (history : List LifetimeEvent) (a b : Ambient)
    (run : (runStatePrefix (wgGetDevicePrefix ref) w a history).1 = .ok ((result,v),b)) :
    DuringDump h 7 cs loans v :=
  wgGetDevice_funded ref hi stable a b
    ((wgGetDevicePrefix_erases ref w a history).symm.trans run)

private theorem duringDump_lift (h : DurableHolders) (fd : Nat) (action : WG.M α)
    (ha : Preserves (DuringDump h fd cs loans) action) :
    Preserves (fun w : World => DuringDump h fd cs loans w.wg) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact (hoare_iff_run_ambient _ _ _).mp ha w.wg w.ambient x v.wg v.ambient hi
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
      action w v x run)

private theorem duringDump_ambient (h : DurableHolders) (fd : Nat) (action : AmbientM α) :
    Preserves (fun w : World => DuringDump h fd cs loans w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi)

/-- The original socket wrapper keeps its actual fdget/fdput behavior and
permits an arbitrary product callback satisfying the displayed invariant. -/
theorem socketCallOn_duringDump (h : DurableHolders) (cursor fd : Nat) (body : Leanux.M Int)
    (hb : Preserves (fun w : World => DuringDump h cursor cs loans w.wg) body) :
    Preserves (fun w : World => DuringDump h cursor cs loans w.wg) (socketCallOn fd body) := by
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
theorem netlinkRequest_duringDump (h : DurableHolders) (fd : Nat) (body : Leanux.M Int)
    (hb : Preserves (fun w : World => DuringDump h fd cs loans w.wg) body) :
    Preserves (fun w : World => DuringDump h fd cs loans w.wg) (netlinkRequest body) := by
  unfold netlinkRequest socketCall
  apply preserves_bind
  · apply socketCallOn_duringDump
    exact preserves_bind (duringDump_ambient h fd (AmbientM.skipCut allocCuts)) (fun _ =>
      preserves_bind hb (fun ret =>
      preserves_bind (duringDump_ambient h fd (AmbientM.skipCut allocCuts)) (fun _ =>
      preserves_pure ret)))
  intro ret
  exact preserves_bind (socketCallOn_duringDump h fd _ _ (preserves_pure 0))
    (fun _ => preserves_pure ret)

theorem dispatchGet_during (h : DurableHolders) (ref : DeviceRef) :
    Preserves (fun w : World => DuringDump h 7 cs loans w.wg) (dispatch (.wgGet ref)) := by
  simp only [dispatch]
  apply netlinkRequest_duringDump
  apply preserves_bind (duringDump_lift h 7 (wgGetDevice ref) (wgGetDevice_during h ref))
  intro result
  cases result with
  | error e => exact preserves_pure e
  | ok device =>
    exact preserves_bind (duringDump_ambient h 7 (modify fun w => {w with extraOut := [("device",device)]}))
      (fun _ => preserves_pure 0)

theorem dispatchRecv_during (h : DurableHolders) :
    Preserves (fun w : World => DuringDump h DUMP_FD cs loans w.wg) (dispatch .wgGetRecv) := by
  simp only [dispatch]
  apply socketCallOn_duringDump
  apply preserves_bind (duringDump_ambient h DUMP_FD (AmbientM.skipCut allocCuts))
  intro _
  apply preserves_bind (duringDump_lift h DUMP_FD (netlinkRecvmsg DUMP_FD) (netlinkRecvmsg_during h DUMP_FD))
  intro result
  cases result with
  | none => exact duringDump_ambient h DUMP_FD (AmbientM.unsupported _)
  | some messages =>
    apply preserves_bind (duringDump_ambient h DUMP_FD (AmbientM.skipCut allocCuts))
    intro _
    split
    · apply preserves_bind (duringDump_ambient h DUMP_FD (AmbientM.unsupported _))
      intro _
      exact preserves_bind (duringDump_ambient h DUMP_FD (modify fun w =>
        {w with extraOut := [("messages",Lean.Json.arr (messages.map (·.toJson)).toArray)]}))
        (fun _ => preserves_pure 0)
    · exact preserves_bind (duringDump_ambient h DUMP_FD (modify fun w =>
        {w with extraOut := [("messages",Lean.Json.arr (messages.map (·.toJson)).toArray)]}))
        (fun _ => preserves_pure 0)

/-- Starting the stepped dump retains the actual first-use autobind check.
Its socket update preserves the saved cursor, and only the ensuing native dump
start may exchange that funded reservation. -/
theorem dispatchStart_during (h : DurableHolders) (ref : DeviceRef) :
    Preserves (fun w : World => DuringDump h DUMP_FD cs loans w.wg)
      (dispatch (.wgGetStart ref)) := by
  let P := fun w : World => DuringDump h DUMP_FD cs loans w.wg
  have tail : Preserves P (do
      liftWG (netlinkDumpStart DUMP_FD ref)
      skipCut allocCuts
      pure (0 : Int) : Leanux.M Int) :=
    preserves_bind (duringDump_lift h DUMP_FD _ (netlinkDumpStart_during h DUMP_FD ref))
      (fun _ => preserves_bind (duringDump_ambient h DUMP_FD (AmbientM.skipCut allocCuts))
      (fun _ => preserves_pure 0))
  have getter : Hoare (liftWG (getNlSock DUMP_FD)) P
      (fun sock w => P w ∧ sock = socketAt DUMP_FD w.wg) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w sock v hi run
    change Except.ok (socketAt DUMP_FD w.wg,w) = Except.ok (sock,v) at run
    cases run
    exact ⟨hi,rfl⟩
  simp only [dispatch]
  apply socketCallOn_duringDump
  apply preserves_bind (duringDump_ambient h DUMP_FD (AmbientM.skipCut allocCuts))
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
      obtain ⟨next,funded,stable⟩ := hi.1
      have same : activeCursor {sock with bound := true} = activeCursor (socketAt DUMP_FD w.wg) := by
        change activeCursor sock = activeCursor (socketAt DUMP_FD w.wg)
        exact congrArg activeCursor hi.2
      have kept := socket_write_funded funded stable DUMP_FD {sock with bound := true} same
      exact ⟨next,kept⟩)
    intro _
    exact tail
  · exact hoare_consequence tail (fun _ hi => hi.1) (fun _ _ hi => hi)

/-- The actual dispatcher result, including ordinary errno returns, retains
all supplied noncursor holders and the caller's transient loans. -/
theorem dispatchGet_funded (ref : DeviceRef) {h : DurableHolders} (w v : World)
    (hi : h.Funded cs loans w.wg) (stable : StableRx cs w.wg)
    (run : (dispatch (.wgGet ref)).run w = .ok (result,v)) :
    DuringDump h 7 cs loans v.wg :=
  (hoare_iff_run _ _ _).mp (dispatchGet_during h ref)
    w result v (duringDump_initial h 7 hi stable) run

/-- The existing audit observer gives the identical native accounting at its
normal endpoint, for arbitrary incoming history. No endpoint is asserted for Stop. -/
theorem dispatchGet_observed_funded (ref : DeviceRef) {h : DurableHolders} (w v : World)
    (hi : h.Funded cs loans w.wg) (stable : StableRx cs w.wg)
    (history : List AuditEvent)
    (run : (runPrefix (dispatchAudit (.wgGet ref)) w history).1 = .ok (result,v)) :
    DuringDump h 7 cs loans v.wg :=
  dispatchGet_funded ref w v hi stable
    ((dispatchAudit_erases (.wgGet ref) w history).symm.trans run)

/-- The actual dispatcher result, including ordinary errno returns, retains
all supplied noncursor holders and the caller's transient loans. -/
theorem dispatchStart_funded (ref : DeviceRef) {h : DurableHolders} (w v : World)
    (hi : h.Funded cs loans w.wg) (stable : StableRx cs w.wg)
    (run : (dispatch (.wgGetStart ref)).run w = .ok (result,v)) :
    DuringDump h DUMP_FD cs loans v.wg :=
  (hoare_iff_run _ _ _).mp (dispatchStart_during h ref)
    w result v (duringDump_initial h DUMP_FD hi stable) run

/-- The existing audit observer gives the identical native accounting at its
normal endpoint, for arbitrary incoming history. No endpoint is asserted for Stop. -/
theorem dispatchStart_observed_funded (ref : DeviceRef) {h : DurableHolders} (w v : World)
    (hi : h.Funded cs loans w.wg) (stable : StableRx cs w.wg)
    (history : List AuditEvent)
    (run : (runPrefix (dispatchAudit (.wgGetStart ref)) w history).1 = .ok (result,v)) :
    DuringDump h DUMP_FD cs loans v.wg :=
  dispatchStart_funded ref w v hi stable
    ((dispatchAudit_erases (.wgGetStart ref) w history).symm.trans run)

/-- The actual dispatcher result, including ordinary errno returns, retains
all supplied noncursor holders and the caller's transient loans. -/
theorem dispatchRecv_funded {h : DurableHolders} (w v : World)
    (hi : h.Funded cs loans w.wg) (stable : StableRx cs w.wg)
    (run : (dispatch .wgGetRecv).run w = .ok (result,v)) :
    DuringDump h DUMP_FD cs loans v.wg :=
  (hoare_iff_run _ _ _).mp (dispatchRecv_during h)
    w result v (duringDump_initial h DUMP_FD hi stable) run

/-- The existing audit observer gives the identical native accounting at its
normal endpoint, for arbitrary incoming history. No endpoint is asserted for Stop. -/
theorem dispatchRecv_observed_funded {h : DurableHolders} (w v : World)
    (hi : h.Funded cs loans w.wg) (stable : StableRx cs w.wg)
    (history : List AuditEvent)
    (run : (runPrefix (dispatchAudit .wgGetRecv) w history).1 = .ok (result,v)) :
    DuringDump h DUMP_FD cs loans v.wg :=
  dispatchRecv_funded w v hi stable
    ((dispatchAudit_erases .wgGetRecv w history).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
