import Leanux.Proofs.WG.Queues.HolderDeviceCreate
import Leanux.Proofs.WG.Queues.HolderDeviceStop
import Leanux.Proofs.WG.Queues.HolderBaseRetirement
import Leanux.Proofs.WG.Queues.RxDrainBoundary
import Leanux.Proofs.WG.Queues.JointDelete
import Leanux.Proofs.WG.Origins.OwnerControlCalls

/-! Actual environment deletion first establishes an empty receive ledger and
inactive dump cursors. These are normal-return cuts of the original guards;
no state is assigned to a Stop. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders HolderDeviceCreate Configuration

/-- The literal environment prefix before the native deletion callback. -/
def guards : Leanux.M Unit := do
  if (← getWG).dev.isSome then Env.requireIdleDevice
  let pending (sock : WG.NlSock) : Bool :=
    sock.cbRunning || sock.queue.any fun chunk => chunk.messages.any fun m => match m with | .done .. => true | _ => false
  let k ← getWG
  if pending k.nlSock7 || pending k.nlSock8 then
    unsupported "a delete with a stepped dump pending (the dump's cursor holds the device reference; the guest refuses wg_delete_with_dump_pending)"

/-- Both actual guards preserve the whole product on normal return. The
physical witness is used only to discharge the idle receive ledger. -/
theorem guards_normal (w v : World) (hi : Boundary cs loans w.wg)
    (physical : OptionalPhysical w.wg) (run : guards.run w=.ok ((),v)) :
    v=w ∧ cs=[] ∧ activeCursor w.wg.nlSock7=none ∧ activeCursor w.wg.nlSock8=none := by
  let tail : Leanux.M Unit := do
    let pending (sock : WG.NlSock) : Bool :=
      sock.cbRunning || sock.queue.any fun chunk => chunk.messages.any fun m => match m with | .done .. => true | _ => false
    let k ← getWG
    if pending k.nlSock7 || pending k.nlSock8 then
      unsupported "a delete with a stepped dump pending (the dump's cursor holds the device reference; the guest refuses wg_delete_with_dump_pending)"
  have finish (u z : World) (hr : tail.run u=.ok ((),z)) :
      z=u ∧ activeCursor u.wg.nlSock7=none ∧ activeCursor u.wg.nlSock8=none := by
    simp only [tail,StateT.run_bind,
      show (getWG : Leanux.M WGWorld).run u=.ok (u.wg,u) from rfl,
      CounterWindow.except_ok_bind] at hr
    split at hr
    · cases hr
    · rename_i quiet
      cases hr
      have flags : u.wg.nlSock7.cbRunning=false ∧ u.wg.nlSock8.cbRunning=false := by
        simp only [Bool.or_eq_true,not_or,Bool.not_eq_true] at quiet
        exact ⟨quiet.1.1,quiet.2.1⟩
      exact ⟨rfl,by simp [activeCursor,flags.1],by simp [activeCursor,flags.2]⟩
  change ((if w.wg.dev.isSome then Env.requireIdleDevice >>= fun _ => tail else tail).run w)=.ok ((),v) at run
  cases hd:w.wg.dev with
  | none =>
    simp only [hd,Option.isSome_none,Bool.false_eq_true,ite_false] at run
    obtain ⟨same,c7,c8⟩ := finish w v run
    exact ⟨same,(HolderDeviceCreate.absent hi hd).1,c7,c8⟩
  | some d =>
    simp only [hd,Option.isSome_some,ite_true,MaterialOrigin.bind_ok] at run
    obtain ⟨u,middle,idle,rest⟩ := run
    cases u
    have same := (idleDevice_normal w middle idle).1
    subst middle
    obtain ⟨same,c7,c8⟩ := finish w v rest
    rcases physical with absent | ⟨epoch,n,history,ring⟩
    · simp [hd] at absent
    · obtain ⟨h,funded,stable⟩ := hi
      exact ⟨same,(idleDevice_empty w w cs (h.owners++loans) funded.carriers stable ring idle).1,c7,c8⟩

/-- A retired device has neither a physical ring nor any charged receive
object. Inactive cursors are required explicitly. -/
theorem absent_boundary (w : WGWorld) (absent : w.dev=none)
    (c7 : activeCursor w.nlSock7=none) (c8 : activeCursor w.nlSock8=none) :
    Boundary [] [] w ∧ OptionalPhysical w := by
  constructor
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HolderDeviceCreate.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceCreate.empty_boundary)
      (show ∀ d, w.dev=some d → _ from by intro d hd; simp [absent] at hd) c7 c8
  · exact Or.inl absent

private def Clear (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  Boundary cs loans w ∧ activeCursor w.nlSock7=none ∧ activeCursor w.nlSock8=none

private theorem clear_frame (action : WG.M α) (keeps : Preserves (Boundary cs loans) action)
    (frame : ∀ initial, Preserves (Frame initial) action) : Preserves (Clear cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  have out := (hoare_iff_run_ambient _ _ _).mp keeps w a x v b hi.1 run
  have fields := ((hoare_iff_run_ambient _ _ _).mp (frame w) w a x v b (Frame.refl w) run).passive
  exact ⟨out,(congrArg (fun p => p.2.2.1) fields).trans hi.2.1,
    (congrArg (fun p => p.2.2.2) fields).trans hi.2.2⟩

private theorem clear_work (action : WG.M α)
    (keeps : ∀ original, Preserves (DuringWork original cs loans) action) :
    Preserves (Clear cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  obtain ⟨⟨h,funded,stable⟩,c7,c8⟩ := hi
  obtain ⟨out,rest,kept,stableOut⟩ := (hoare_iff_run_ambient _ _ _).mp (keeps h)
    w a x v b (duringWork_initial funded stable) run
  refine ⟨⟨out,kept,stableOut⟩,?_,?_⟩
  · rw [←kept.aligned.cursor7,rest.cursor7,funded.aligned.cursor7,c7]
  · rw [←kept.aligned.cursor8,rest.cursor8,funded.aligned.cursor8,c8]

private theorem clear_modify (f : Device → Device)
    (same : ∀ w : WGWorld,HolderEncrypt.fields {w with dev:=w.dev.map f}=HolderEncrypt.fields w) :
    Preserves (Clear cs loans) (modifyDev f) := by
  apply hoare_modify
  intro w hi
  exact ⟨HolderEncrypt.boundary_fields hi.1 (same w),hi.2⟩

private theorem clear_read : Preserves (Clear cs loans) getDev := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a d v b hi run
  exact (DecryptCarrier.getDev_current a b run).1 ▸ hi

private theorem clear_socket (new4 new6 : Option Nat) :
    Preserves (Clear cs loans) (socketReinit new4 new6) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp (socketReinit_sameSocket new4 new6)
    w a x v b run
  refine ⟨(hoare_iff_run_ambient _ _ _).mp (HolderDeviceStop.socket new4 new6) w a x v b hi.1 run,?_,?_⟩
  · exact (congrArg (fun s : WGOwnedView => activeCursor s.nlSock7) fields).trans hi.2.1
  · exact (congrArg (fun s : WGOwnedView => activeCursor s.nlSock8) fields).trans hi.2.2

private theorem purge_frame (pid : PeerId) (initial : WGWorld) :
    Preserves (Frame initial) (purgeStagedPackets pid) := by
  unfold purgeStagedPackets
  repeat' holder_work_step initial

private theorem reset_frame (pid : PeerId) (initial : WGWorld) :
    Preserves (Frame initial) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  simp only [hiddenClock64]
  repeat' holder_work_step initial

/-- Shutdown retains the absence of dump cursor obligations in addition to
its funded boundary; queued clear work uses its actual surviving holder list. -/
theorem down_clear : Preserves (Clear cs loans) wgDown := by
  have stop : Preserves (Clear cs loans) wgStop := by
    unfold wgStop
    simp (config := {zeta := false}) only [requireNotPending,branch,unsupported]
    repeat' first
      | (rx_retention_head getDev; exact clear_read)
      | (rx_retention_head purgeStagedPackets; exact clear_frame _ (HolderTimers.purge_boundary _) (purge_frame _))
      | (rx_retention_head timersStop; exact clear_work _ (fun _ => timersStop_preserves _))
      | (rx_retention_head handshakeClear; exact clear_frame _ (HolderDeviceStop.handshake _) (HolderWorkFrames.handshakeClear_frame _))
      | (rx_retention_head keypairsClear; exact clear_work _ (fun _ => keypairsClear_preserves _))
      | (rx_retention_head resetLastSentHandshake; exact clear_frame _ (HolderDeviceStop.reset _) (reset_frame _))
      | (rx_retention_head socketReinit; exact clear_socket _ _)
      | (rx_retention_head modifyDev
         apply clear_modify
         intro w
         unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
         unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
         cases hd:w.dev <;> simp [hd,rxView])
      | (rx_retention_head ForIn.forIn
         apply list_view_spec id (Clear cs loans)
         intro x u
         change Preserves (Clear cs loans) _)
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Clear cs loans))
      | rx_retention_step
  unfold wgDown
  apply preserves_bind
  · apply clear_modify
    intro w
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    cases hd:w.dev <;> simp [hd,rxView]
  · intro _; exact stop

private theorem remove_clear : Preserves (Clear cs loans) peerRemoveAll := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  cases x
  obtain ⟨⟨h,funded,stable⟩,c7,c8⟩ := hi
  obtain ⟨out,rest,kept,stableOut⟩ := peerRemoveAll_funded funded stable a b run
  refine ⟨⟨out,kept,stableOut⟩,?_,?_⟩
  · rw [←kept.aligned.cursor7,rest.cursor7]
    exact funded.aligned.cursor7.trans c7
  · rw [←kept.aligned.cursor8,rest.cursor8]
    exact funded.aligned.cursor8.trans c8

private theorem finish_cursors : Preserves
    (fun w : WGWorld => activeCursor w.nlSock7=none ∧ activeCursor w.nlSock8=none)
    (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish) := by
  let P := fun w : WGWorld => activeCursor w.nlSock7=none ∧ activeCursor w.nlSock8=none
  have store {α : Type} (a : WG.M α) (frame : SameWGStore a) : Preserves P a := by
    apply hoare_consequence (frame.wp (fun s : WGStoreView => activeCursor s.nlSock7=none ∧ activeCursor s.nlSock8=none))
    all_goals intro; intros; assumption
  have limiter : Preserves P ratelimiterUninit := by
    exact ratelimiterUninit_sameRatelimiter.wp
      (fun s : WGStoreView => activeCursor s.nlSock7=none ∧ activeCursor s.nlSock8=none)
  change Preserves P _
  index_unfold _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head getDev; exact store _ getDev_sameWGStore)
    | (rx_retention_head mayHaveSlept; exact store _ mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit; exact limiter)
    | (rx_retention_head retireDeviceUnits; exact store _ retireDeviceUnits_sameWGStore)
    | (rx_retention_head modifyDev; apply hoare_modify; intro w hi; exact hi)
    | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ P)
    | rx_retention_step

private theorem finish_retired : Hoare
    (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish)
    (Clear [] []) (fun _ w => w.dev=none ∧ Boundary [] [] w ∧ OptionalPhysical w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  cases x
  have absent : v.dev=none := by
    have gone := (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish_none) w v a b run
    simpa [AllowedIps.routingView] using gone
  have cursors := (hoare_iff_run_ambient _ _ _).mp finish_cursors w a () v b hi.2 run
  exact ⟨absent,absent_boundary v absent cursors.1 cursors.2⟩

/-- The native destruction cut is used only after the real guards established
an empty ledger and inactive cursors. Queued-work failures remain partial. -/
theorem destruct_empty : Hoare wgDestruct (Clear [] [])
    (fun _ w => w.dev=none ∧ Boundary [] [] w ∧ OptionalPhysical w) := by
  rw [wgDestruct_factor]
  unfold destructWith
  apply hoare_bind _ _ (show Preserves (Clear [] []) (modifyDev fun d => {d with creatingNet:=false,incomingPort:=0}) from ?_)
  · intro _
    apply hoare_bind _ _ (clear_socket none none)
    intro _
    apply hoare_bind _ _ remove_clear
    intro _
    exact finish_retired
  · apply clear_modify
    intro w
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    cases hd:w.dev <;> simp [hd,rxView]

private theorem lift_spec {a : WG.M α} {P : WGWorld → Prop} {Q : α → WGWorld → Prop}
    (rule : Hoare a P Q) : Hoare (liftWG a) (fun w => P w.wg) (fun x w => Q x w.wg) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  exact (hoare_iff_run_ambient _ _ _).mp rule w.wg w.ambient x v.wg v.ambient hi
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) a w v x run)

private theorem product_clear (a : Leanux.M α) (frame : SameProductStore a) :
    Preserves (fun w : World => Clear cs loans w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  have fields := congrArg (fun s : ProductStore43 => s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w x v run)
  have keep := Frame.of_store fields
  exact ⟨HolderEncrypt.boundary_fields hi.1 (congrArg
    (fun s : WGStoreView => HolderEncrypt.fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8}) fields),
    (congrArg (fun p => p.2.2.1) keep.passive).trans hi.2.1,
    (congrArg (fun p => p.2.2.2) keep.passive).trans hi.2.2⟩

/-- The source suffix after the absent-device test; callback domains remain
arbitrary product actions with their explicit preservation contracts. -/
private def deleteBody (onDown onUnregister : Leanux.M Unit) : Leanux.M Int := do
  if (← getDev).running then
    WG.wgDown
    onDown
  skipCut allocCuts
  onUnregister
  mayHaveSlept
  WG.wgDestruct
  return 0

private theorem deleteBody_spec (onDown onUnregister : Leanux.M Unit)
    (down : Preserves (fun w : World => Clear [] [] w.wg) onDown)
    (unregister : Preserves (fun w : World => Clear [] [] w.wg) onUnregister) :
    Hoare (deleteBody onDown onUnregister) (fun w => Clear [] [] w.wg)
      (fun _ w => w.wg.dev=none ∧ Boundary [] [] w.wg ∧ OptionalPhysical w.wg) := by
  let P := fun w : World => Clear [] [] w.wg
  let beforeDrop : Leanux.M Unit := do
    if (← getDev).running then
      WG.wgDown
      onDown
    skipCut allocCuts
    onUnregister
    mayHaveSlept
  have prefixRule : Preserves P beforeDrop := by
    unfold beforeDrop
    simp (config := {zeta := false}) only [skipCut]
    repeat' first
      | exact down
      | exact unregister
      | (allocation_release_lift_from WG.M; first
          | exact lift_spec clear_read
          | exact lift_spec down_clear
          | exact product_clear _ (liftWG_sameProductStore _ mayHaveSlept_sameWGStore))
      | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ P (fun _ _ hi => hi))
      | rx_retention_step
  have factor : deleteBody onDown onUnregister = (beforeDrop >>= fun _ => liftWG wgDestruct >>= fun _ => pure 0) := by
    simp only [deleteBody,beforeDrop,bind_assoc,bind_if_source]
    rfl
  rw [factor]
  apply hoare_bind _ _ prefixRule
  intro _
  apply hoare_bind _ _ (lift_spec destruct_empty)
  intro _
  exact preserves_pure 0

private def notifyDown : Leanux.M Unit := do
  Net.Fib.rtCacheFlush
  Net.Fib.netdevDown WG0_IFINDEX
  modifyRouting fun w => {w with defaultRoute6:=false,addrs6:=[],ipv6Gen:=w.ipv6Gen+1}

private def notifyUnregister : Leanux.M Unit := do
  Env.inetdevDestroy
  Net.Fib.netdevUnregister WG0_IFINDEX
  modifyRouting fun w => {w with addrs6:=[],defaultRoute6:=false,ipv6Gen:=w.ipv6Gen+1}

/-- Exact original environment source, including the separate idle and dump
checks and the absent-device errno return. -/
theorem source_factor : Env.wgDelete = (do
    guards
    if (← getWG).dev.isNone then return -ENODEV
    deleteBody notifyDown notifyUnregister) := by
  rw [envDelete_factor]
  simp only [envDeleteWith,guards,deleteBody,notifyDown,notifyUnregister,
    bind_assoc,bind_if_source,pure_bind]
  rfl

private theorem routing_clear (a : Net.M α) :
    Preserves (fun w : World => Clear cs loans w.wg)
      (MonadLift.monadLift (MonadLift.monadLift a : WG.M α) : Leanux.M α) :=
  product_clear _ (liftWG_sameProductStore _ (liftRouting_sameWGStore a))

private theorem notifyDown_clear : Preserves (fun w : World => Clear cs loans w.wg) notifyDown := by
  unfold notifyDown modifyRouting
  repeat' first
    | (allocation_release_lift_from WG.M; exact routing_clear _)
    | (allocation_release_lift_from Net.M; exact routing_clear _)
    | rx_retention_step

private theorem notifyUnregister_clear : Preserves (fun w : World => Clear cs loans w.wg) notifyUnregister := by
  unfold notifyUnregister modifyRouting
  apply preserves_bind (product_clear _
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.inetdevDestroy_store))
  intro _
  repeat' first
    | (allocation_release_lift_from WG.M; exact routing_clear _)
    | (allocation_release_lift_from Net.M; exact routing_clear _)
    | rx_retention_step

/-- Every normal actual environment deletion, including -ENODEV, has an
absent device and an empty receive ledger. External loans are zero at this
boundary; the real idle and pending-dump guards supply the required facts. -/
theorem delete_normal (w v : World) (hi : Boundary cs [] w.wg)
    (physical : OptionalPhysical w.wg) (run : Env.wgDelete.run w=.ok (ret,v)) :
    cs=[] ∧ v.wg.dev=none ∧ Boundary cs [] v.wg ∧ OptionalPhysical v.wg := by
  rw [source_factor,MaterialOrigin.bind_ok] at run
  obtain ⟨u,middle,guard,rest⟩ := run
  cases u
  obtain ⟨same,empty,c7,c8⟩ := guards_normal w middle hi physical guard
  subst middle
  subst cs
  simp only [StateT.run_bind,
    show (getWG : Leanux.M WGWorld).run w=.ok (w.wg,w) from rfl,
    CounterWindow.except_ok_bind] at rest
  split at rest
  · rename_i absent
    have noDev : w.wg.dev=none := Option.isNone_iff_eq_none.mp absent
    cases rest
    exact ⟨rfl,noDev,hi,Or.inl noDev⟩
  · exact ⟨rfl,(hoare_iff_run _ _ _).mp
      (deleteBody_spec notifyDown notifyUnregister notifyDown_clear notifyUnregister_clear)
      w ret v ⟨hi,c7,c8⟩ rest⟩

/-- Original product-state deletion preserves the complete supplied boundary
and its optional physical witness on normal returns. -/
theorem delete : Preserves (fun w : World => Boundary cs [] w.wg ∧ OptionalPhysical w.wg) Env.wgDelete := by
  apply (hoare_iff_run _ _ _).mpr
  intro w ret v hi run
  have out := delete_normal w v hi.1 hi.2 run
  exact ⟨out.2.2.1,out.2.2.2⟩

end Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete
