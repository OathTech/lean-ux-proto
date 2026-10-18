import Leanux.Proofs.WG.Queues.HolderEntryDispatch

/-! Concrete poll-free syscall entries. Each normal endpoint is joined with
the owner evidence from the same original observer. Socket and netlink wrappers
retain descriptor failures, errno returns and their actual partial behavior. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem ambient (a : AmbientM α) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (liftAmbient a) :=
  productAmbient_spec a _ (fun _ _ hi=>hi)

private theorem fs (a : FS.M α) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (liftFS a) :=
  productFS_spec a _ (fun _ _ _ _ hi=>hi)

private theorem task (a : TaskM α) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (liftTask a) :=
  productTask_spec a _ (fun _ _ _ hi=>hi)

private theorem seccomp (a : Seccomp.M α) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (liftSeccomp a) :=
  productSeccomp_spec a _ (fun _ _ _ _ hi=>hi)

private theorem native (a : WG.M α) (keeps : Preserves (DeviceAuxEntry.Entry cs loans) a) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (liftWG a) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryControls.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryControls.lift_native) a keeps

macro "holder_pollfree_step" : tactic => `(tactic| first
  | (allocation_release_lift_from FS.M; exact fs _)
  | (allocation_release_lift_from TaskM; exact task _)
  | (allocation_release_lift_from AmbientM; exact ambient _)
  | (allocation_release_lift_from Seccomp.M; exact seccomp _)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ hi=>hi) (fun _ _ hi=>hi.2))
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact HolderEntryFrames.store hi rfl)
  | holder_entry_product_step)

private theorem socket_spec (P : World→Prop)
    (store : ∀ w v,wgStoreView v.wg=wgStoreView w.wg→P w→P v)
    (fd : Nat) (body : Leanux.M Int) (keeps : Preserves P body) :
    Preserves P (socketCallOn fd body) := by
  have files {α : Type} (action : FS.M α) : Preserves P (liftFS action) :=
    productFS_spec action P (fun w _ _ _ hi=>store w _ rfl hi)
  unfold socketCallOn
  apply preserves_bind (files (fdget fd))
  intro f
  split
  · exact preserves_pure _
  · exact preserves_bind keeps (fun result=>preserves_bind (files (fdput f)) (fun _=>preserves_pure result))

/-- The callback remains an arbitrary product action. -/
theorem socket (fd : Nat) (body : Leanux.M Int)
    (keeps : Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) body) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (socketCallOn fd body) :=
  socket_spec _ (fun _ _ same hi=>HolderEntryFrames.store hi same) fd body keeps

theorem netlink (body : Leanux.M Int)
    (keeps : Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) body) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (netlinkRequest body) := by
  unfold netlinkRequest socketCall
  simp (config := {zeta := false}) only [skipCut]
  repeat' first
    | (rx_retention_head socketCallOn; apply socket)
    | holder_pollfree_step
    | (run_tac
         let target ← Lean.Elab.Tactic.getMainTarget
         let some action := target.getAppArgs.back? | throwError "missing source action"
         unless action.consumeMData.headBeta.isFVar do throwError "not the callback"
       exact keeps)

private theorem rtnetlink_spec (P : World→Prop)
    (store : ∀ w v,wgStoreView v.wg=wgStoreView w.wg→P w→P v)
    (body : Leanux.M Int) (keeps : Preserves P body) : Preserves P (rtnetlinkRequest body) := by
  have files {α : Type} (action : FS.M α) : Preserves P (liftFS action) :=
    productFS_spec action P (fun w _ _ _ hi=>store w _ rfl hi)
  -- These source-level task getters/setters use TaskM → FS.M → M.
  have tasks {α : Type} (action : TaskM α) : Preserves P (liftFS (StateT.lift action)) :=
    files _
  have amb {α : Type} (action : AmbientM α) : Preserves P (liftAmbient action) :=
    productAmbient_spec action P (fun w _ hi=>store w _ rfl hi)
  unfold rtnetlinkRequest getFiles getTask modifyFiles modifyTask
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head socketCallOn; apply socket_spec P store)
    | (allocation_release_lift_from FS.M; exact files _)
    | (allocation_release_lift_from TaskM; exact tasks _)
    | (allocation_release_lift_from AmbientM; exact amb _)
    | (rx_retention_head get; exact hoare_consequence (hoare_get P) (fun _ hi=>hi) (fun _ _ hi=>hi.2))
    | (rx_retention_head modify; apply hoare_modify; intro w hi; exact store w _ rfl hi)
    | rx_retention_step
    | (run_tac
         let target ← Lean.Elab.Tactic.getMainTarget
         let some action := target.getAppArgs.back? | throwError "missing source action"
         unless action.consumeMData.headBeta.isFVar do throwError "not the callback"
       exact keeps)

theorem rtnetlink (body : Leanux.M Int)
    (keeps : Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) body) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (rtnetlinkRequest body) :=
  rtnetlink_spec _ (fun _ _ same hi=>HolderEntryFrames.store hi same) body keeps

/-- Reuse the original dispatch's append and stopped-journal contract. The
new native fact concerns only the state returned by that identical execution. -/
theorem checked (call : Syscall)
    (keeps : Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (Leanux.dispatch call)) :
    PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch call) := by
  intro w h hi
  obtain ⟨suffix,hist,safe,post⟩ := OwnerSyscalls.dispatch call w h hi.2
  refine ⟨suffix,hist,safe,?_⟩
  cases run : (runPrefix (RxHistory.syscallDispatch call) w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at post
    have actual := ((RxHistory.syscallDispatch_erases call) w h).symm.trans run
    exact ⟨(hoare_iff_run _ _ _).mp keeps w out.1 out.2 hi.1 actual,post⟩

theorem configuration (attrs : DeviceAttrs) :
    PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch (.wgSet attrs)) :=
  checked _ (netlink _ (native _ (HolderEntry.configuration attrs)))

theorem create : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
    (RxHistory.syscallDispatch .wgCreate) :=
  checked _ (rtnetlink _ (native _ DeviceAuxEntry.create))

theorem up : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
    (RxHistory.syscallDispatch .wgUp) :=
  checked _ (socket _ _ HolderEntryControls.up_entry)

theorem down : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
    (RxHistory.syscallDispatch .wgDown) :=
  checked _ (socket _ _ HolderEntryControls.down_entry)

private theorem deletion_entry :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs [] w.wg) Env.wgDelete := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  obtain ⟨_,absent,account,physical⟩ := HolderDeviceDelete.delete_normal w v hi.1.1 hi.2.1 run
  refine ⟨⟨account,?_,?_⟩,physical,?_⟩
  · simp [BaseCoherence.Inv,BaseCoherence.slots,BaseCoherence.rows,absent]
  · intro s hs
    simp [ConfiguredIdentity.view,absent] at hs
  · apply (CurrentSlots.inv_iff v.wg).mpr
    intro d pid p kid hd
    simp [absent] at hd

/-- The source idle and dump guards justify deletion only with zero external
loans. Descriptor failure is still an ordinary unchanged-entry return. -/
theorem delete : PrefixPreserves (HolderEntry.Inv cs []) OwnerChecks.Safe
    (RxHistory.syscallDispatch .wgDelete) :=
  checked _ (rtnetlink _ deletion_entry)

theorem mtu (n : Nat) : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgSetMtu n)) :=
  checked _ (socket _ _ (HolderEntryFrames.mtu n))

theorem namespaceClose : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
    (RxHistory.syscallDispatch .wgNetnsClose) := by
  apply checked
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  exact HolderEntryFrames.store hi ((ProjectedAction.iff_run _ _ _).mp
    SyscallFrames.netnsClose_sameWGStore w result v run)

private theorem delroute_entry (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg)
      (Env.wgDelroute family named dst plen oif typeCode metric) := by
  unfold Env.wgDelroute
  simp (config := {zeta := false}) only [unsupported]
  repeat' holder_pollfree_step

private theorem addroute_entry (dst plen oif typeCode metric mtu flags : Nat) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg)
      (Env.wgAddroute dst plen oif typeCode metric mtu flags) := by
  unfold Env.wgAddroute
  simp (config := {zeta := false}) only [invariant]
  repeat' holder_pollfree_step

private theorem addaddr_entry (addr plen : Nat) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (Env.wgAddaddr addr plen) := by
  unfold Env.wgAddaddr
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg)
       intro _ _
       change Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) _)
    | holder_pollfree_step

theorem deladdr (family : Nat) : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgDeladdr family)) :=
  checked _ (rtnetlink _ (HolderEntryFrames.product (wgDeladdr_sameKernel family)))

theorem delroute (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgDelroute family named dst plen oif typeCode metric)) :=
  checked _ (rtnetlink _ (delroute_entry family named dst plen oif typeCode metric))

theorem addroute (dst plen oif typeCode metric mtu flags : Nat) :
    PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgAddroute dst plen oif typeCode metric mtu flags)) :=
  checked _ (rtnetlink _ (addroute_entry dst plen oif typeCode metric mtu flags))

theorem addaddr (addr plen : Nat) : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgAddaddr addr plen)) :=
  checked _ (rtnetlink _ (addaddr_entry addr plen))

theorem advance (ticks : Nat) : PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
    (RxHistory.syscallDispatch (.wgAdvance ticks)) := by
  apply checked
  unfold Leanux.dispatch
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head Env.advance; exact HolderEntryFrames.product (advance_sameKernel _))
    | holder_pollfree_step

/-- Exactly the typed filesystem and seccomp dispatch arms. Other constructors
are excluded explicitly; this is not a fallback for traffic or observations. -/
def Ordinary : Syscall → Prop
  | .eventfd2 .. | .dup .. | .dup3 .. | .close .. | .read .. | .write ..
  | .pipe2 .. | .fcntl .. | .epollCreate1 .. | .epollCtl .. | .epollWait ..
  | .seccompInstall .. | .seccompProbe .. | .seccompPrctl .. | .seccompCapdrop | .seccompQuery .. => True
  | _ => False

theorem ordinary (call : Syscall) (selected : Ordinary call) :
    PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe (RxHistory.syscallDispatch call) := by
  apply checked
  cases call with
  | eventfd2 count flags => exact fs _
  | dup fd => exact fs _
  | dup3 oldfd newfd flags => exact fs _
  | close fd => exact fs _
  | read fd count => exact fs _
  | write fd count buf => exact fs _
  | pipe2 flags => exact fs _
  | fcntl fd cmd arg => exact fs _
  | epollCreate1 flags => exact fs _
  | epollCtl epfd op fd events data => exact fs _
  | epollWait epfd maxevents timeout => exact fs _
  | seccompInstall via flags filter len bad mode => exact seccomp _
  | seccompProbe nr args target strict => cases target <;> exact seccomp _
  | seccompPrctl cmd args => exact seccomp _
  | seccompCapdrop => exact seccomp _
  | seccompQuery cmd action flags => exact seccomp _
  | _ => exact False.elim selected

end Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree
