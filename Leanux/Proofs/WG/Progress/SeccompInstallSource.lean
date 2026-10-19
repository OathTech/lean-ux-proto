import Leanux.Seccomp.Syscalls

/-! Four concrete source seams for the original filter-install callers.
Only the preparation/caller callbacks are exposed; attachment, cache, cleanup,
refusal and unsupported paths retain their original operations and order. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompInstall
open Leanux Leanux.Seccomp

def modeWith
    (user : Seccomp.SockFprog → Bool → Seccomp.M (Except Int FilterId))
    (flags : UInt32) (fprog : Seccomp.SockFprog) (badFprog : Bool) : Seccomp.M Int := do
  if ← kbranchCmp .setFilterBadFlags (flags > SECCOMP_FILTER_FLAG_MASK) flags.toNat SECCOMP_FILTER_FLAG_MASK.toNat then
    return errEINVAL
  let three := SECCOMP_FILTER_FLAG_TSYNC ||| SECCOMP_FILTER_FLAG_NEW_LISTENER ||| SECCOMP_FILTER_FLAG_TSYNC_ESRCH
  let both := SECCOMP_FILTER_FLAG_TSYNC ||| SECCOMP_FILTER_FLAG_NEW_LISTENER
  if ← kbranchCmp .setFilterTsync ((flags &&& three) == both) (flags &&& three).toNat both.toNat then
    if ← kbranch .setFilterNewListener true then
      if !(← kbranch .setFilterTsyncEsrch false) then return errEINVAL
  let pair := SECCOMP_FILTER_FLAG_WAIT_KILLABLE_RECV ||| SECCOMP_FILTER_FLAG_NEW_LISTENER
  if ← kbranchCmp .setFilterWaitKillable ((flags &&& pair) == SECCOMP_FILTER_FLAG_WAIT_KILLABLE_RECV)
      (flags &&& pair).toNat SECCOMP_FILTER_FLAG_WAIT_KILLABLE_RECV.toNat then
    if !(← kbranch .setFilterWaitNewListener false) then return errEINVAL
  let id ← match ← user fprog badFprog with
    | .error e =>
      _ ← kbranch .setFilterPrepareErr true
      return e
    | .ok id =>
      _ ← kbranch .setFilterPrepareErr false
      pure id
  if ← kflag .setFilterNewListenerFlag flags SECCOMP_FILTER_FLAG_NEW_LISTENER then
    _root_.Leanux.unsupported "SECCOMP_FILTER_FLAG_NEW_LISTENER (design 9.1)"
  if ← kflag .setFilterTsyncLock flags SECCOMP_FILTER_FLAG_TSYNC then
    if ← kbranch .setFilterTsyncLockFailed false then
      _root_.Leanux.unsupported "mutex_lock_killable(cred_guard_mutex) interrupted by a fatal signal"
  let mut ret : Int := errEINVAL
  let mut prepared : Option FilterId := some id
  if ← kbranch .setFilterCannotAssign (!(← seccompMayAssignMode .filter)) then
    pure ()
  else if ← kbranch .setFilterDuplicateListener (← hasDuplicateListener) then
    ret := errEBUSY
  else
    ret ← seccompAttachFilter flags id
    if ← kbranch .setFilterAttachErr (ret != 0) then
      pure ()
    else
      prepared := none
      seccompAssignMode .filter flags
  if ← kflag .setFilterTsyncUnlock flags SECCOMP_FILTER_FLAG_TSYNC then
    pure ()
  if ← kflag .setFilterNewListenerOut flags SECCOMP_FILTER_FLAG_NEW_LISTENER then
    _root_.Leanux.invariant "NEW_LISTENER reached out_put_fd: its arm leaves the domain first"
  seccompFilterFree prepared
  return ret

theorem mode_factor (flags : UInt32) (fprog : Seccomp.SockFprog) (badFprog : Bool) :
    seccompSetModeFilter flags fprog badFprog =
      modeWith seccompPrepareUserFilter flags fprog badFprog := by
  rfl

def dispatchWith
    (modeFilter : UInt32 → Seccomp.SockFprog → Bool → Seccomp.M Int)
    (op : Nat) (flags : UInt32) (uargs : SeccompArgs) : Seccomp.M Int := do
  if op == SECCOMP_SET_MODE_STRICT then
    _ ← kbranch .doSeccompCaseStrict true
    if ← kbranch .doSeccompStrictFlags (flags != 0) then return errEINVAL
    let nonNull := match uargs with | .null => false | _ => true
    if ← kbranch .doSeccompStrictArgs nonNull then return errEINVAL
    seccompSetModeStrict
  else if op == SECCOMP_SET_MODE_FILTER then
    _ ← kbranch .doSeccompCaseFilter true
    match uargs with
    | .fprog fprog bad => modeFilter flags fprog bad
    | .null =>
      modeFilter flags { len := 0, filter := none } true
    | _ => _root_.Leanux.invariant "SECCOMP_SET_MODE_FILTER with a non-fprog argument"
  else if op == SECCOMP_GET_ACTION_AVAIL then
    _ ← kbranch .doSeccompCaseActionAvail true
    if ← kbranchCmp .doSeccompActionAvailFlags (flags != 0) flags.toNat 0 then return errEINVAL
    match uargs with
    | .action a => seccompGetActionAvail a
    | _ => _root_.Leanux.invariant "SECCOMP_GET_ACTION_AVAIL without an action"
  else if op == SECCOMP_GET_NOTIF_SIZES then
    _ ← kbranch .doSeccompCaseNotifSizes true
    if ← kbranchCmp .doSeccompNotifSizesFlags (flags != 0) flags.toNat 0 then return errEINVAL
    seccompGetNotifSizes
  else
    _ ← kbranch .doSeccompCaseDefault true
    return errEINVAL

theorem dispatch_factor (op : Nat) (flags : UInt32) (uargs : SeccompArgs) :
    doSeccomp op flags uargs = dispatchWith seccompSetModeFilter op flags uargs := by
  rfl

def prctlWith (dispatch : Nat → UInt32 → SeccompArgs → Seccomp.M Int)
    (mode : Nat) (filter : SeccompArgs) : Seccomp.M Int := do
  if mode == 1 then
    _ ← kbranch .prctlSetCaseStrict true
    dispatch SECCOMP_SET_MODE_STRICT 0 .null
  else if mode == 2 then
    _ ← kbranch .prctlSetCaseFilter true
    dispatch SECCOMP_SET_MODE_FILTER 0 filter
  else
    _ ← kbranch .prctlSetCaseDefault true
    return errEINVAL

theorem prctl_factor (mode : Nat) (filter : SeccompArgs) :
    prctlSetSeccomp mode filter = prctlWith doSeccomp mode filter := by
  rfl

def installWith (dispatch : Nat → UInt32 → SeccompArgs → Seccomp.M Int)
    (prctl : Nat → SeccompArgs → Seccomp.M Int) (via : InstallVia) (flags : UInt32) (filter : Option _root_.Leanux.ClassicProg)
    (len : Option Nat) (bad : BadPtr) (mode : Nat) : Seccomp.M Int := do
  let fprog : Seccomp.SockFprog := {
    len := len.getD ((filter.map (·.size)).getD 0)
    filter := filter.map (·.map Seccomp.SockFilter.ofKernel)
    insnsFault := bad == .insns }
  let args := SeccompArgs.fprog fprog (bad == .fprog)
  match via with
  | .seccomp => dispatch SECCOMP_SET_MODE_FILTER flags args
  | .prctl =>
    if flags != 0 then _root_.Leanux.unsupported "flags with the prctl install (prctl passes none)"
    prctl mode args

theorem install_factor (via : InstallVia) (flags : UInt32)
    (filter : Option _root_.Leanux.ClassicProg) (len : Option Nat) (bad : BadPtr) (mode : Nat) :
    sysSeccompInstall via flags filter len bad mode =
      installWith doSeccomp prctlSetSeccomp via flags filter len bad mode := by
  rfl

end Leanux.Proofs.WG.Progress.SeccompInstall
