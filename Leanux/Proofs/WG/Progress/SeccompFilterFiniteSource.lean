import Leanux.Proofs.WG.Progress.SeccompProgramFiniteSource
import Leanux.Seccomp.Filter

/-! Finite concrete filter preparation. The allocation of the filter object
and all program allocations use the finite hidden allocator, in the original
order. This stops before set-mode attachment and the syscall wrappers. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompFilterFinite
open Leanux Leanux.Seccomp

def prepareWith (allocate : Seccomp.M Bool)
    (create : Seccomp.SockFprog → Seccomp.M (Except Int Seccomp.BpfProg))
    (fprog : Seccomp.SockFprog) : Seccomp.M (Except Int FilterId) := do
  let tk ← getCurrent
  if ← kbranchCmp .prepareLenZero (fprog.len == 0 || fprog.len > BPF_MAXINSNS)
      (minusOneU fprog.len 16) 0xfff then
    return .error errEINVAL
  if ← kbranch .prepareLenOverMax (fprog.len > BPF_MAXINSNS) then
    return .error errEINVAL
  if ← kbranch .prepareNoNnp (!tk.noNewPrivs) then
    if ← kbranch .prepareNotCapable (!tk.capSysAdmin) then return .error errEACCES
  if ← kbranch .prepareSfilterNoMem (!(← allocate)) then return .error errENOMEM
  let id := (← get).nextFilter
  modify fun s => { s with nextFilter := s.nextFilter + 1 }
  match ← create fprog with
  | .error e =>
    _ ← kbranchCmp .prepareCreateErr true e 0
    return .error e
  | .ok prog =>
    _ ← kbranchCmp .prepareCreateErr false 0 0
    let flt : SeccompFilter :=
      { id, refs := 1, users := 1, prog := prog.toKernel,
        origProg := prog.origProg.map Seccomp.SockFilter.toKernel }
    modify fun s => { s with filters := s.filters.insert id flt }
    return .ok id

theorem prepare_factor (fprog : Seccomp.SockFprog) :
    seccompPrepareFilter fprog =
      prepareWith (hiddenAlloc .kzallocSfilter) bpfProgCreateFromUser fprog := by
  rfl

def prepare (fprog : Seccomp.SockFprog) : Seccomp.M (Except Int FilterId) :=
  prepareWith (monadLift (hiddenAllocFinite .kzallocSfilter))
    SeccompProgramFinite.create fprog

theorem prepare_source (fprog : Seccomp.SockFprog) :
    seccompPrepareFilter fprog = prepare fprog := by
  rw [prepare_factor]
  unfold prepare
  have allocation : (hiddenAlloc .kzallocSfilter : Seccomp.M Bool) =
      monadLift (hiddenAllocFinite .kzallocSfilter) := by
    change (monadLift (AmbientM.hiddenAlloc .kzallocSfilter) : Seccomp.M Bool) = _
    rw [hiddenAlloc_finite_source]
  rw [allocation]
  have creation : (bpfProgCreateFromUser : Seccomp.SockFprog →
      Seccomp.M (Except Int Seccomp.BpfProg)) = SeccompProgramFinite.create := by
    funext f
    exact SeccompProgramFinite.create_source f
  exact congrArg
    (fun callback => prepareWith (monadLift (hiddenAllocFinite .kzallocSfilter)) callback fprog)
    creation

def userWith (prepare : Seccomp.SockFprog → Seccomp.M (Except Int FilterId))
    (fprog : Seccomp.SockFprog) (badFprog : Bool) : Seccomp.M (Except Int FilterId) := do
  if ← kbranch .userFilterCopyFault badFprog then return .error errEFAULT
  prepare fprog

theorem user_factor (fprog : Seccomp.SockFprog) (badFprog : Bool) :
    seccompPrepareUserFilter fprog badFprog =
      userWith seccompPrepareFilter fprog badFprog := by
  rfl

def user (fprog : Seccomp.SockFprog) (badFprog : Bool) :
    Seccomp.M (Except Int FilterId) := userWith prepare fprog badFprog

theorem user_source (fprog : Seccomp.SockFprog) (badFprog : Bool) :
    seccompPrepareUserFilter fprog badFprog = user fprog badFprog := by
  rw [user_factor]
  unfold user
  exact congrArg (fun callback => userWith callback fprog badFprog)
    (funext prepare_source)

end Leanux.Proofs.WG.Progress.SeccompFilterFinite
