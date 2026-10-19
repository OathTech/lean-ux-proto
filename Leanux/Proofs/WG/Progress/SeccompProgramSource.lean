import Leanux.Seccomp.Translate

/-! Exact original caller factors. Only the conversion/migration/preparation
callbacks are exposed; allocation remains a field of the supplied operations.
No termination property is asserted for arbitrary SeccompM instances. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompProgram
open Leanux Leanux.Seccomp

def migrateWith {m : Type → Type} [SeccompM m]
    (convert : Seccomp.ClassicProg → Option Nat → Bool → Nat → m (Except Int ConvertOut)) (insns : Seccomp.ClassicProg) (orig : Seccomp.ClassicProg) : m (Except Int Seccomp.BpfProg) := do
  if ← Seccomp.branch .migOldProgNoMem (!(← Seccomp.alloc .kmemdupArrayOldProg)) then return .error errENOMEM
  -- 1st pass: the new length
  let c1 ← match ← convert insns none false 0 with
    | .error e =>
      let _ ← Seccomp.branch .migConvert1Err true
      return .error e
    | .ok c =>
      let _ ← Seccomp.branch .migConvert1Err false
      pure c
  -- bpf_prog_realloc (core.c:245-272), below the cut: one page allocation when the image grows
  if ← Seccomp.branch .migReallocNoMem (!(← Seccomp.alloc .bpfProgReallocImage)) then return .error errENOMEM
  -- 2nd pass: the remapping
  let c2 ← match ← convert insns (some 0) c1.seenLdAbs c1.newLen with
    | .error e =>
      let _ ← Seccomp.branch .migConvert2Err true
      return .error e
    | .ok c =>
      let _ ← Seccomp.branch .migConvert2Err false
      pure c
  -- the kind-309 hook: at the end of the second pass, before the pages are locked
  checkTranslatedRecords c2.insns
  -- bpf_prog_select_runtime (core.c:2527-2579), below the cut: no error on these programs
  if ← Seccomp.branch .migSelectRuntimeErr false then
    Seccomp.invariant "bpf_migrate_filter: bpf_prog_select_runtime failed; the cut assumes it cannot"
  return .ok { insns := c2.insns, len := c2.newLen, stackDepth := c2.stackDepth, origProg := orig }

theorem migrate_source {m : Type → Type} [SeccompM m] (insns orig : Seccomp.ClassicProg) :
    (bpfMigrateFilter insns orig : m _) =
      migrateWith bpfConvertFilter insns orig := rfl

def prepareWith {m : Type → Type} [SeccompM m]
    (migrate : Seccomp.ClassicProg → Seccomp.ClassicProg → m (Except Int Seccomp.BpfProg)) (insns : Seccomp.ClassicProg) (orig : Seccomp.ClassicProg) : m (Except Int Seccomp.BpfProg) := do
  -- fp->bpf_func = NULL; fp->jited = 0;
  match ← bpfCheckClassic insns with
  | .error e =>
    let _ ← Seccomp.branch .prepCheckClassicErr true
    -- __bpf_prog_release(fp): the type is BPF_PROG_TYPE_UNSPEC, orig_prog is saved
    let _ ← Seccomp.branch .releaseSocketFilter false
    let _ ← Seccomp.branch .releaseOrigHasFprog true
    return .error e
  | .ok () =>
    let _ ← Seccomp.branch .prepCheckClassicErr false
  let mut fp := insns
  if ← Seccomp.branch .prepHasTrans true then
    match ← seccompCheckFilter fp with
    | .error e =>
      let _ ← Seccomp.branch .prepTransErr true
      let _ ← Seccomp.branch .releaseSocketFilter false
      let _ ← Seccomp.branch .releaseOrigHasFprog true
      return .error e
    | .ok rewritten =>
      let _ ← Seccomp.branch .prepTransErr false
      fp := rewritten
  -- bpf_jit_compile: the weak no-op; jited stays 0
  if ← Seccomp.branch .prepNotJited true then migrate fp orig
  else Seccomp.invariant "bpf_prepare_filter: a jited classic filter; there is no classic JIT on x86-64"

theorem prepare_source {m : Type → Type} [SeccompM m] (insns orig : Seccomp.ClassicProg) :
    (bpfPrepareFilter insns orig : m _) =
      prepareWith bpfMigrateFilter insns orig := rfl

def createWith {m : Type → Type} [SeccompM m]
    (prepare : Seccomp.ClassicProg → Seccomp.ClassicProg → m (Except Int Seccomp.BpfProg)) (fprog : Seccomp.SockFprog) : m (Except Int Seccomp.BpfProg) := do
  if ← Seccomp.branch .createBasicsNotOk (!(← bpfCheckBasicsOk fprog.filter fprog.len)) then return .error errEINVAL
  if ← Seccomp.branch .createProgAllocNoMem (!(← bpfProgAlloc)) then return .error errENOMEM
  if ← Seccomp.branch .createCopyFault fprog.insnsFault then return .error errEFAULT
  let insns := fprog.filter.get!
  if insns.size != fprog.len then
    Seccomp.invariant s!"bpf_prog_create_from_user: {insns.size} instructions supplied for len {fprog.len}"
  if ← Seccomp.branch .createSaveOrig true then
    match ← bpfProgStoreOrigFilter with
    | .error _ =>
      let _ ← Seccomp.branch .createStoreOrigErr true
      return .error errENOMEM
    | .ok () =>
      let _ ← Seccomp.branch .createStoreOrigErr false
  match ← prepare insns insns with
  | .error e =>
    let _ ← Seccomp.branch .createPrepareErr true
    return .error e
  | .ok p =>
    let _ ← Seccomp.branch .createPrepareErr false
    return .ok p

theorem create_source {m : Type → Type} [SeccompM m] (fprog : Seccomp.SockFprog) :
    (bpfProgCreateFromUser fprog : m _) =
      createWith bpfPrepareFilter fprog := rfl

end Leanux.Proofs.WG.Progress.SeccompProgram
