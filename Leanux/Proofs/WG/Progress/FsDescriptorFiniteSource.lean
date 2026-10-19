import Leanux.Proofs.WG.Progress.FsAllocationFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Exact finite descriptor-allocation callers. The original two-turn retry
and its exhaustion invariant are retained; no success premise is supplied. -/

def expandFdtable (nr : Nat) : FS.M Int := do
  -- spin_unlock(&files->file_lock)
  let newFdt ← allocFdtable (nr + 1)
  if ← branchCmp .expandFdtableShared ((← getFiles).count > 1) (← getFiles).count 1 then
    unsupported "synchronize_rcu for a shared files_struct"
  -- spin_lock(&files->file_lock)
  let nfdt ← match newFdt with
    | .error e => do
      _ ← branch .expandFdtableAllocError true
      return e
    | .ok t => do
      _ ← branch .expandFdtableAllocError false
      pure t
  let cur := (← getFiles).fdt
  if ← branchCmp .expandFdtableBugNr (nr < cur.maxFds) nr cur.maxFds then
    unsupported "expand_fdtable: BUG_ON(nr < cur_fdt->max_fds)"
  let copied ← copyFdtable nfdt cur
  let embedded := (← getFiles).fdtGeneration == 0  -- cur_fdt == &files->fdtab
  modifyFiles fun fs => { fs with fdt := copied, fdtGeneration := fs.fdtGeneration + 1 }
  _ ← branch .expandFdtableFreeOld !embedded       -- call_rcu(&cur_fdt->rcu, free_fdtable_rcu)
  -- smp_wmb(): coupled with smp_rmb() in fd_install()
  return 1

theorem expandFdtable_source (nr : Nat) :
    Leanux.expandFdtable nr = expandFdtable nr := by
  unfold Leanux.expandFdtable expandFdtable
  simp only [allocFdtable_source]
  rfl

def expandFiles (nr : Nat) : FS.M Int := do
  let files ← getFiles
  if ← branchCmp .expandFilesFits (nr < files.fdt.maxFds) nr files.fdt.maxFds then return 0
  if ← branchCmp .expandFilesOverNrOpen (nr >= SYSCTL_NR_OPEN) nr SYSCTL_NR_OPEN then return -EMFILE
  if ← branch .expandFilesResizeInProgress files.resizeInProgress then
    unsupported "expand_files waiting for a concurrent resize"
  modifyFiles fun fs => { fs with resizeInProgress := true }
  let expanded ← expandFdtable nr
  modifyFiles fun fs => { fs with resizeInProgress := false }
  -- wake_up_all(&files->resize_wait): a cut point (no waiters)
  return expanded

theorem expandFiles_source (nr : Nat) :
    Leanux.expandFiles nr = expandFiles nr := by
  unfold Leanux.expandFiles expandFiles
  simp only [expandFdtable_source]

def allocFd (start «end» : Nat) (flags : UInt32) : FS.M Int := do
  -- spin_lock(&files->file_lock)
  for _ in [0:2] do
    -- repeat:
    let files ← getFiles
    let fdt := files.fdt
    let mut fd := start
    if ← branch .allocFdBelowNextFd (fd < files.nextFd) then fd := files.nextFd
    if ← branchCmp .allocFdSearch (fd < fdt.maxFds) fd fdt.maxFds then fd ← findNextFd fdt fd
    -- error = -EMFILE
    if ← branchCmp .allocFdLimit (fd >= «end») fd «end» then return -EMFILE  -- goto out
    let error ← expandFiles fd
    if ← branchCmp .allocFdExpandError (error < 0) error 0 then return error
    if ← branchCmp .allocFdExpanded (error != 0) error 0 then continue  -- goto repeat
    if ← branchCmp .allocFdUpdateNextFd (start <= (← getFiles).nextFd) start (← getFiles).nextFd then
      modifyFiles fun fs => { fs with nextFd := fd + 1 }
    setOpenFd fd
    if ← branchCmp .allocFdCloexec (hasFlag flags O_CLOEXEC) (flags &&& O_CLOEXEC).toNat 0 then setCloseOnExecBit fd
    else clearCloseOnExecBit fd
    -- Sanity check
    if ← branch .allocFdSlotNotNull (← fdtSlot (← getFiles).fdt fd).isSome then
      unsupported "alloc_fd: slot not NULL"
    -- out: spin_unlock(&files->file_lock)
    return fd
  invariant "alloc_fd: a second retry after expansion"

theorem allocFd_source (start «end» : Nat) (flags : UInt32) :
    Leanux.allocFd start «end» flags = allocFd start «end» flags := by
  unfold Leanux.allocFd allocFd
  simp only [expandFiles_source]

def getUnusedFdFlags (flags : UInt32) : FS.M Int := do
  allocFd 0 (← getTask .task).rlimitNofile flags

theorem getUnusedFdFlags_source (flags : UInt32) :
    Leanux.getUnusedFdFlags flags = getUnusedFdFlags flags := by
  unfold Leanux.getUnusedFdFlags getUnusedFdFlags
  simp only [allocFd_source]


end Leanux.Proofs.WG.Progress.FsFinite
