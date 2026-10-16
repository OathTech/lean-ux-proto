import Leanux.FS.Open

/-!
# fs/file.c — the descriptor table

Bitmap helpers, `find_next_fd`, `expand_files`, `alloc_fd`, `fd_install`,
`__put_unused_fd`, `file_close_fd_locked`, `files_lookup_fd_raw`, `do_dup2`,
`ksys_dup3`, `__fget_files_rcu`, `__fget_light`/`fdget`/`fdget_pos`,
`set_close_on_exec`/`get_close_on_exec`, and the `dup` syscall.

`files->file_lock` is taken and released at the C's positions (comments).
The domain is single-threaded, so each lock-held region is one atomic mirror
step; RCU dereferences and `rcu_assign_pointer` are plain reads and writes.
-/

namespace Leanux

/-! ## Bitmap helpers (fs/file.c:256-284) -/

/-- `!~fdt->open_fds[word]`: every descriptor in the 64-bit word is open. This
    is the only fact `full_fds_bits` records, so it is derived, not stored. -/
def fullWord (fdt : Fdtable) (word : Nat) : M Bool :=
  (List.range BITS_PER_LONG).allM fun i => fdtOpen fdt (word * BITS_PER_LONG + i)

def setCloseOnExecBit (fd : Nat) : M Unit := setFdtCloexec fd true  -- __set_close_on_exec

/-- __clear_close_on_exec (file.c:261-265). -/
def clearCloseOnExecBit (fd : Nat) : M Unit := do
  if ← branch .clearCloexecWasSet (← fdtCloexec (← getFiles).fdt fd) then
    setFdtCloexec fd false

/-- __set_open_fd (file.c:267-273). -/
def setOpenFd (fd : Nat) : M Unit := do
  setFdtOpen fd true
  _ ← branch .setOpenFdFullWord (← fullWord (← getFiles).fdt (fd / BITS_PER_LONG))
  -- __set_bit(fd, fdt->full_fds_bits) is implied by the derived view

/-- __clear_open_fd (file.c:275-279). -/
def clearOpenFd (fd : Nat) : M Unit := setFdtOpen fd false

/-- `find_next_zero_bit(bits, size, start)`: an architecture bit-search cut
    point with contract "least clear bit in [start, size), else size". -/
def findNextZeroBit (bit : Nat → M Bool) (size start : Nat) : M Nat := do
  for n in List.range (size - start) do
    if !(← bit (n + start)) then return n + start
  return size

/-- find_next_fd (file.c:475-487). -/
def findNextFd (fdt : Fdtable) (start : Nat) : M Nat := do
  let maxfd := fdt.maxFds
  let maxbit := maxfd / BITS_PER_LONG
  let bitbit := (← findNextZeroBit (fullWord fdt) maxbit (start / BITS_PER_LONG)) * BITS_PER_LONG
  if ← branchCmp .findNextFdAllFull (bitbit >= maxfd) bitbit maxfd then return maxfd
  let start ← do
    if ← branch .findNextFdSkipFullWords (bitbit > start) then pure bitbit else pure start
  findNextZeroBit (fdtOpen fdt) maxfd start

/-- `roundup_pow_of_two(n)` (include/linux/log2.h): a pure helper. -/
def roundupPowOfTwo (n : Nat) : Nat :=
  if n ≤ 1 then 1 else 2 ^ (Nat.log2 (n - 1) + 1)

/-- alloc_fdtable (file.c:94-175). `CONFIG_32BIT=n`, so `nr` is the smallest
    power of two at least `slots_wanted`. The three allocations consult the
    environment oracle; `kvmalloc` leaves the arrays uninitialized, and
    `copy_fdtable` then writes every slot and bit, so they start empty here. -/
def allocFdtable (slotsWanted : Nat) : M (Except Int Fdtable) := do
  let mut nr := roundupPowOfTwo slotsWanted
  if ← branchCmp .allocFdtableOverNrOpen (nr > SYSCTL_NR_OPEN) nr SYSCTL_NR_OPEN then
    nr := SYSCTL_NR_OPEN / BITS_PER_LONG * BITS_PER_LONG  -- round_down(sysctl_nr_open, BITS_PER_LONG)
    if ← branchCmp .allocFdtableBelowWanted (nr < slotsWanted) nr slotsWanted then return .error (-EMFILE)
  if ← branchCmp .allocFdtableOverIntMax (nr > 2147483647 / 8) nr (2147483647 / 8) then return .error (-EMFILE)
  if ← branch .allocFdtableNoMem (!(← hiddenAlloc .kmallocFdtable)) then return .error (-ENOMEM)
  -- `kvmalloc_array(nr, sizeof(struct file *))`: above PAGE_SIZE its one slab
  -- attempt carries __GFP_NORETRY (mm/util.c:620-624) and may fail, after
  -- which vmalloc succeeds; a fail record there never means -ENOMEM
  -- (docs/2026-10-05-a-alloc.md 6.2, M7), and the fallback is not modeled
  let arrayOk ← hiddenAlloc .kvmallocFdArray
  if !arrayOk && nr * 8 > PAGE_SIZE then unsupported "kvmalloc vmalloc fallback"
  if ← branch .allocFdtableFdArrayNoMem !arrayOk then return .error (-ENOMEM)
  if ← branch .allocFdtableBitmapNoMem (!(← hiddenAlloc .kvmallocFdBitmaps)) then return .error (-ENOMEM)
  return .ok { maxFds := nr, fd := Array.replicate nr none, openFds := Array.replicate nr false,
               closeOnExec := Array.replicate nr false }

/-- copy_fdtable (file.c:73-85) with copy_fd_bitmaps (56-67): copy the old
    slots and bits, clear the rest. `bitmap_copy_and_extend`
    (include/linux/bitmap.h) is a cut point with a pure contract; its internal
    `count % BITS_PER_LONG` branch is not mirrored. `full_fds_bits` is derived. -/
def copyFdtable (nfdt ofdt : Fdtable) : M Fdtable := do
  if ← branchCmp .copyFdtableShrink (nfdt.maxFds < ofdt.maxFds) nfdt.maxFds ofdt.maxFds then
    unsupported "copy_fdtable: BUG_ON(nfdt->max_fds < ofdt->max_fds)"
  let extra := nfdt.maxFds - ofdt.maxFds
  return { nfdt with fd := ofdt.fd ++ Array.replicate extra none,
                     openFds := ofdt.openFds ++ Array.replicate extra false,
                     closeOnExec := ofdt.closeOnExec ++ Array.replicate extra false }

/-- expand_fdtable (file.c:184-211): drops `file_lock` to allocate, then
    publishes the new table with `rcu_assign_pointer`. The old table, unless
    it is the embedded `files->fdtab`, is freed after a grace period
    (`call_rcu`, a cut point; it is unreachable in the mirror). -/
def expandFdtable (nr : Nat) : M Int := do
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

/-- expand_files (file.c:221-254), with `file_lock` held. -/
def expandFiles (nr : Nat) : M Int := do
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

/-- alloc_fd (file.c:492-548). A successful expansion returns 1 and jumps
    back to `repeat:`, so the loop's decisions are evaluated again; they are
    declared repeatable. One expansion always covers the requested slot, so a
    second retry would be a mirror defect. -/
def allocFd (start «end» : Nat) (flags : UInt32) : M Int := do
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

/-- get_unused_fd_flags (file.c:555-558): `alloc_fd(0, rlimit(RLIMIT_NOFILE), flags)`. -/
def getUnusedFdFlags (flags : UInt32) : M Int := do
  allocFd 0 (← getTask .task).rlimitNofile flags

/-- __put_unused_fd (file.c:561-567). -/
def putUnusedFdLocked (fd : Nat) : M Unit := do
  clearOpenFd fd
  if ← branchCmp .putUnusedFdLowerNextFd (fd < (← getFiles).nextFd) fd (← getFiles).nextFd then
    modifyFiles fun fs => { fs with nextFd := fd }

/-- put_unused_fd (file.c:569-575). -/
def putUnusedFd (fd : Nat) : M Unit := do
  -- spin_lock(&files->file_lock)
  putUnusedFdLocked fd
  -- spin_unlock(&files->file_lock)

/-- fd_install (file.c:595-620). Consumes the caller's file reference. -/
def fdInstall (fd : Nat) (fid : FileId) : M Unit := do
  if ← branchCmp .fdInstallBacking (hasFlag (← getFile fid).fMode FMODE_BACKING) ((← getFile fid).fMode &&& FMODE_BACKING).toNat 0 then
    unsupported "fd_install of a backing file (WARN_ON_ONCE)"
  -- rcu_read_lock_sched()
  if ← branch .fdInstallResizeInProgress (← getFiles).resizeInProgress then
    unsupported "fd_install during resize"
  -- smp_rmb(); fdt = rcu_dereference_sched(files->fdt)
  if ← branch .fdInstallSlotBusy (← fdtSlot (← getFiles).fdt fd).isSome then
    unsupported "fd_install: BUG_ON(fdt->fd[fd] != NULL)"
  setFdtSlot fd (some fid)  -- rcu_assign_pointer(fdt->fd[fd], file)
  -- rcu_read_unlock_sched()

/-- file_close_fd_locked (file.c:635-652), with `file_lock` held. -/
def fileCloseFdLocked (fd : Nat) : M (Option FileId) := do
  let fdt := (← getFiles).fdt
  if ← branchCmp .closeFdOutOfRange (fd >= fdt.maxFds) fd fdt.maxFds then return none
  -- fd = array_index_nospec(fd, fdt->max_fds): the identity for in-range fd
  let file ← fdtSlot fdt fd
  if ← branch .closeFdFound file.isSome then
    setFdtSlot fd none  -- rcu_assign_pointer(fdt->fd[fd], NULL)
    putUnusedFdLocked fd
  return file

/-- file_close_fd (file.c:791-801). -/
def fileCloseFd (fd : Nat) : M (Option FileId) := do
  -- spin_lock(&files->file_lock)
  let file ← fileCloseFdLocked fd
  -- spin_unlock(&files->file_lock)
  return file

/-- files_lookup_fd_raw (include/linux/fdtable.h:72-88). Branch-free: the
    speculation mask selects slot `fd` in range and NULL out of range. -/
def filesLookupFdRaw (fd : Nat) : M (Option FileId) := do
  let fdt := (← getFiles).fdt
  let inRange := fd < fdt.maxFds
  let needsMasking ← fdtSlot fdt (if inRange then fd else 0)
  return if inRange then needsMasking else none

/-- get_file (include/linux/fs.h:1122-1127). -/
def getFileRef (fid : FileId) : M Unit := do
  let f ← getFile fid
  setFile fid { f with fCount := f.fCount + 1 }  -- prior = atomic_long_fetch_inc_relaxed(&f->f_count)
  if ← branchCmp .getFileFromZero (f.fCount == 0) f.fCount 0 then
    unsupported "get_file: f_count incremented from zero (WARN_ONCE)"

/-- do_dup2 (file.c:1205-1248), entered with `file_lock` held. -/
def doDup2 (fid : FileId) (fd : Nat) (flags : UInt32) : M Int := do
  let fdt := (← getFiles).fdt
  -- fd = array_index_nospec(fd, fdt->max_fds)
  let tofree ← fdtSlot fdt fd
  -- `if (!tofree && fd_is_open(fd, fdt)) goto Ebusy;`
  if ← branch .doDup2NoTofree tofree.isNone then
    if ← branch .doDup2FdOpen (← fdtOpen fdt fd) then
      return -EBUSY  -- Ebusy: spin_unlock
  getFileRef fid
  setFdtSlot fd (some fid)  -- rcu_assign_pointer(fdt->fd[fd], file)
  setOpenFd fd
  if ← branchCmp .doDup2Cloexec (hasFlag flags O_CLOEXEC) (flags &&& O_CLOEXEC).toNat 0 then setCloseOnExecBit fd
  else clearCloseOnExecBit fd
  -- spin_unlock(&files->file_lock)
  if ← branch .doDup2Replace tofree.isSome then
    if let some old := tofree then _ ← filpClose old
  return fd

/-- ksys_dup3 (file.c:1331-1363). -/
def ksysDup3 (oldfd newfd : Nat) (flags : UInt32) : M Int := do
  if ← branchCmp .dup3InvalidFlags (flags &&& ~~~O_CLOEXEC != 0) (flags &&& ~~~O_CLOEXEC).toNat 0 then return -EINVAL
  if ← branchCmp .dup3Equal (oldfd == newfd) oldfd newfd then return -EINVAL
  if ← branchCmp .dup3TargetLimit (newfd >= (← getTask .task).rlimitNofile) newfd (← getTask .task).rlimitNofile then return -EBADF
  -- spin_lock(&files->file_lock)
  let err ← expandFiles newfd
  let file ← filesLookupFdRaw oldfd   -- files_lookup_fd_locked
  if ← branch .dup3NoFile file.isNone then return -EBADF  -- Ebadf: spin_unlock
  if ← branchCmp .dup3ExpandError (err < 0) err 0 then
    if ← branch .dup3ExpandEmfile (err == -EMFILE) then return -EBADF
    return err  -- out_unlock
  match file with
  | some fid => doDup2 fid newfd flags
  | none => invariant "unreachable: file checked non-NULL"

/-- __fget_files_rcu (file.c:930-1004) under rcu_read_lock. The retry arms
    (`inc_not_zero` failing, the table or slot changing) need concurrency. -/
def fgetFilesRcu (fd : Nat) (mask : UInt32) : M (Option FileId) := do
  let generation := (← getFiles).fdtGeneration  -- fdt = rcu_dereference_raw(files->fdt)
  let file ← filesLookupFdRaw fd
  if ← branch .fgetRcuNoFile file.isNone then return none
  let some fid := file | invariant "unreachable"
  let f ← getFile fid
  -- the condition tests atomic_long_inc_not_zero's result (a cut point), not a comparison
  if ← branch .fgetRcuIncNotZeroFailed (f.fCount == 0) then
    unsupported "__fget_files_rcu retry"
  setFile fid { f with fCount := f.fCount + 1 }
  -- `file != rcu_dereference_raw(*fdentry) || rcu_dereference_raw(files->fdt) != fdt`
  let stale ← do
    if ← branch .fgetRcuEntryChanged ((← filesLookupFdRaw fd) != some fid) then pure true
    else branch .fgetRcuTableChanged ((← getFiles).fdtGeneration != generation)
  if stale then unsupported "__fget_files_rcu retry after a stale entry"
  if ← branch .fgetRcuMasked (hasFlag f.fMode mask) then
    fput fid
    return none
  return some fid

/-- A `struct fd`: the file and whether `fdput` must drop a reference
    (`FDPUT_FPUT`) or unlock `f_pos` (`FDPUT_POS_UNLOCK`). -/
structure Fd where
  file : Option FileId
  fput : Bool := false
  posUnlock : Bool := false

/-- __fget_light (file.c:1107-1132). -/
def fgetLight (fd : Nat) (mask : UInt32) : M Fd := do
  if ← branchCmp .fgetLightSingleOwner ((← getFiles).count == 1) (← getFiles).count 1 then
    let file ← filesLookupFdRaw fd
    let empty ← do
      if ← branch .fgetLightNoFile file.isNone then pure true
      else
        let some fid := file | invariant "unreachable"
        -- the comparison depends on each caller's constant mask (fdget_raw's 0 folds away)
        branch .fgetLightMasked (hasFlag (← getFile fid).fMode mask)
    if empty then return {file := none}  -- EMPTY_FD
    return {file}                        -- BORROWED_FD
  unsupported "__fget_light with a shared files_struct"

def fdget (fd : Nat) : M Fd := fgetLight fd FMODE_PATH       -- file.c:1133-1136
def fdgetRaw (fd : Nat) : M Fd := fgetLight fd 0             -- file.c:1139-1142

/-- fdget_pos (file.c:1160-1170) with file_needs_f_pos_lock (1154-1158). -/
def fdgetPos (fd : Nat) : M Fd := do
  let f ← fdget fd
  if ← branch .fdgetPosHasFile f.file.isSome then
    let some fid := f.file | invariant "unreachable"
    let file ← getFile fid
    let needsLock ← do
      if ← branchCmp .fposLockAtomicPos (hasFlag file.fMode FMODE_ATOMIC_POS) (file.fMode &&& FMODE_ATOMIC_POS).toNat 0 then
        if ← branch .fposLockShared (file.fCount > 1) then pure true
        else branch .fposLockIterateShared (← fopsOf file.fOp).iterateShared
      else pure false
    if needsLock then
      return { f with posUnlock := true }  -- mutex_lock(&file->f_pos_lock)
  return f

/-- fdput (include/linux/file.h:60-64). -/
def fdput (f : Fd) : M Unit := do
  if ← branch .fdputFput f.fput then
    if let some fid := f.file then fput fid

/-- fdput_pos (include/linux/file.h:75-80). -/
def fdputPos (f : Fd) : M Unit := do
  if ← branch .fdputPosUnlock f.posUnlock then
    pure ()  -- __f_unlock_pos: mutex_unlock(&f->f_pos_lock)
  fdput f

/-- set_close_on_exec (file.c:1183-1194). -/
def setCloseOnExec (fd : Nat) (flag : Bool) : M Unit := do
  -- spin_lock(&files->file_lock)
  if ← branch .setCloexecFlag flag then setCloseOnExecBit fd
  else clearCloseOnExecBit fd
  -- spin_unlock(&files->file_lock)

/-- get_close_on_exec (file.c:1196-1203): `test_bit`, no branch. -/
def getCloseOnExec (fd : Nat) : M Bool := do
  fdtCloexec (← getFiles).fdt fd

/-- fget_raw (file.c:1029-1032): `__fget(fd, 0)`. -/
def fgetRaw (fd : Nat) : M (Option FileId) := fgetFilesRcu fd 0

/-- SYSCALL_DEFINE1(dup) (file.c:1389-1402). -/
def sysDup (fildes : Nat) : M Int := do
  let file ← fgetRaw fildes
  let mut ret := -EBADF
  if ← branch .dupFound file.isSome then
    let some fid := file | invariant "unreachable"
    ret ← getUnusedFdFlags 0
    if ← branchCmp .dupAllocOk (ret >= 0) ret 0 then fdInstall ret.toNat fid
    else fput fid
  return ret

end Leanux
