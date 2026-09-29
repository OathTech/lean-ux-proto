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
def fullWord (fdt : Fdtable) (word : Nat) : Bool :=
  (List.range BITS_PER_LONG).all fun i => fdt.openFds (word * BITS_PER_LONG + i)

def setCloseOnExecBit (fd : Nat) : M Unit :=  -- __set_close_on_exec
  modifyFdt fun t => { t with closeOnExec := fun n => if n = fd then true else t.closeOnExec n }

/-- __clear_close_on_exec (file.c:261-265). -/
def clearCloseOnExecBit (fd : Nat) : M Unit := do
  if ← branch .clearCloexecWasSet ((← getFiles).fdt.closeOnExec fd) then
    modifyFdt fun t => { t with closeOnExec := fun n => if n = fd then false else t.closeOnExec n }

/-- __set_open_fd (file.c:267-273). -/
def setOpenFd (fd : Nat) : M Unit := do
  modifyFdt fun t => { t with openFds := fun n => if n = fd then true else t.openFds n }
  _ ← branch .setOpenFdFullWord (fullWord (← getFiles).fdt (fd / BITS_PER_LONG))
  -- __set_bit(fd, fdt->full_fds_bits) is implied by the derived view

/-- __clear_open_fd (file.c:275-279). -/
def clearOpenFd (fd : Nat) : M Unit :=
  modifyFdt fun t => { t with openFds := fun n => if n = fd then false else t.openFds n }

/-- `find_next_zero_bit(bits, size, start)`: an architecture bit-search cut
    point with contract "least clear bit in [start, size), else size". -/
def findNextZeroBit (bit : Nat → Bool) (size start : Nat) : Nat :=
  ((List.range (size - start)).map (· + start)).find? (fun n => !bit n) |>.getD size

/-- find_next_fd (file.c:475-487). -/
def findNextFd (fdt : Fdtable) (start : Nat) : M Nat := do
  let maxfd := fdt.maxFds
  let maxbit := maxfd / BITS_PER_LONG
  let bitbit := findNextZeroBit (fullWord fdt) maxbit (start / BITS_PER_LONG) * BITS_PER_LONG
  if ← branch .findNextFdAllFull (bitbit >= maxfd) then return maxfd
  let start ← do
    if ← branch .findNextFdSkipFullWords (bitbit > start) then pure bitbit else pure start
  return findNextZeroBit fdt.openFds maxfd start

/-- expand_files (file.c:221-254), with `file_lock` held. Growth beyond the
    embedded 64-slot table (`expand_fdtable`) is outside the domain. -/
def expandFiles (nr : Nat) : M Int := do
  let files ← getFiles
  if ← branch .expandFilesFits (nr < files.fdt.maxFds) then return 0
  if ← branch .expandFilesOverNrOpen (nr >= SYSCTL_NR_OPEN) then return -EMFILE
  if ← branch .expandFilesResizeInProgress files.resizeInProgress then
    unsupported "expand_files waiting for a concurrent resize"
  unsupported "expand_fdtable"

/-- alloc_fd (file.c:492-548). -/
def allocFd (start «end» : Nat) (flags : UInt32) : M Int := do
  -- spin_lock(&files->file_lock); repeat:
  let files ← getFiles
  let fdt := files.fdt
  let mut fd := start
  if ← branch .allocFdBelowNextFd (fd < files.nextFd) then fd := files.nextFd
  if ← branch .allocFdSearch (fd < fdt.maxFds) then fd ← findNextFd fdt fd
  -- error = -EMFILE
  if ← branch .allocFdLimit (fd >= «end») then return -EMFILE  -- goto out
  let error ← expandFiles fd
  if ← branch .allocFdExpandError (error < 0) then return error
  if ← branch .allocFdExpanded (error != 0) then unsupported "alloc_fd retry after expansion"
  if ← branch .allocFdUpdateNextFd (start <= (← getFiles).nextFd) then
    modifyFiles fun fs => { fs with nextFd := fd + 1 }
  setOpenFd fd
  if ← branch .allocFdCloexec (hasFlag flags O_CLOEXEC) then setCloseOnExecBit fd
  else clearCloseOnExecBit fd
  -- Sanity check
  if ← branch .allocFdSlotNotNull ((← getFiles).fdt.fd fd).isSome then
    unsupported "alloc_fd: slot not NULL"
  -- out: spin_unlock(&files->file_lock)
  return fd

/-- get_unused_fd_flags (file.c:555-558): `alloc_fd(0, rlimit(RLIMIT_NOFILE), flags)`. -/
def getUnusedFdFlags (flags : UInt32) : M Int := do
  allocFd 0 (← getK).task.rlimitNofile flags

/-- __put_unused_fd (file.c:561-567). -/
def putUnusedFdLocked (fd : Nat) : M Unit := do
  clearOpenFd fd
  if ← branch .putUnusedFdLowerNextFd (fd < (← getFiles).nextFd) then
    modifyFiles fun fs => { fs with nextFd := fd }

/-- put_unused_fd (file.c:569-575). -/
def putUnusedFd (fd : Nat) : M Unit := do
  -- spin_lock(&files->file_lock)
  putUnusedFdLocked fd
  -- spin_unlock(&files->file_lock)

/-- fd_install (file.c:595-620). Consumes the caller's file reference. -/
def fdInstall (fd : Nat) (fid : FileId) : M Unit := do
  if ← branch .fdInstallBacking (hasFlag (← getFile fid).fMode FMODE_BACKING) then
    unsupported "fd_install of a backing file (WARN_ON_ONCE)"
  -- rcu_read_lock_sched()
  if ← branch .fdInstallResizeInProgress (← getFiles).resizeInProgress then
    unsupported "fd_install during resize"
  -- smp_rmb(); fdt = rcu_dereference_sched(files->fdt)
  if ← branch .fdInstallSlotBusy ((← getFiles).fdt.fd fd).isSome then
    unsupported "fd_install: BUG_ON(fdt->fd[fd] != NULL)"
  modifyFdt fun t => { t with fd := fun n => if n = fd then some fid else t.fd n }
  -- rcu_read_unlock_sched()

/-- file_close_fd_locked (file.c:635-652), with `file_lock` held. -/
def fileCloseFdLocked (fd : Nat) : M (Option FileId) := do
  let fdt := (← getFiles).fdt
  if ← branch .closeFdOutOfRange (fd >= fdt.maxFds) then return none
  -- fd = array_index_nospec(fd, fdt->max_fds): the identity for in-range fd
  let file := fdt.fd fd
  if ← branch .closeFdFound file.isSome then
    modifyFdt fun t => { t with fd := fun n => if n = fd then none else t.fd n }
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
  let needsMasking := fdt.fd (if inRange then fd else 0)
  return if inRange then needsMasking else none

/-- get_file (include/linux/fs.h:1122-1127). -/
def getFileRef (fid : FileId) : M Unit := do
  let f ← getFile fid
  setFile fid { f with fCount := f.fCount + 1 }  -- prior = atomic_long_fetch_inc_relaxed(&f->f_count)
  if ← branch .getFileFromZero (f.fCount == 0) then
    unsupported "get_file: f_count incremented from zero (WARN_ONCE)"

/-- do_dup2 (file.c:1205-1248), entered with `file_lock` held. -/
def doDup2 (fid : FileId) (fd : Nat) (flags : UInt32) : M Int := do
  let fdt := (← getFiles).fdt
  -- fd = array_index_nospec(fd, fdt->max_fds)
  let tofree := fdt.fd fd
  -- `if (!tofree && fd_is_open(fd, fdt)) goto Ebusy;`
  if ← branch .doDup2NoTofree tofree.isNone then
    if ← branch .doDup2FdOpen (fdt.openFds fd) then
      return -EBUSY  -- Ebusy: spin_unlock
  getFileRef fid
  modifyFdt fun t => { t with fd := fun n => if n = fd then some fid else t.fd n }
  setOpenFd fd
  if ← branch .doDup2Cloexec (hasFlag flags O_CLOEXEC) then setCloseOnExecBit fd
  else clearCloseOnExecBit fd
  -- spin_unlock(&files->file_lock)
  if ← branch .doDup2Replace tofree.isSome then
    if let some old := tofree then _ ← filpClose old
  return fd

/-- ksys_dup3 (file.c:1331-1363). -/
def ksysDup3 (oldfd newfd : Nat) (flags : UInt32) : M Int := do
  if ← branch .dup3InvalidFlags (flags &&& ~~~O_CLOEXEC != 0) then return -EINVAL
  if ← branch .dup3Equal (oldfd == newfd) then return -EINVAL
  if ← branch .dup3TargetLimit (newfd >= (← getK).task.rlimitNofile) then return -EBADF
  -- spin_lock(&files->file_lock)
  let err ← expandFiles newfd
  let file ← filesLookupFdRaw oldfd   -- files_lookup_fd_locked
  if ← branch .dup3NoFile file.isNone then return -EBADF  -- Ebadf: spin_unlock
  if ← branch .dup3ExpandError (err < 0) then
    if ← branch .dup3ExpandEmfile (err == -EMFILE) then return -EBADF
    return err  -- out_unlock
  match file with
  | some fid => doDup2 fid newfd flags
  | none => unsupported "unreachable: file checked non-NULL"

/-- __fget_files_rcu (file.c:930-1004) under rcu_read_lock. The retry arms
    (`inc_not_zero` failing, the table or slot changing) need concurrency. -/
def fgetFilesRcu (fd : Nat) (mask : UInt32) : M (Option FileId) := do
  let generation := (← getFiles).fdtGeneration  -- fdt = rcu_dereference_raw(files->fdt)
  let file ← filesLookupFdRaw fd
  if ← branch .fgetRcuNoFile file.isNone then return none
  let some fid := file | unsupported "unreachable"
  let f ← getFile fid
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
  if ← branch .fgetLightSingleOwner ((← getFiles).count == 1) then
    let file ← filesLookupFdRaw fd
    let empty ← do
      if ← branch .fgetLightNoFile file.isNone then pure true
      else
        let some fid := file | unsupported "unreachable"
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
    let some fid := f.file | unsupported "unreachable"
    let file ← getFile fid
    let needsLock ← do
      if ← branch .fposLockAtomicPos (hasFlag file.fMode FMODE_ATOMIC_POS) then
        if ← branch .fposLockShared (file.fCount > 1) then pure true
        else branch .fposLockIterateShared (← fopsOf file.kind).iterateShared
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
def getCloseOnExec (fd : Nat) : M Bool :=
  return (← getFiles).fdt.closeOnExec fd

/-- fget_raw (file.c:1029-1032): `__fget(fd, 0)`. -/
def fgetRaw (fd : Nat) : M (Option FileId) := fgetFilesRcu fd 0

/-- SYSCALL_DEFINE1(dup) (file.c:1389-1402). -/
def sysDup (fildes : Nat) : M Int := do
  let file ← fgetRaw fildes
  let mut ret := -EBADF
  if ← branch .dupFound file.isSome then
    let some fid := file | unsupported "unreachable"
    ret ← getUnusedFdFlags 0
    if ← branch .dupAllocOk (ret >= 0) then fdInstall ret.toNat fid
    else fput fid
  return ret

end Leanux
