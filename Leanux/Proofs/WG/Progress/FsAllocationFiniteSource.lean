import Leanux.Proofs.WG.Progress.AllocationProgressSource
import Leanux.FS.File

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Allocation calls retain their native order and all refusal/error paths;
only the hidden allocation evaluator changes. -/

def allocEmptyFile (flags : UInt32) : FS.M (Except Int FileId) := do
  let k ← get
  if ← branch .allocEmptyFileOverMax (k.nrFiles >= k.maxFiles) then
    _ ← branch .allocEmptyFileNotCapable false  -- the harness runs as root: capable(CAP_SYS_ADMIN)
    unsupported "files_stat.max_files reached (percpu recount)"
  if ← branch .allocEmptyFileNoMem (!(← (monadLift (hiddenAllocFinite .filpAlloc)))) then
    return .error (-ENOMEM)
  let fid := k.nextFile
  setFile fid { fFlags := flags, fMode := openFmode flags, fCount := 1 }
  modify fun k => { k with nextFile := fid + 1, nrFiles := k.nrFiles + 1 }
  return .ok fid

theorem allocEmptyFile_source (flags : UInt32) :
    Leanux.allocEmptyFile flags = allocEmptyFile flags := by
  unfold Leanux.allocEmptyFile allocEmptyFile
  simp only [hiddenAlloc, hiddenAlloc_finite_source]

def allocPathPseudo (inode : InodeId) : FS.M Int := do
  if ← branch .allocPathPseudoFail (!(← (monadLift (hiddenAllocFinite .dAllocPseudo)))) then return -ENOMEM
  if let .pipefs id := inode then
    let ino ← getInode id
    if ino.dCount != 0 then invariant s!"d_alloc_pseudo for pipefs inode {id}, whose dentry exists"
    setInode id { ino with dCount := 1 }
  return 0

theorem allocPathPseudo_source (inode : InodeId) :
    Leanux.allocPathPseudo inode = allocPathPseudo inode := by
  unfold Leanux.allocPathPseudo allocPathPseudo
  simp only [hiddenAlloc, hiddenAlloc_finite_source]
  rfl

def allocFdtable (slotsWanted : Nat) : FS.M (Except Int Fdtable) := do
  let mut nr := roundupPowOfTwo slotsWanted
  if ← branchCmp .allocFdtableOverNrOpen (nr > SYSCTL_NR_OPEN) nr SYSCTL_NR_OPEN then
    nr := SYSCTL_NR_OPEN / BITS_PER_LONG * BITS_PER_LONG  -- round_down(sysctl_nr_open, BITS_PER_LONG)
    if ← branchCmp .allocFdtableBelowWanted (nr < slotsWanted) nr slotsWanted then return .error (-EMFILE)
  if ← branchCmp .allocFdtableOverIntMax (nr > 2147483647 / 8) nr (2147483647 / 8) then return .error (-EMFILE)
  if ← branch .allocFdtableNoMem (!(← (monadLift (hiddenAllocFinite .kmallocFdtable)))) then return .error (-ENOMEM)
  -- `kvmalloc_array(nr, sizeof(struct file *))`: above PAGE_SIZE its one slab
  -- attempt carries __GFP_NORETRY (mm/util.c:620-624) and may fail, after
  -- which vmalloc succeeds; a fail record there never means -ENOMEM
  -- (docs/2026-10-05-a-alloc.md 6.2, M7), and the fallback is not modeled
  let arrayOk ← (monadLift (hiddenAllocFinite .kvmallocFdArray))
  if !arrayOk && nr * 8 > PAGE_SIZE then unsupported "kvmalloc vmalloc fallback"
  if ← branch .allocFdtableFdArrayNoMem !arrayOk then return .error (-ENOMEM)
  if ← branch .allocFdtableBitmapNoMem (!(← (monadLift (hiddenAllocFinite .kvmallocFdBitmaps)))) then return .error (-ENOMEM)
  return .ok { maxFds := nr, fd := Array.replicate nr none, openFds := Array.replicate nr false,
               closeOnExec := Array.replicate nr false }

theorem allocFdtable_source (slotsWanted : Nat) :
    Leanux.allocFdtable slotsWanted = allocFdtable slotsWanted := by
  unfold Leanux.allocFdtable allocFdtable
  simp only [hiddenAlloc, hiddenAlloc_finite_source]

def allocPipeInfo : FS.M (Option PipeId) := do
  let mut pipeBufs := PIPE_DEF_BUFFERS
  let user ← getCurrentUser
  let maxSize := (← get).pipeMaxSize
  -- pipe = kzalloc(sizeof(struct pipe_inode_info), GFP_KERNEL_ACCOUNT)
  if ← branch .allocPipeInfoNoMem !(← (monadLift (hiddenAllocFinite .kzallocPipeInfo))) then
    return none  -- out_free_uid: free_uid(user)
  -- `pipe_bufs * PAGE_SIZE > max_size && !capable(CAP_SYS_RESOURCE)`
  if ← branchCmp .allocPipeInfoOverMax (PIPE_DEF_BUFFERS * PAGE_SIZE > maxSize) maxSize (PIPE_DEF_BUFFERS * PAGE_SIZE) then
    if ← branch .allocPipeInfoNotCapable false then  -- capable(): root
      pipeBufs := maxSize >>> 12
  let mut userBufs ← accountPipeBuffers 0 pipeBufs
  if ← branch .allocPipeInfoSoft (← tooManyPipeBuffersSoft userBufs) then
    if ← branch .allocPipeInfoSoftUnpriv (← pipeIsUnprivilegedUser) then
      userBufs ← accountPipeBuffers pipeBufs PIPE_MIN_DEF_BUFFERS
      pipeBufs := PIPE_MIN_DEF_BUFFERS
  let revert ← do
    if ← branch .allocPipeInfoHard (← tooManyPipeBuffersHard userBufs) then
      branch .allocPipeInfoHardUnpriv (← pipeIsUnprivilegedUser)
    else pure false
  if !revert then
    -- pipe->bufs = kcalloc(pipe_bufs, sizeof(struct pipe_buffer), GFP_KERNEL_ACCOUNT)
    if ← branch .allocPipeInfoBufs (← (monadLift (hiddenAllocFinite .kcallocPipeBufs))) then
      -- init_waitqueue_head (x2), r_counter = w_counter = 1, max_usage =
      -- ring_size = nr_accounted = pipe_bufs, user, mutex_init
      let pid := (← get).nextPipe
      setPipe pid { maxUsage := pipeBufs, ringSize := pipeBufs, nrAccounted := pipeBufs,
                    rCounter := 1, wCounter := 1, bufs := Array.replicate pipeBufs {}, user }
      modify fun k => { k with nextPipe := pid + 1 }
      return some pid
  -- out_revert_acct:
  _ ← accountPipeBuffers pipeBufs 0
  -- kfree(pipe); out_free_uid: free_uid(user)
  return none

theorem allocPipeInfo_source :
    Leanux.allocPipeInfo = allocPipeInfo := by
  unfold Leanux.allocPipeInfo allocPipeInfo
  simp only [hiddenAlloc, hiddenAlloc_finite_source]

end Leanux.Proofs.WG.Progress.FsFinite
