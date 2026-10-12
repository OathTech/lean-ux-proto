import Leanux.Kernel.Defs

/-!
# fs/inode.c, fs/libfs.c, include/linux/time64.h — pipefs inode timestamps

The pipefs inode's life (docs/2026-10-05-p-pipes.md sections 3 and 5): the
inode-allocation cut (`new_inode_pseudo`), the creation stamp
(`simple_inode_init_ts`), the access stamp on a read (`file_accessed` →
`touch_atime`), the modification stamps on a write (`file_update_time`), and
the last `iput` through the pseudo dentry's `dput`.

**The clock.** Every `current_time` consumes one `.currentTime` record
(`ktime_get_coarse_real_ts64`, consumer frame fs/inode.c:2648), in C order:
one per `pipe2`, one or two per successful read (none with `O_NOATIME`), one
or two per successful write. The stamps flow into `timespec64_equal`, whose
two comparisons (time64.h:49) report their operands (A3).

**pipefs facts**, each derived from source and stated where it decides:
- `s_time_gran = 1` (fs/libfs.c:657, `pseudo_fs_fill_super`), `s_time_min =
  TIME64_MIN`, `s_time_max = TIME64_MAX` (fs/super.c:375-376);
- `s_flags = SB_KERNMOUNT | SB_NOUSER | SB_BORN | SB_ACTIVE` (0xe0400000:
  `kern_mount`, fs/libfs.c:706, and the mount's bring-up; bit values
  include/linux/fs.h:1216-1240), so `SB_RDONLY`, `SB_NOATIME`,
  `SB_NODIRATIME`, `SB_I_VERSION` and `SB_LAZYTIME` are clear;
- `pipe_mnt->mnt_flags = MNT_INTERNAL` (fs/namespace.c:1220), so
  `MNT_NOATIME`, `MNT_NODIRATIME` and `MNT_RELATIME` are clear;
- `i_op = &empty_iops` (fs/inode.c:170): no `update_time`;
- `pipefs_ops` has no `dirty_inode`, `drop_inode` or `evict_inode`, and
  `destroy_inode = free_inode_nonrcu` (fs/pipe.c:1424-1427).

**Cuts**, each with its contract: inode allocation (`.allocInode`, below);
`sb_start_write_trylock`/`sb_end_write` (succeed: no freeze);
`mnt_get_write_access`/`mnt_get_write_access_file` (0: `pipe_mnt` is not
read-only) and their puts; `__mark_inode_dirty` (below); `HAS_UNMAPPED_ID`'s
idmapping (`nop_mnt_idmap`; the creator is root, so `i_uid`/`i_gid` are 0
and valid); the dentry apart from its count (`dputPipefs`); `iput`'s
internals (`iputPipefs`).
-/

namespace Leanux

/-! ## pipefs superblock and mount facts -/

def TIME64_MAX : Int := 2 ^ 63 - 1
def TIME64_MIN : Int := -(2 ^ 63)
def NSEC_PER_SEC : Nat := 1000000000

/-- `sb->s_time_gran` of pipefs (fs/libfs.c:657). -/
def pipefsTimeGran : Nat := 1
def pipefsTimeMin : Int := TIME64_MIN
def pipefsTimeMax : Int := TIME64_MAX

def SB_RDONLY : Nat := 1 <<< 0
def SB_NOATIME : Nat := 1 <<< 10
def SB_NODIRATIME : Nat := 1 <<< 11
def SB_KERNMOUNT : Nat := 1 <<< 22
def SB_I_VERSION : Nat := 1 <<< 23
def SB_LAZYTIME : Nat := 1 <<< 25
def SB_BORN : Nat := 1 <<< 29
def SB_ACTIVE : Nat := 1 <<< 30
def SB_NOUSER : Nat := 1 <<< 31

/-- pipefs's `s_flags` (0xe0400000). -/
def pipefsSFlags : Nat := SB_KERNMOUNT ||| SB_NOUSER ||| SB_BORN ||| SB_ACTIVE

def MNT_NOATIME : Nat := 0x08
def MNT_NODIRATIME : Nat := 0x10
def MNT_RELATIME : Nat := 0x20
def MNT_INTERNAL : Nat := 0x4000

/-- `pipe_mnt->mnt_flags` (fs/namespace.c:1220). -/
def pipeMntFlags : Nat := MNT_INTERNAL

/-- `enum file_time_flags` (include/linux/fs.h:2565-2570). -/
def S_ATIME : Nat := 1
def S_MTIME : Nat := 2
def S_CTIME : Nat := 4
def S_VERSION : Nat := 8

def I_DIRTY_SYNC : Nat := 1 <<< 3
def I_DIRTY_TIME : Nat := 1 <<< 11

/-! ## Inode allocation and release (cuts) -/

/-- `new_inode_pseudo(pipe_mnt->mnt_sb)` (fs/inode.c:1102-1105) with the
    `get_next_ino` of `get_pipe_inode` (fs/pipe.c:893): the inode-allocation
    cut, no decisions (design section 5, audit M3: WireGuard's `sock_alloc`
    runs the same functions in-window, so they are not listed in
    `correspondence/kcov.json`). `none` when the `.allocInode` site fails.
    Contract (`inode_init_always_gfp`, fs/inode.c:158-240): `i_flags = 0`,
    `i_count = 1`, `i_op = &empty_iops`, `i_pipe = NULL`, `i_state = 0`, no
    stamps yet; `i_ino` from the mirror-local `Kernel.lastIno` (`last_ino`
    has an unknown boot baseline and `i_ino` is unobserved). `get_pipe_inode`
    then sets `i_pipe`, `i_mode` and `i_state` itself. -/
def newInodePseudo : M (Option PipefsInodeId) := do
  if !(← envOk .allocInode) then return none
  let k ← getK
  let id := k.nextInode
  let ino := k.lastIno + 1
  setInode id { iIno := ino, iMode := 0, iFlags := 0, iState := 0, iCount := 1 }
  modifyK fun k => { k with nextInode := id + 1, lastIno := ino }
  return some id

/-- `iput(inode)` of a pipefs inode (fs/inode.c:1889-1904), a cut. Contract:
    `atomic_dec_and_lock(&i_count)`; at zero, `I_DIRTY_TIME` is clear (the
    lazytime arm is not taken), `iput_final` drops the inode
    (`generic_drop_inode`: pseudo inodes are unhashed) and `evict` →
    `destroy_inode` → `free_inode_nonrcu` frees it (no RCU deferral:
    fs/pipe.c:1425). `i_pipe` is not consulted: `put_pipe_info` cleared it,
    or on the `-ENOPKG` arm `create_pipe_files` freed the pipe first. -/
def iputPipefs (id : PipefsInodeId) : M Unit := do
  let ino ← getInode id
  if ino.iCount == 0 then invariant s!"iput of pipefs inode {id} with i_count 0"
  if ino.iCount > 1 then
    setInode id { ino with iCount := ino.iCount - 1 }
    return
  -- `inode->i_nlink && (inode->i_state & I_DIRTY_TIME)` (pseudo inodes keep
  -- i_nlink = 1)
  if ino.iState &&& I_DIRTY_TIME != 0 then unsupported "iput: lazytime dirty inode"
  modifyK fun k => { k with inodes := k.inodes.erase id }

/-- `dput(dentry)` of a pipe file's pseudo dentry (fs/dcache.c:845), a cut
    apart from the count: `d_lockref.count` drops; the last reference kills
    the dentry (`DCACHE_NORCU` from `d_alloc_pseudo`, fs/dcache.c:1770) and
    `dentry_unlink_inode` puts its inode. -/
def dputPipefs (id : PipefsInodeId) : M Unit := do
  let ino ← getInode id
  if ino.dCount == 0 then invariant s!"dput of the pipefs dentry of inode {id} with count 0"
  setInode id { ino with dCount := ino.dCount - 1 }
  if ino.dCount == 1 then iputPipefs id

/-! ## The clock -/

/-- `timestamp_truncate(t, inode)` (fs/inode.c:2612-2631) for pipefs. -/
def timestampTruncate (t : Timespec64) : M Timespec64 := do
  let mut t := t
  -- `t.tv_sec = clamp(t.tv_sec, sb->s_time_min, sb->s_time_max)`
  -- (__clamp, include/linux/minmax.h:181-182: `>= hi`, then `<= lo`)
  if ← branchCmp .truncClampMax (t.tvSec ≥ pipefsTimeMax) t.tvSec pipefsTimeMax then
    t := { t with tvSec := pipefsTimeMax }
  else if ← branch .truncClampMin (t.tvSec ≤ pipefsTimeMin) then
    t := { t with tvSec := pipefsTimeMin }
  -- `unlikely(t.tv_sec == sb->s_time_max || t.tv_sec == sb->s_time_min)`
  let atLimit ← do
    if ← branchCmp .truncSecIsMax (t.tvSec == pipefsTimeMax) t.tvSec pipefsTimeMax then pure true
    else branchCmp .truncSecIsMin (t.tvSec == pipefsTimeMin) t.tvSec pipefsTimeMin
  if atLimit then t := { t with tvNsec := 0 }
  if ← branchCmp .truncGranOne (pipefsTimeGran == 1) pipefsTimeGran 1 then
    pure ()   -- nothing
  else
    unsupported "timestamp_truncate: s_time_gran != 1"
  return t

/-- `current_time(inode)` (fs/inode.c:2644-2650): one clock record. -/
def currentTime : M Timespec64 := do
  let now ← hiddenTimespec .currentTime   -- ktime_get_coarse_real_ts64(&now)
  timestampTruncate now

/-- `timespec64_equal(a, b)` (include/linux/time64.h:46-50). -/
def timespec64Equal (a b : Timespec64) : M Bool := do
  if ← branchCmp .tsEqualSec (a.tvSec == b.tvSec) a.tvSec b.tvSec then
    branchCmp .tsEqualNsec (a.tvNsec == b.tvNsec) a.tvNsec b.tvNsec
  else
    return false

/-- `inode_set_ctime_current(inode)` (fs/inode.c:2660-2666). -/
def inodeSetCtimeCurrent (id : PipefsInodeId) : M Timespec64 := do
  let now ← currentTime
  setInode id { (← getInode id) with iCtime := now }   -- inode_set_ctime_to_ts
  return now

/-- `simple_inode_init_ts(inode)` (fs/libfs.c:2101-2108): one clock read;
    atime, mtime and ctime all set to it. Returns the stamp. -/
def simpleInodeInitTs (id : PipefsInodeId) : M Timespec64 := do
  let ts ← inodeSetCtimeCurrent id
  setInode id { (← getInode id) with iAtime := ts, iMtime := ts }
  return ts

/-! ## Timestamp updates -/

/-- `__mark_inode_dirty(inode, flags)` (fs/fs-writeback.c:2492-2600), a cut.
    Contract: `pipefs_ops` has no `dirty_inode` (2557-2558 not taken);
    `get_pipe_inode` set `i_state = I_DIRTY`, so for the `I_DIRTY_SYNC` (or
    empty) flags of these paths `(inode->i_state & flags) == flags` returns
    at 2580-2581 with no state change. Anything else leaves the domain. -/
def markInodeDirty (id : PipefsInodeId) (flags : Nat) : M Unit := do
  let ino ← getInode id
  if flags &&& I_DIRTY_TIME != 0 || ino.iState &&& flags != flags then
    unsupported s!"__mark_inode_dirty: flags {flags} change i_state {ino.iState}"

/-- `inode_update_timestamps(inode, flags)` (fs/inode.c:1988-2019). -/
def inodeUpdateTimestamps (id : PipefsInodeId) (flags : Nat) : M Nat := do
  let mut updated := 0
  let mask := S_MTIME ||| S_CTIME ||| S_VERSION
  let now ← do
    if ← branchCmp .tsUpdateCmtime (flags &&& mask != 0) (flags &&& mask) 0 then
      let ino ← getInode id
      let ctime := ino.iCtime
      let mtime := ino.iMtime
      let now ← inodeSetCtimeCurrent id
      if ← branch .tsUpdateCtimeDiffers (!(← timespec64Equal now ctime)) then
        updated := updated ||| S_CTIME
      if ← branch .tsUpdateMtimeDiffers (!(← timespec64Equal now mtime)) then
        setInode id { (← getInode id) with iMtime := now }   -- inode_set_mtime_to_ts
        updated := updated ||| S_MTIME
      if ← branchCmp .tsUpdateIVersion (pipefsSFlags &&& SB_I_VERSION != 0) (pipefsSFlags &&& SB_I_VERSION) 0 then
        unsupported "inode_maybe_inc_iversion"   -- SB_I_VERSION is clear on pipefs
      pure now
    else
      currentTime
  if ← branchCmp .tsUpdateAtimeFlag (flags &&& S_ATIME != 0) (flags &&& S_ATIME) 0 then
    let atime := (← getInode id).iAtime
    if ← branch .tsUpdateAtimeDiffers (!(← timespec64Equal now atime)) then
      setInode id { (← getInode id) with iAtime := now }   -- inode_set_atime_to_ts
      updated := updated ||| S_ATIME
  return updated

/-- `generic_update_time(inode, flags)` (fs/inode.c:2034-2045). -/
def genericUpdateTime (id : PipefsInodeId) (flags : Nat) : M Nat := do
  let updated ← inodeUpdateTimestamps id flags
  let mut dirtyFlags := 0
  let mask := S_ATIME ||| S_MTIME ||| S_CTIME
  if ← branchCmp .genericUpdated (updated &&& mask != 0) (updated &&& mask) 0 then
    dirtyFlags :=
      if ← branchCmp .genericLazytime (pipefsSFlags &&& SB_LAZYTIME != 0) (pipefsSFlags &&& SB_LAZYTIME) 0
      then I_DIRTY_TIME else I_DIRTY_SYNC
  if ← branchCmp .genericVersion (updated &&& S_VERSION != 0) (updated &&& S_VERSION) 0 then
    dirtyFlags := dirtyFlags ||| I_DIRTY_SYNC
  markInodeDirty id dirtyFlags
  return updated

/-- `inode_update_time(inode, flags)` (fs/inode.c:2052-2058). -/
def inodeUpdateTime (id : PipefsInodeId) (flags : Nat) : M Int := do
  -- `inode->i_op->update_time`: `empty_iops` has none
  if ← branch .inodeUpdateTimeHasOp false then
    unsupported "i_op->update_time"
  _ ← genericUpdateTime id flags
  return 0

/-- `relatime_need_update(mnt, inode, now)` (fs/inode.c:1939-1970). -/
def relatimeNeedUpdate (_now : Timespec64) : M Bool := do
  if ← branchCmp .relatimeNotSet (pipeMntFlags &&& MNT_RELATIME == 0) (pipeMntFlags &&& MNT_RELATIME) 0 then
    return true
  unsupported "relatime_need_update with MNT_RELATIME"   -- pipe_mnt has MNT_INTERNAL only

/-- `atime_needs_update(path, inode)` (fs/inode.c:2070-2104). -/
def atimeNeedsUpdate (id : PipefsInodeId) : M Bool := do
  let ino ← getInode id
  if ← branchCmp .atimeSNoatime (ino.iFlags &&& S_NOATIME != 0) (ino.iFlags &&& S_NOATIME) 0 then
    return false
  -- HAS_UNMAPPED_ID(mnt_idmap(mnt), inode) (include/linux/fs.h:2384-2389):
  -- nop_mnt_idmap, and i_uid/i_gid are the creating root's (fs/pipe.c:907-908)
  let unmapped ← do
    if ← branch .unmappedUid false then pure true
    else branch .unmappedGid false
  if unmapped then return false
  let noatime := SB_RDONLY ||| SB_NOATIME
  if ← branchCmp .atimeIsNoatime (pipefsSFlags &&& noatime != 0) (pipefsSFlags &&& noatime) 0 then
    return false
  if ← branchCmp .atimeSbNodiratime (pipefsSFlags &&& SB_NODIRATIME != 0) (pipefsSFlags &&& SB_NODIRATIME) 0 then
    unsupported "SB_NODIRATIME on pipefs"   -- the S_ISDIR operand
  if ← branchCmp .atimeMntNoatime (pipeMntFlags &&& MNT_NOATIME != 0) (pipeMntFlags &&& MNT_NOATIME) 0 then
    return false
  if ← branchCmp .atimeMntNodiratime (pipeMntFlags &&& MNT_NODIRATIME != 0) (pipeMntFlags &&& MNT_NODIRATIME) 0 then
    unsupported "MNT_NODIRATIME on pipe_mnt"   -- the S_ISDIR operand
  let now ← currentTime
  if ← branch .atimeNoRelatimeUpdate (!(← relatimeNeedUpdate now)) then
    return false
  let atime := (← getInode id).iAtime
  if ← branch .atimeEqual (← timespec64Equal atime now) then
    return false
  return true

/-- `touch_atime(&file->f_path)` (fs/inode.c:2106-2132). -/
def touchAtime (id : PipefsInodeId) : M Unit := do
  let needs ← atimeNeedsUpdate id
  if ← branchCmp .touchAtimeNoUpdate (!needs) (if needs then 1 else 0) 0 then
    return
  -- sb_start_write_trylock(inode->i_sb): a cut, succeeds (no freeze)
  if ← branch .touchAtimeTrylockFailed false then
    return
  -- mnt_get_write_access(mnt): a cut returning 0 (pipe_mnt is not read-only)
  if ← branchCmp .touchAtimeWriteAccessErr false 0 0 then
    return   -- skip_update; sb_end_write is a cut
  _ ← inodeUpdateTime id S_ATIME
  -- mnt_put_write_access(mnt); sb_end_write(inode->i_sb): cuts

/-- The pipefs inode a file's `f_inode` points to. -/
private def pipefsInodeOf (f : File) (what : String) : M PipefsInodeId :=
  match f.fInode with
  | some (.pipefs id) => return id
  | some .anon => unsupported s!"{what} on the anonymous inode"
  | some (.fixture name) => unsupported s!"{what} on fixture file {name}"
  | none => invariant s!"{what}: file->f_inode is NULL"

/-- `file_accessed(file)` (include/linux/fs.h:2576-2580) and `touch_atime`:
    one or two clock reads, none with `O_NOATIME`. -/
def fileAccessed (f : File) : M Unit := do
  if ← branchCmp .fileAccessedNotNoatime (!hasFlag f.fFlags O_NOATIME) (f.fFlags &&& O_NOATIME).toNat 0 then
    touchAtime (← pipefsInodeOf f "touch_atime")

/-- `inode_needs_update_time(inode)` (fs/inode.c:2214-2236). -/
def inodeNeedsUpdateTime (id : PipefsInodeId) : M Nat := do
  let mut syncIt := 0
  let now ← currentTime
  let ino ← getInode id
  if ← branchCmp .needsNocmtime (ino.iFlags &&& S_NOCMTIME != 0) (ino.iFlags &&& S_NOCMTIME) 0 then
    return 0
  if ← branch .needsMtimeDiffers (!(← timespec64Equal ino.iMtime now)) then
    syncIt := S_MTIME
  if ← branch .needsCtimeDiffers (!(← timespec64Equal ino.iCtime now)) then
    syncIt := syncIt ||| S_CTIME
  if ← branchCmp .needsIVersion (pipefsSFlags &&& SB_I_VERSION != 0) (pipefsSFlags &&& SB_I_VERSION) 0 then
    unsupported "inode_iversion_need_inc"   -- SB_I_VERSION is clear on pipefs
  return syncIt

/-- `file_update_time(file)` (fs/inode.c:2266-2276) with `__file_update_time`
    (2238-2250) inlined: one or two clock reads; the C's return value. -/
def fileUpdateTime (f : File) : M Int := do
  let id ← pipefsInodeOf f "file_update_time"
  let ret : Int := (← inodeNeedsUpdateTime id)
  if ← branchCmp .fileUpdateNothing (ret ≤ 0) ret 0 then
    return ret
  -- __file_update_time(file, ret)
  let mut r : Int := 0
  -- `!mnt_get_write_access_file(file)`: a cut returning 0
  if ← branchCmp .fileUpdateWriteAccessOk true 0 0 then
    r ← inodeUpdateTime id ret.toNat
    -- mnt_put_write_access_file(file): a cut
  return r

/-! ## `i_readcount` (include/linux/fs.h:3125-3133, real with CONFIG_FILE_LOCKING=y) -/

/-- `i_readcount_inc(inode)`: `atomic_inc`, no decision. -/
def inodeReadcountInc : Option InodeId → M Unit
  | some (.pipefs id) => do
    let ino ← getInode id
    setInode id { ino with iReadcount := ino.iReadcount + 1 }
  -- no read-only file of the anonymous inode exists in the slice (eventfd
  -- files are O_RDWR)
  | some .anon => unsupported "i_readcount_inc of the anonymous inode"
  | some (.fixture name) => unsupported s!"i_readcount_inc of fixture file {name}"
  | none => invariant "i_readcount_inc: file->f_inode is NULL"

/-- `i_readcount_dec(inode)`: `BUG_ON(atomic_dec_return(&inode->i_readcount) < 0)`. -/
def inodeReadcountDec : Option InodeId → M Unit
  | some (.pipefs id) => do
    let ino ← getInode id
    let new : Int := (ino.iReadcount : Int) - 1
    if ← branchCmp .iReadcountDecUnderflow (new < 0) new 0 then
      invariant s!"i_readcount of pipefs inode {id} below zero (BUG_ON)"
    setInode id { ino with iReadcount := ino.iReadcount - 1 }
  | some .anon => unsupported "i_readcount_dec of the anonymous inode"
  -- W8: the pin's nsfs inode (read-only); without CONFIG_IMA the helper is
  -- empty (fs/internal.h), so nothing to model
  | some (.fixture "netns-pin") => pure ()
  | some (.fixture name) => unsupported s!"i_readcount_dec of fixture file {name}"
  | none => invariant "i_readcount_dec: file->f_inode is NULL"

end Leanux
