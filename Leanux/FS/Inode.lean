import Leanux.Kernel.Defs

/-!
# fs/inode.c, fs/libfs.c, include/linux/time64.h — pipefs inode timestamps

Interface stubs for workstream P stream 3 (docs/2026-10-05-p-pipes.md
sections 3, 5 and 11). Stream 3 fills in the bodies: the inode-allocation cut
(`.allocInode`), `simple_inode_init_ts`, `current_time` and
`timestamp_truncate`, `file_accessed`/`touch_atime`, `file_update_time`,
`timespec64_equal`, and `iput` for a pipefs inode. Every `current_time`
consumes one `.currentTime` record (`hiddenTimespec`), in C order. Stream 2
(`Leanux/FS/Pipe.lean`) calls these signatures.
-/

namespace Leanux

/-- `new_inode_pseudo(pipe_mnt->mnt_sb)` (fs/inode.c:1102-1105): the
    inode-allocation cut, no decisions (design section 5, audit M3). `none`
    when the `.allocInode` site fails. On success, a new `Kernel.inodes`
    entry with `i_flags = 0`, `i_count = 1`, `i_pipe = NULL` and `i_ino` from
    `Kernel.lastIno`. -/
def newInodePseudo : M (Option PipefsInodeId) :=
  unsupported "P3: not yet (new_inode_pseudo)"

/-- `simple_inode_init_ts(inode)` (fs/libfs.c:2101-2108): one clock read;
    atime, mtime and ctime all set to it. Returns the stamp. -/
def simpleInodeInitTs (_ino : PipefsInodeId) : M Timespec64 :=
  unsupported "P3: not yet (simple_inode_init_ts)"

/-- `file_accessed(file)` (include/linux/fs.h:2576-2580) and `touch_atime`
    (fs/inode.c:2106-2132): one or two clock reads, none with `O_NOATIME`. -/
def fileAccessed (_f : File) : M Unit :=
  unsupported "P3: not yet (file_accessed)"

/-- `file_update_time(file)` (fs/inode.c:2266-2276): one or two clock
    reads; the C's return value. -/
def fileUpdateTime (_f : File) : M Int :=
  unsupported "P3: not yet (file_update_time)"

/-- `iput(inode)` of a pipefs inode: the last reference frees it
    (`pipefs_ops.destroy_inode = free_inode_nonrcu`, fs/pipe.c:1425). -/
def iputPipefs (_ino : PipefsInodeId) : M Unit :=
  unsupported "P3: not yet (iput)"

end Leanux
