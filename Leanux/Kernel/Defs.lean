import Leanux.Kernel.Decision
import Leanux.WG.Types
import Std.Data.TreeMap
import Std.Data.TreeSet
import Std.Data.HashSet
import Lean.Data.Json

/-!
# Mirror state and execution monad

State is shaped like the configured C structures (Linux 6.12.110, x86-64):
one structure per C struct, pointers replaced by abstract identities, and each
object owned once in a finite identity-keyed store. Descriptor slots hold
identities, not ownership. Field names follow the C. The whole state is
finite and comparable (`BEq`), so a relation to the kernel's objects can be
stated slot by slot and object by object.
-/

namespace Leanux
open Std

/-! ## Constants (x86-64 UAPI and include/linux/fs.h) -/

def O_ACCMODE : UInt32 := 0o3
def O_RDONLY : UInt32 := 0o0
def O_WRONLY : UInt32 := 0o1
def O_RDWR : UInt32 := 0o2
/-- `O_NOTIFICATION_PIPE = O_EXCL` (include/uapi/linux/watch_queue.h:9). -/
def O_NOTIFICATION_PIPE : UInt32 := 0o200
def O_APPEND : UInt32 := 0o2000
def O_NONBLOCK : UInt32 := 0o4000
def O_DSYNC : UInt32 := 0o10000
def FASYNC : UInt32 := 0o20000
def O_DIRECT : UInt32 := 0o40000
def O_NOATIME : UInt32 := 0o1000000
def O_CLOEXEC : UInt32 := 0o2000000
/-- `SETFL_MASK` (fs/fcntl.c:37); `O_NDELAY` is `O_NONBLOCK` on x86-64. -/
def SETFL_MASK : UInt32 := O_APPEND ||| O_NONBLOCK ||| O_DIRECT ||| O_NOATIME
def O_SYNC_INTERNAL : UInt32 := 0o4000000   -- __O_SYNC

def EFD_SEMAPHORE : UInt32 := 1
def EFD_SHARED_FCNTL_FLAGS : UInt32 := O_CLOEXEC ||| O_NONBLOCK
def EFD_FLAGS_SET : UInt32 := EFD_SHARED_FCNTL_FLAGS ||| EFD_SEMAPHORE

def FD_CLOEXEC : Nat := 1

def FMODE_READ : UInt32 := (1 : UInt32) <<< 0
def FMODE_WRITE : UInt32 := (1 : UInt32) <<< 1
def FMODE_LSEEK : UInt32 := (1 : UInt32) <<< 2
def FMODE_PATH : UInt32 := (1 : UInt32) <<< 14
def FMODE_ATOMIC_POS : UInt32 := (1 : UInt32) <<< 15
def FMODE_WRITER : UInt32 := (1 : UInt32) <<< 16
def FMODE_CAN_READ : UInt32 := (1 : UInt32) <<< 17
def FMODE_CAN_WRITE : UInt32 := (1 : UInt32) <<< 18
def FMODE_OPENED : UInt32 := (1 : UInt32) <<< 19
def FMODE_STREAM : UInt32 := (1 : UInt32) <<< 21
def FMODE_CAN_ODIRECT : UInt32 := (1 : UInt32) <<< 22
def FMODE_BACKING : UInt32 := (1 : UInt32) <<< 24
def FMODE_NONOTIFY : UInt32 := (1 : UInt32) <<< 25
def FMODE_NOWAIT : UInt32 := (1 : UInt32) <<< 27
def FMODE_NEED_UNMOUNT : UInt32 := (1 : UInt32) <<< 28
def FMODE_NOACCOUNT : UInt32 := (1 : UInt32) <<< 29

def EBADF : Int := 9
def EAGAIN : Int := 11
def ENOMEM : Int := 12
def EFAULT : Int := 14
def EBUSY : Int := 16
def EPIPE : Int := 32
def ENOPKG : Int := 65
def ENFILE : Int := 23
def EINVAL : Int := 22
def EMFILE : Int := 24
def EPERM : Int := 1
def ENODEV : Int := 19
def EBADR : Int := 53
def EOPNOTSUPP : Int := 95
def EPFNOSUPPORT : Int := 96
def ENOKEY : Int := 126
def EDESTADDRREQ : Int := 89
def EPROTONOSUPPORT : Int := 93
def ENETUNREACH : Int := 101
-- W4: dev_validate_mtu's refusal, and the sender's datagram above cork->fragsize
def ERANGE : Int := 34
def EMSGSIZE : Int := 90
def ENONET : Int := 64
def ESRCH : Int := 3
def EADDRNOTAVAIL : Int := 99
def EAFNOSUPPORT : Int := 97
/-- L: `wg_create` of an existing wg0; a bind at a held port. -/
def EEXIST : Int := 17
def EADDRINUSE : Int := 98

def ULLONG_MAX : UInt64 := 18446744073709551615
/-- `NR_OPEN_DEFAULT = BITS_PER_LONG`: capacity of the embedded initial table. -/
def NR_OPEN_DEFAULT : Nat := 64
def BITS_PER_LONG : Nat := 64
/-- `sysctl_nr_open` default, `NR_OPEN = 1024 * 1024`. -/
def SYSCTL_NR_OPEN : Nat := 1048576
/-- `MAX_RW_COUNT = INT_MAX & PAGE_MASK`. -/
def MAX_RW_COUNT : Nat := 0x7ffff000

def hasFlag (flags mask : UInt32) : Bool := flags &&& mask != 0

/-! ## Pipes (P, docs/2026-10-05-p-pipes.md section 2) -/

def PAGE_SIZE : Nat := 4096
/-- include/linux/pipe_fs_i.h:5. -/
def PIPE_DEF_BUFFERS : Nat := 16
/-- `struct pipe_buffer` flags (include/linux/pipe_fs_i.h:7-12; `LOSS` needs
    `CONFIG_WATCH_QUEUE`, unset). -/
def PIPE_BUF_FLAG_LRU : UInt32 := 0x01
def PIPE_BUF_FLAG_ATOMIC : UInt32 := 0x02
def PIPE_BUF_FLAG_GIFT : UInt32 := 0x04
def PIPE_BUF_FLAG_PACKET : UInt32 := 0x08
def PIPE_BUF_FLAG_CAN_MERGE : UInt32 := 0x10
def PIPE_BUF_FLAG_WHOLE : UInt32 := 0x20

/-- `i_flags` bits (include/linux/fs.h:2306-2314) and `i_mode` bits
    (include/uapi/linux/stat.h). -/
def S_NOATIME : Nat := 1 <<< 1
def S_APPEND : Nat := 1 <<< 2
def S_NOCMTIME : Nat := 1 <<< 7
def S_PRIVATE : Nat := 1 <<< 9
def S_IFMT : Nat := 0o170000
def S_IFIFO : Nat := 0o010000
def S_IFCHR : Nat := 0o020000
def S_IFREG : Nat := 0o100000
def S_IRUSR : Nat := 0o400
def S_IWUSR : Nat := 0o200
/-- `I_DIRTY = I_DIRTY_SYNC | I_DIRTY_DATASYNC | I_DIRTY_PAGES`
    (include/linux/fs.h:2502-2519). -/
def I_DIRTY : Nat := (1 <<< 3) ||| (1 <<< 4) ||| (1 <<< 5)

/-- `SIGPIPE` (arch/x86/include/uapi/asm/signal.h:35). -/
def SIGPIPE : Nat := 13

/-! ## Objects -/

abbrev FileId := Nat
abbrev CtxId := Nat
/-- Identities of `struct pipe_inode_info`, of the pipes' data pages and of
    pipefs inodes, each into its store in `Kernel`. -/
abbrev PipeId := Nat
abbrev PageId := Nat
abbrev PipefsInodeId := Nat
/-- epoll identities (docs/2026-10-12-epoll-design.md, 4.1): a `struct
    eventpoll`, an `epitem` and an `eppoll_entry`. Their stores arrive with
    the epoll mirror (stream S); the wait-queue service names them now. -/
abbrev EpId := Nat
abbrev EpiId := Nat
abbrev PwqId := Nat

/-! ## Wait queues (include/linux/wait.h, kernel/sched/wait.c; design 4.1) -/

/-- `wait_queue_entry.func`, the callback a wake dispatches to. In tier 1
    the only waiter is epoll's `ep_poll_callback` (fs/eventpoll.c), whose
    entry is an `eppoll_entry`; tier 2 adds a sleeping task. -/
inductive WaitFunc where
  | epPollCallback (pwq : PwqId)
  deriving Repr, BEq, DecidableEq

/-- `struct wait_queue_entry` (wait.h:31-36). `flags` carries
    `WQ_FLAG_EXCLUSIVE` only (no caller in the domain sets the others);
    `private` is implied by `func`; `entry` is the position in its queue. -/
structure WaitEntry where
  func : WaitFunc
  exclusive : Bool := false
  deriving Repr, BEq

/-- `struct wait_queue_head` (wait.h:38-41): the entries, head first. The
    spinlock is a cut (one task). -/
structure WaitQueue where
  entries : List WaitEntry := []
  deriving Repr, BEq

/-- A `wait_queue_head_t *`: the heads the domain's objects embed. The
    eventpoll heads (`ep->wq`, `ep->poll_wait`) arrive with the epoll mirror. -/
inductive WaitQueueRef where
  | pipeRd (p : PipeId)
  | pipeWr (p : PipeId)
  | eventfdWqh (c : CtxId)
  | epWq (e : EpId)
  | epPollWait (e : EpId)
  deriving Repr, BEq, DecidableEq

/-- The `struct file_operations` table a file's `f_op` points to. Fixture files
    (console, KCOV, /dev/null) are opened by the harness outside the trace; their
    operations are outside the modeled slice. -/
inductive FopsId where
  | eventfd
  /-- `pipefifo_fops` (fs/pipe.c:1232-1241). -/
  | pipefifo
  /-- `eventpoll_fops` (fs/eventpoll.c:1271-1280). -/
  | eventpoll
  | fixture (name : String)
  deriving Repr, BEq, DecidableEq

/-- What a file's `private_data` points to. -/
inductive PrivateData where
  | eventfdCtx (ctx : CtxId)
  /-- A pipe file's `private_data` is its `pipe_inode_info` (fs/pipe.c:947,957). -/
  | pipe (id : PipeId)
  /-- An epoll file's `private_data` is its `struct eventpoll` (fs/eventpoll.c:2424). -/
  | eventpoll (ep : EpId)
  deriving Repr, BEq, DecidableEq

/-- `file->f_ep` (include/linux/fs.h): NULL; a non-epoll file's
    `epitems_head` (its `epitems` hlist, head first; the head's `next` and
    `file`, the `tfile_check_list` membership, are `Kernel.tfileCheckList`); or
    an epoll file's own `ep->refs` (`ep_attach_file`, fs/eventpoll.c:1718). -/
inductive FEp where
  | null
  | head (items : List EpiId)
  | epRefs (ep : EpId)
  deriving Repr, BEq, DecidableEq

/-- The inode a file's `f_inode` points to: the shared anonymous inode, or a
    fixture file's inode (outside the slice). -/
inductive InodeId where
  | anon
  /-- A pipefs inode, owned by `Kernel.inodes` (`get_pipe_inode`). -/
  | pipefs (id : PipefsInodeId)
  | fixture (name : String)
  deriving Repr, BEq, DecidableEq

/-- `struct file`. `fCount` is `f_count`. Fixture files carry references held
    outside the trace (other processes, the KCOV mapping), so trace operations
    never drop them to zero; the exact external count is not observable. -/
structure File where
  fFlags : UInt32
  fMode : UInt32
  fCount : Nat
  /-- `f_op`: NULL until `file_init_path` (file_table.c:348). -/
  fOp : Option FopsId := none
  /-- `f_inode`: set by `file_init_path` (file_table.c:334). -/
  fInode : Option InodeId := none
  /-- `private_data`: set by `__anon_inode_getfile` (anon_inodes.c:129). -/
  privateData : Option PrivateData := none
  fPos : Int := 0
  fIocbFlags : UInt32 := 0
  /-- `f_owner` is non-NULL only after F_SETOWN-style calls (outside the slice). -/
  fOwner : Bool := false
  /-- `f_ep` (include/linux/fs.h): NULL, or the file's epoll links (`FEp`). -/
  fEp : FEp := .null
  /-- `f_pipe` (include/linux/fs.h:1092), written at fs/pipe.c:948,958 and
      read only by `pipe_poll`. -/
  fPipe : Nat := 0
  deriving Repr, BEq

/-- `struct eventfd_ctx`. `wqh` is the wait queue head (`init_waitqueue_head`,
    eventfd.c:398); its lock is a cut (one task). `id` is the `eventfd_ida`
    number. -/
structure EventfdCtx where
  kref : Nat
  count : UInt64
  flags : UInt32
  /-- `none` until `ctx->id = ida_alloc(...)` (eventfd.c:401): kmalloc leaves it unset. -/
  id : Option Int
  wqh : WaitQueue := {}
  deriving Repr, BEq

/-- `struct timespec64` (include/linux/time64.h): 16 bytes, `tv_sec` then
    `tv_nsec`, both signed 64-bit. -/
structure Timespec64 where
  tvSec : Int
  tvNsec : Int
  deriving Repr, BEq, Inhabited

/-- `struct pipe_buffer` (include/linux/pipe_fs_i.h:26-32). `ops` is
    "`&anon_pipe_buf_ops`, else NULL" (`pipe_buf_release` NULLs it); `private`
    is unused on these paths. -/
structure PipeBuffer where
  page : Option PageId := none
  offset : Nat := 0
  len : Nat := 0
  ops : Bool := false
  flags : UInt32 := 0
  deriving Repr, BEq, Inhabited

/-- `pipe->user`: always `&root_user`, the one `UserStruct` (`Kernel.user`). -/
inductive UserId where
  | root
  deriving Repr, BEq, DecidableEq

/-- `struct pipe_inode_info` (include/linux/pipe_fs_i.h:58-83). `head` and
    `tail` wrap as `unsigned int` and are masked with `ringSize - 1` only at
    dereference. The mutex and the queue locks are cuts (one task);
    `rd_wait`/`wr_wait` are the wait queues (`init_waitqueue_head`,
    fs/pipe.c:819-820); `watch_queue` and `note_loss` do not exist in this
    build; `fasync_readers`/`fasync_writers` are NULL lists, kept as booleans. -/
structure PipeInodeInfo where
  head : UInt32 := 0
  tail : UInt32 := 0
  rdWait : WaitQueue := {}
  wrWait : WaitQueue := {}
  maxUsage : Nat
  ringSize : Nat
  nrAccounted : Nat
  readers : Nat := 0
  writers : Nat := 0
  files : Nat := 0
  rCounter : Nat := 0
  wCounter : Nat := 0
  pollUsage : Bool := false
  tmpPage : Option PageId := none
  fasyncReaders : Bool := false
  fasyncWriters : Bool := false
  bufs : Array PipeBuffer
  user : UserId := .root
  deriving Repr, BEq

/-- The `struct page` of a pipe data page: its refcount (`page_count`) and
    its bytes (the digest check observes them). -/
structure Page where
  pageCount : Nat := 1
  bytes : ByteArray
  deriving Inhabited

instance : BEq Page where
  beq a b := a.pageCount == b.pageCount && a.bytes.data == b.bytes.data

/-- `struct inode` of a pipefs inode, the fields these paths use.
    `get_pipe_inode` sets `i_state = I_DIRTY` and `i_mode = S_IFIFO | S_IRUSR |
    S_IWUSR` (fs/pipe.c:905-906); the inode-allocation cut (`.allocInode`)
    gives `i_flags = 0`, `i_count = 1`, `i_pipe = NULL` and `i_ino` from a
    mirror-local counter. `dCount` is the pseudo dentry's `d_lockref.count`
    (the dentry is otherwise a cut): its last `dput` releases the inode. -/
structure Inode where
  iIno : Nat
  iMode : Nat
  iFlags : Nat := 0
  iState : Nat := 0
  iAtime : Timespec64 := ⟨0, 0⟩
  iMtime : Timespec64 := ⟨0, 0⟩
  iCtime : Timespec64 := ⟨0, 0⟩
  iPipe : Option PipeId := none
  iReadcount : Nat := 0
  iWritecount : Nat := 0
  iCount : Nat := 1
  dCount : Nat := 0
  deriving Repr, BEq

/-- `struct user_struct` (include/linux/sched/user.h:14-21), the one field
    these paths use; one instance, `root_user`. -/
structure UserStruct where
  pipeBufs : Nat := 0
  /-- `epoll_watches`: a plain count without `CONFIG_SMP` (design 3.4),
      tracked from a baseline of 0 (no epoll item outside the trace: the
      fixture's warm-up closed its own). -/
  epollWatches : Nat := 0
  deriving Repr, BEq

/-! ## epoll (fs/eventpoll.c; docs/2026-10-12-epoll-design.md, 4.1)

Line numbers are the pristine source's (`.deps/linux`): the kind-308 hook
keeps the file's line count, as every patch of an anchored file does, since
the check reads statements and spans from the pristine tree. -/

/-- `struct eppoll_entry` (fs/eventpoll.c:234-249): `whead` is NULL only
    after a `POLLFREE` wake (out of the domain); `base` the item; its `wait`
    entry sits on `whead` with `func = ep_poll_callback`; `next` chains it in
    `Epitem.pwqlist`. -/
structure EppollEntry where
  whead : Option WaitQueueRef
  base : EpiId
  deriving Repr, BEq

/-- `struct epitem` (fs/eventpoll.c:257-300). `ffd` is `(file, fd)` with the
    file's address from the kind-308 record (`ep_cmp_ffd`'s first key);
    `linked` is `ep_is_linked` (`rdllink` on the set's `rdllist`), `onOvflist`
    is `epi_on_ovflist` (`ovflist_next != EP_UNACTIVE_PTR`); `pwqlist` is
    head first, as `next` chains them (:1563-1564); `ws` is NULL (no
    `CONFIG_PM`). -/
structure Epitem where
  ep : EpId
  file : FileId
  fd : Int
  fileAddr : Nat
  events : UInt32
  data : UInt64
  linked : Bool := false
  onOvflist : Bool := false
  pwqlist : List PwqId := []
  dying : Bool := false
  deriving Repr, BEq

/-- `struct eventpoll` (fs/eventpoll.c:307-377). `ovflist` is `none` for
    `EP_UNACTIVE_PTR` (not scanning) and `some chain` while scanning, the
    chain head first as `ovflist_next` links it (LIFO); `seq` is the
    `seqcount_spinlock_t`, bumped twice by each `ep_start_scan` and
    `ep_done_scan`; `rbr` is the rbtree as an ordered map keyed by
    `(fileAddr, fd)` ascending, `ep_cmp_ffd`'s order (the cut of design 3.2,
    named at `Eventpoll.lean`'s `epFind`/`epRbtreeInsert`); `refs` the outer
    items watching this set, head first; `file` the set's own file
    (:2430); `ws` is NULL; the mutex and locks are cuts (one task). -/
structure Eventpoll where
  wq : WaitQueue := {}
  pollWait : WaitQueue := {}
  rdllist : List EpiId := []
  ovflist : Option (List EpiId) := none
  seq : Nat := 0
  rbr : List ((Nat × Int) × EpiId) := []
  refs : List EpiId := []
  refcount : Nat := 1
  gen : Nat := 0
  loopCheckDepth : Nat := 0
  busyPollUsecs : Nat := 0
  user : UserId := .root
  file : Option FileId := none
  deriving Repr, BEq

/-- A signal set of one word (`_NSIG_WORDS == 1`): bit `sig - 1`. -/
abbrev SigSet := UInt64

def sigmask (sig : Nat) : SigSet := (1 : UInt64) <<< (sig - 1).toUInt64
def sigismember (s : SigSet) (sig : Nat) : Bool := s &&& sigmask sig != 0
def sigaddset (s : SigSet) (sig : Nat) : SigSet := s ||| sigmask sig

/-- The caller's buffer as an `iov_iter` (`iov_iter_ubuf`): `count` is
    `iov_iter_count`. -/
structure IovIter where
  bytes : ByteArray
  pos : Nat := 0

def IovIter.count (i : IovIter) : Nat := i.bytes.size - i.pos

/-- `struct fdtable`: the `fd[]` array and the `open_fds`/`close_on_exec`
    bitmaps, each of length `max_fds`. `full_fds_bits` is derived from
    `openFds` (see `fullWord`). Every access is bounds-checked; the C never
    indexes past `max_fds`, so an out-of-range index is a mirror invariant
    failure. -/
structure Fdtable where
  maxFds : Nat
  fd : Array (Option FileId)
  openFds : Array Bool
  closeOnExec : Array Bool
  deriving Repr, BEq

/-- `struct files_struct`. `count` is the number of tasks sharing it. -/
structure FilesStruct where
  count : Nat
  resizeInProgress : Bool
  nextFd : Nat
  fdt : Fdtable
  /-- Identity of the `files->fdt` table; `expand_fdtable` would replace it. -/
  fdtGeneration : Nat := 0
  deriving BEq

/-! ## seccomp: the shared names (docs/2026-10-12-seccomp-design.md, 4.1)

The interface commit's data: the classic and translated programs (the
functions over them are stream U's, `Leanux/Seccomp/Classic.lean` and
`Translate.lean`), the filter and the task's seccomp state (stream V's
functions, `Leanux/Seccomp/Filter.lean`), and the child task of a child
probe with the `current` selector. The five operations on the wire
(`harness/trace.py`, design 6.1): `seccomp_install` 30, `seccomp_probe` 31,
`seccomp_prctl` 32, `seccomp_capdrop` 33, `seccomp_query` 34; their
constructors are the runner's (stream V). -/

/-- `struct sock_filter` (include/uapi/linux/filter.h:24-29). -/
structure SockFilter where
  code : UInt16
  jt : UInt8
  jf : UInt8
  k : UInt32
  deriving Repr, BEq, DecidableEq

/-- A classic program as the user passed it (`sock_fprog.filter`, `len` is
    the array's size). -/
abbrev ClassicProg := Array SockFilter

/-- `struct bpf_insn` (include/uapi/linux/bpf.h:72-78): the 8-byte eBPF
    instruction, `dst_reg` and `src_reg` the two 4-bit fields. -/
structure BpfInsn where
  code : UInt8
  dst : UInt8
  src : UInt8
  off : Int16
  imm : Int32
  deriving Repr, BEq, DecidableEq

/-- The translated program (design 4.3): `bpf_prog.insnsi` and `len`, and
    `aux->stack_depth` as the conversion leaves it. -/
structure BpfProg where
  insns : Array BpfInsn := #[]
  stackDepth : Nat := 0
  len : Nat := 0
  deriving Repr, BEq

/-- A filter's allocation identity (the `sfilter` record of
    `AllocSite.kzallocSfilter`), the key of `Kernel.seccompFilters`. -/
abbrev FilterId := Nat

/-- `seccomp.mode`: `SECCOMP_MODE_DISABLED`, `_STRICT`, `_FILTER`, and
    `SECCOMP_MODE_DEAD` (kernel/seccomp.c:52). -/
inductive SeccompMode where
  | disabled | strict | filter | dead
  deriving Repr, BEq, DecidableEq

/-- `__NR_syscalls` of x86-64 in 6.12.110 (`mseal` 462 is the last entry):
    the width of `action_cache.allow_native`. -/
def NR_syscalls : Nat := 463

/-- `struct seccomp_filter` (kernel/seccomp.c:192-241) on the modelled
    paths: the refcounts, the flags, the cache, the chain and the two
    programs. The notifier, lock and wait-queue fields are not mirrored
    (design 9.2). -/
structure SeccompFilter where
  id : FilterId
  /-- `refcount_t refs` and `users`. -/
  refs : Nat := 1
  users : Nat := 1
  log : Bool := false
  waitKillableRecv : Bool := false
  /-- `cache.allow_native`: bit `nr` set when the chain is constantly
      `ALLOW` for `nr` (`seccomp_cache_prepare`). -/
  allowNative : BitVec NR_syscalls := 0
  /-- `prev`, the chain towards the first installed filter. -/
  prev : Option FilterId := none
  /-- `prog`, the translated program (4.3). -/
  prog : BpfProg := {}
  /-- `prog->orig_prog`, the user's program as copied. -/
  origProg : ClassicProg := #[]
  deriving Repr, BEq

/-- `struct seccomp` (include/linux/seccomp.h): `mode`, `filter_count` and
    the head of the chain. -/
structure SeccompState where
  mode : SeccompMode := .disabled
  filterCount : Nat := 0
  filter : Option FilterId := none
  deriving Repr, BEq

/-- `sighand->action[SIGSYS - 1]` as the seccomp paths read it: the guest's
    handler (`SA_SIGINFO`, installed at setup), the default, or the default
    made immutable by `force_sig_info_to_task`'s `HANDLER_EXIT` arm. -/
inductive SigDisposition where
  | handler | dfl | dflImmutable
  deriving Repr, BEq, DecidableEq

/-- Which task a kernel path targets (design 4.1): the trace process
    (`Kernel.task`) or the sandboxed child of a child probe
    (`Kernel.child`), which exists only while the probe's steps run. -/
inductive TaskRef where
  | task | child
  deriving Repr, BEq, DecidableEq

/-- The parts of `struct task_struct` on these paths. `taskWorks` is the
    `task_work` list (deferred `____fput`), run on return to user mode. -/
structure Task where
  files : FilesStruct
  rlimitNofile : Nat
  taskWorks : List FileId := []
  inEventfd : Bool := false
  isKthread : Bool := false
  /-- `task_work_add` fails once the task has run `exit_task_work`. -/
  exited : Bool := false
  /-- `t->blocked` and `t->pending.signal`. Shape deviation (P design
      section 2): `t->pending` is the set plus a `sigqueue` list; only the
      set is mirrored (`legacy_queue` tests it, nothing dequeues). -/
  blocked : SigSet := 0
  pending : SigSet := 0
  /-- seccomp (design 4.1): `current->seccomp`; `task_no_new_privs`;
      `CAP_SYS_ADMIN` in the effective set (root with every capability at
      trace start); the `SIGSYS` disposition; `TIF_SIGPENDING`. -/
  seccomp : SeccompState := {}
  noNewPrivs : Bool := false
  capSysAdmin : Bool := true
  sigsys : SigDisposition := .handler
  sigpending : Bool := false
  deriving BEq

/-- `wg_ratelimiter`'s statics (drivers/net/wireguard/ratelimiter.c:12-18):
    `init_refcnt` and the hsiphash `key` (zeros while unknown: drawn before
    the trace for the fixture's wg0). The tables hold no entries on the
    modeled paths (an entry is made only under load, E's domain). -/
structure Ratelimiter where
  refcnt : Nat := 0
  key : List UInt8 := List.replicate 16 0
  /-- E-B arm C (docs/2026-10-05-e-dos.md §6.C): the token-bucket table, keyed by
      source IP (the `(net, ip)` hash is a cut, and there is one netns per
      trace): `(ip, tokens, last_time_ns)` per entry. The GC that would free
      stale entries arms a timer (D3); its firing is out of scope on this base
      (no timer source here), so entries persist for the trace. -/
  table : List (Nat × Int × Int) := []
  /-- `table_v6` (ratelimiter.c:23, :100-106): the IPv6 entries, keyed by the
      source /64 (the first eight bytes of the address, `memcpy(&ip, &saddr, 8)`),
      the same bucket algorithm; modelled 2026-10-14 (the receive audit's F12). -/
  table6 : List (Nat × Int × Int) := []
  deriving Repr, BEq

/-- Whole-kernel mirror state. `nrFiles`/`maxFiles` mirror the system-wide
    `nr_files` percpu counter and `files_stat.max_files`, and
    `anonInodeInodeErr` whether the boot-time `anon_inode_inode` is an error
    pointer; the runner supplies these environment facts. -/
structure Kernel where
  task : Task
  files : TreeMap FileId File
  nextFile : FileId
  ctxs : TreeMap CtxId EventfdCtx
  nextCtx : CtxId
  /-- `eventfd_ida`: the allocated ids. -/
  idaUsed : TreeSet Nat
  nrFiles : Nat
  maxFiles : Nat
  anonInodeInodeErr : Bool
  /-- The fixture's WireGuard device, in traces that use the network fixture. -/
  wg : Option WG.Device := none
  /-- W2 (docs/2026-10-06-w1-w2-netlink.md, 4.3): the dump state of the
      fixture's generic-netlink socket (fd 7, `wg_get`) and of the stepped
      dump socket (fd 8, `wg_get_start`/`wg_get_recv`). -/
  nlSock7 : WG.NlSock := {}
  nlSock8 : WG.NlSock := {}
  /-- `peer_counter` (drivers/net/wireguard/peer.c), a global atomic. -/
  peerCounter : Nat := 0
  /-- `keypair_counter` (drivers/net/wireguard/noise.c), a global atomic. -/
  keypairCounter : Nat := 0
  /-- L: the network namespace's ifindex cursor (`net->ifindex`, the
      `xa_alloc_cyclic` cursor of `dev_by_index`, never reset): the next
      device registered gets this index. -/
  netIfindexNext : Nat := 4
  /-- L: the ratelimiter's global singleton (ratelimiter.c:12-18). -/
  ratelimiter : Ratelimiter := {}
  /-- Pipes (P): the pipefs inodes, the `pipe_inode_info`s and their data
      pages, each an owned store with its next identity. -/
  inodes : TreeMap PipefsInodeId Inode := {}
  nextInode : PipefsInodeId := 0
  /-- The inode-allocation cut's mirror-local `i_ino` counter (`get_next_ino`
      has an unknown boot baseline; `i_ino` is unobserved in stage 1). -/
  lastIno : Nat := 0
  pipes : TreeMap PipeId PipeInodeInfo := {}
  nextPipe : PipeId := 0
  pages : TreeMap PageId Page := {}
  nextPage : PageId := 0
  /-- `root_user`; `pipe_bufs` is tracked from a baseline of 0 (section 5). -/
  user : UserStruct := {}
  /-- sysctl defaults (fs/pipe.c:54, 59-60), never written by traces. -/
  pipeMaxSize : Nat := 1048576
  pipeUserPagesSoft : Nat := 16384
  pipeUserPagesHard : Nat := 0
  /-- seccomp (design 4.1): every filter any task holds, by allocation
      identity (the chain runs through `prev`); the sandboxed child of a
      child probe, created from `task` by `copy_seccomp`'s effects and
      dropped at the parent's `wait4`; and `current`, the task the runner
      is executing (the child only while a child probe's steps run). -/
  seccompFilters : TreeMap FilterId SeccompFilter := {}
  child : Option Task := none
  current : TaskRef := .task
  /-- The next filter's allocation identity (stream V): monotone, never reused. -/
  nextFilter : FilterId := 0
  /-- epoll (design 4.1): the `struct eventpoll`, `epitem` and `eppoll_entry`
      stores, each with its next identity (lifetime identities: never
      reused). -/
  eps : TreeMap EpId Eventpoll := {}
  nextEp : EpId := 0
  epis : TreeMap EpiId Epitem := {}
  nextEpi : EpiId := 0
  pwqs : TreeMap PwqId EppollEntry := {}
  nextPwq : PwqId := 0
  /-- fs/eventpoll.c's statics: `loop_check_gen` (:394) relative to the
      boot's unknown base (`Env.LOOP_CHECK_GEN_BASE`, design 3.5),
      `inserting_into` (:397), `tfile_check_list` (:415: the listed heads'
      files, newest first, each holding one `f_count` reference) and
      `path_count` (:1603). `max_user_watches` (:389) is the fixture
      constant `Env.MAX_USER_WATCHES`, set by the runner. -/
  loopCheckGen : Nat := 0
  insertingInto : Option EpId := none
  tfileCheckList : List FileId := []
  pathCount : Array Nat := #[0, 0, 0, 0, 0]
  maxUserWatches : Nat := 0
  /-- The `epi` field of the `ep_pqueue` of an `ep_insert` in progress
      (:1833, :1865): `ep_ptable_queue_proc` reads it and clears it when its
      `pwq` allocation fails (:1551-1553), which `ep_insert` tests (:1877). -/
  epqEpi : Option EpiId := none
  /-- B3 (docs/2026-10-15-design-b3-timer-wheel.md, section 3.1): the timer
      base's clock (`timer_bases[0].clk`, kernel/time/timer.c:251-266) as
      last recorded at an arm (kind 313), kept for the check that the base
      never rewinds (`__forward_timer_base`, :994-1016); `none` before the
      first arm. -/
  timerClk : Option UInt64 := none
  /-- B3: the enqueue stamp counter (`enqueue_timer`, timer.c:655-680): each
      enqueue takes the next stamp, which orders a slot's list (newest first,
      `hlist_add_head`, :659). -/
  timerEnqueues : Nat := 0
  deriving BEq

/-! ## Allocation outcomes (docs/2026-10-05-a-alloc.md, section 6)

An allocation's outcome is a hidden choice like a random draw: the patched
kernel records it (kind 305, 40 bytes; word 0's low byte is the outcome, 1 ok
or 0 NULL; the rest is attribution) at the two allocator entry functions,
with the consumer's unwound call chain, when the run armed the allocation
ranges that contain it. One site per consumer frame. How the mirror consumes
a site's records (section 6.2): -/

/-- The environment oracle, for the pipe paths' remaining sites only (P,
    design section 5): every site succeeds (`harnessEnv`). A's sites (the
    FS slice, WireGuard and, since the D3+A integration, three direct pipe
    allocations) are allocation outcomes (`AllocSite`, `hiddenAlloc`)
    and the eventfd/pipe2 usercopies trace inputs (A, section 6.5). Left
    here: the inode-allocation cut and the resize kcalloc (see
    `AllocSite.kzallocPipeInfo`'s note), the page usercopies and
    `__sigqueue_alloc`. -/
inductive EnvSite where
  -- L: wg_newlink's allocations (device.c:325-367); `register_netdevice`
  -- (A's domain: assumed success in the harness). wg_ratelimiter_init's
  -- (ratelimiter.c:164-185) are constant-outcome decisions since B4
  -- (`ratelimiterInit`): creation allocations outside the model
  | pubkeyHashtableAlloc | indexHashtableAlloc | allocWorkqueue | packetQueueInit
  | registerNetdevice
  -- P (pipes, design section 5). `allocInode` is the inode-allocation cut:
  -- new_inode_pseudo -> alloc_inode -> alloc_inode_sb, inode_init_always_gfp
  -- and get_next_ino, no decisions (audit M3)
  | allocInode | kcallocResizeBufs
  | copyPageToIter | copyPageFromIter | sigqueueAlloc
  -- W4: skb_gso_segment's allocations inside skb_segment (device.c:179), an
  -- assumed-success site as the sites above (A's domain)
  | skbSegment
  deriving Repr, BEq, DecidableEq

inductive AllocCount where
  /-- `n` records per successful consultation, in order; a failed record
      ends the consultation (an `__alloc_skb` site: the `sk_buff`, then the
      data buffer, so 2 on success and 1 when the `sk_buff` fails). -/
  | exact (n : Nat)
  /-- A lax site whose count A0 fixed at 0 on this fixture (section 16.2.3):
      the outcome is constantly ok and no record is consumed, so a record of
      the site is never consumed and fails the run (unconsumed, or met at
      the next read). -/
  | laxZero
  /-- A below-cut consumer of an armed helper range (section 16.2.4): its
      records are consumed at the cut point that contains it (`skipCut`),
      any number; a failed one is `unsupported`. -/
  | cut
  /-- seccomp (docs/2026-10-12-seccomp-design.md, section 3.1): a site the
      hook never records by construction (the allocator is reached from
      inside `mm/vmalloc.c`, or is the percpu allocator, so the range test
      sees no armed frame). Assumed ok; consumes nothing; a record of it
      would be left over and fail the run. Its `-ENOMEM` arm is modelled but
      unexercised (design section 9.3). -/
  | unrecorded
  deriving Repr, BEq, DecidableEq

inductive AllocSite where
  -- FS slice (class b-task: not steered, Q1)
  | kmallocEventfdCtx | filpAlloc | dAllocPseudo | kmallocFdtable | kvmallocFdArray | kvmallocFdBitmaps
  -- WireGuard control plane (b-task), and noise.c:100 (b-kworker: record-only)
  | kmemCacheZallocPeer | allocNode190 | allocNode205 | allocNode234 | kzallocKeypair
  -- the GFP_ATOMIC alloc_skb sites (class a: steerable [USER A1])
  | sendBufSkb | replySkb | keepaliveSkb
  -- D2's lax sites, count 0 on this fixture (A0)
  | skbCowHead | skbChecksumHelp | skbCowDataTx | skbCowDataRx
  -- below-cut consumers of the `__alloc_skb`/`kmalloc_reserve` ranges
  | nlmsgNew | netlinkAllocLargeSkb | sockAllocSendPskb | netlinkDump | netlinkTrim
  -- below-cut consumer of the dentry cache's range: the last device's delete
  | dAllocSlabDebugfs
  -- below-cut consumer of the `__alloc_skb` range: the net device's uevents
  | allocUeventSkb
  -- below-cut consumer of the `__alloc_skb`/`kmalloc_reserve` ranges: the
  -- stack's own replies built with ip_append_data (W6's TCP RST)
  | ipAppendDataSkb
  -- below-cut consumers of the kvmalloc range: a net device's creation
  -- (alloc_netdev_mqs, its tx and rx queue arrays, WireGuard's ptr rings)
  | netdevAlloc | netdevTxQueues | netdevRxQueues | ptrRingInit
  -- the pipe paths' direct sites (b-task; A section 19.6, integration)
  | kzallocPipeInfo | kcallocPipeBufs | allocPipePage
  -- seccomp (docs/2026-10-12-seccomp-design.md, section 3.1; the interface
  -- commit): one install's sites in the C's order, indices 28-38, hidden-site
  -- ids 400-410 (`AllocSite.hiddenId`)
  | kzallocSfilter | vmallocBpfProg | kzallocBpfAux | percpuBpfActive | percpuBpfStats
  | kmallocOrigFprog | kmemdupOrigFilter | kmallocArrayMasks | kmemdupOldProg | vmallocBpfProgRealloc
  | kcallocAddrs
  -- epoll (docs/2026-10-12-epoll-design.md, 3.1; b-task): the four consumer
  -- frames of fs/eventpoll.c
  | kzallocEp | kmemCacheZallocEpi | kmemCacheAllocPwq | kmemCacheZallocEphead
  -- B4 (docs/2026-10-15-design-b4-load-ratelimiter.md, 4.3): the
  -- ratelimiter entry, wg_ratelimiter_allow's kmem_cache_alloc
  -- (ratelimiter.c:138) in the handshake receive worker; index 69, id 139
  | kmemCacheAllocRlEntry
  deriving Repr, BEq, DecidableEq

structure AllocSiteInfo where
  index : Nat
  /-- The label, as harness/steer.py `ALLOC_SITES` names the site. -/
  label : String
  file : String
  line : Nat
  count : AllocCount

def AllocSite.info : AllocSite → AllocSiteInfo
  | .kmallocEventfdCtx => ⟨0, "kmallocEventfdCtx", "fs/eventfd.c", 393, .exact 1⟩
  | .filpAlloc => ⟨1, "filpAlloc", "fs/file_table.c", 232, .exact 1⟩
  | .dAllocPseudo => ⟨2, "dAllocPseudo", "fs/file_table.c", 374, .exact 1⟩
  -- A0 (section 16.2.2): the fd-table frames are file.c:147/151/156 in 6.12.110
  | .kmallocFdtable => ⟨3, "kmallocFdtable", "fs/file.c", 147, .exact 1⟩
  | .kvmallocFdArray => ⟨4, "kvmallocFdArray", "fs/file.c", 151, .exact 1⟩
  | .kvmallocFdBitmaps => ⟨5, "kvmallocFdBitmaps", "fs/file.c", 156, .exact 1⟩
  | .kmemCacheZallocPeer => ⟨6, "kmemCacheZallocPeer", "drivers/net/wireguard/peer.c", 33, .exact 1⟩
  | .allocNode190 => ⟨7, "allocNode190", "drivers/net/wireguard/allowedips.c", 190, .exact 1⟩
  | .allocNode205 => ⟨8, "allocNode205", "drivers/net/wireguard/allowedips.c", 205, .exact 1⟩
  | .allocNode234 => ⟨9, "allocNode234", "drivers/net/wireguard/allowedips.c", 234, .exact 1⟩
  | .kzallocKeypair => ⟨10, "kzallocKeypair", "drivers/net/wireguard/noise.c", 100, .exact 1⟩
  | .sendBufSkb => ⟨11, "sendBufSkb", "drivers/net/wireguard/socket.c", 192, .exact 2⟩
  | .replySkb => ⟨12, "replySkb", "drivers/net/wireguard/socket.c", 217, .exact 2⟩
  | .keepaliveSkb => ⟨13, "keepaliveSkb", "drivers/net/wireguard/send.c", 226, .exact 2⟩
  | .skbCowHead => ⟨14, "skbCowHead", "drivers/net/wireguard/send.c", 183, .laxZero⟩
  | .skbChecksumHelp => ⟨15, "skbChecksumHelp", "drivers/net/wireguard/send.c", 188, .laxZero⟩
  | .skbCowDataTx => ⟨16, "skbCowDataTx", "drivers/net/wireguard/send.c", 192, .laxZero⟩
  | .skbCowDataRx => ⟨17, "skbCowDataRx", "drivers/net/wireguard/receive.c", 268, .laxZero⟩
  -- nlmsg_new (the netlink ack and rtnetlink notifications)
  | .nlmsgNew => ⟨18, "nlmsgNew", "include/net/netlink.h", 1015, .cut⟩
  -- netlink_alloc_large_skb: the request skb in netlink_sendmsg
  | .netlinkAllocLargeSkb => ⟨19, "netlinkAllocLargeSkb", "net/netlink/af_netlink.c", 1180, .cut⟩
  -- sock_alloc_send_pskb: the fixture's sendto, and ICMP via ip_append_data
  | .sockAllocSendPskb => ⟨20, "sockAllocSendPskb", "net/core/sock.c", 2930, .cut⟩
  -- netlink_dump's skb: alloc_skb(alloc_min_size, GFP_KERNEL) at :2290. The
  -- no-reclaim attempt at :2284 needs max_recvmsg_len above alloc_min_size
  -- (NLMSG_GOODSIZE, 3776), and every netlink receive of the guest is exactly
  -- 3776 bytes (W2's guest step, NL_RECV_LEN), so no modeled path takes it
  -- [AGENT 2026-10-12, the coordinator's decision: the mirror follows the
  -- guest step; docs/2026-10-06-w1-w2-netlink.md 9.5].
  | .netlinkDump => ⟨21, "netlinkDump", "net/netlink/af_netlink.c", 2290, .cut⟩
  -- netlink_trim's pskb_expand_head (its kmalloc_reserve is in the range)
  | .netlinkTrim => ⟨22, "netlinkTrim", "net/netlink/af_netlink.c", 1294, .cut⟩
  -- Pipes (A section 19.6; D3+A integration [AGENT]): direct calls, one
  -- record per consultation. alloc_pipe_info's kzalloc (pipe.c:798) and
  -- kcalloc of the buffers (:815); pipe_write's alloc_page, consulted only
  -- when `tmp_page` is NULL (:513, through __alloc_pages_noprof). Not
  -- sites: get_pipe_inode's new_inode_pseudo (:882), as arming alloc_inode
  -- would also record WireGuard's in-window sock_alloc, a consumer this
  -- table does not declare; pipe_resize_ring's kcalloc (:1271), as above
  -- KMALLOC_MAX_CACHE_SIZE (more than 204 slots) it is a large kmalloc whose
  -- page allocation is not recorded at this frame (its count depends on
  -- the size).
  | .kzallocPipeInfo => ⟨23, "kzallocPipeInfo", "fs/pipe.c", 798, .exact 1⟩
  | .kcallocPipeBufs => ⟨24, "kcallocPipeBufs", "fs/pipe.c", 815, .exact 1⟩
  | .allocPipePage => ⟨25, "allocPipePage", "fs/pipe.c", 513, .exact 1⟩
  -- The last WireGuard device's wg_destruct -> wg_ratelimiter_uninit ->
  -- kmem_cache_destroy(entry_cache) -> debugfs_slab_release ->
  -- debugfs_lookup_and_remove -> lookup_slow -> d_alloc_parallel: the cache's
  -- (negative) dentry under /sys/kernel/debug/slab, allocated by __lookup_slow
  -- (namei.c:1730) when the dentry cache's range is armed. Consumed at
  -- `WG.ratelimiterUninit` (a cut: recorded only when a chunk arms the range).
  | .dAllocSlabDebugfs => ⟨26, "dAllocSlabDebugfs", "fs/namei.c", 1730, .cut⟩
  -- kobject_uevent_env -> alloc_uevent_skb (kobject_uevent.c:289): the
  -- KOBJ_ADD uevents of netdev_register_kobject (the device and its queues)
  -- at register_netdevice, before NETDEV_REGISTER's neighbour draws, and the
  -- KOBJ_REMOVE ones of netdev_unregister_kobject at the unregister, before
  -- wg_destruct; consumed at wgNewlink's register cut and wgDelete's
  -- unregister cut when a chunk arms __alloc_skb [AGENT 2026-10-12].
  | .allocUeventSkb => ⟨27, "allocUeventSkb", "lib/kobject_uevent.c", 289, .cut⟩
  -- __ip_append_data's alloc_skb (ip_output.c:1138) under ip_send_unicast_reply:
  -- the skb and its data (two kind-305 records) of the TCP RST the stack sends
  -- for an inner segment to wg0's address (W6, 2.4.1), before the reply
  -- re-enters wg_xmit; consumed at `Env.Stack.reply4`'s cut when a chunk arms
  -- the ranges (a chunk holding alloc traces and a stack_rst4 trace, 2026-10-12)
  -- [AGENT, wgen].
  | .ipAppendDataSkb => ⟨28, "ipAppendDataSkb", "net/ipv4/ip_output.c", 1138, .cut⟩
  -- wg_create (rtnl_newlink_create -> alloc_netdev_mqs, dev.c:11245) and
  -- register_netdevice's queue arrays (netif_alloc_netdev_queues dev.c:10419,
  -- netif_alloc_rx_queues dev.c:10352), and wg_newlink's ptr_ring_init
  -- (include/linux/ptr_ring.h:471): kvmalloc records when a chunk arms that
  -- range (an fd-array trace beside a lifecycle trace, 2026-10-12), consumed
  -- at wgNewlink's register cut. The indices skip the hidden ids the timer
  -- sections hold (100-117): 70 + index must stay unique [AGENT, wgen].
  | .netdevAlloc => ⟨29, "netdevAlloc", "net/core/dev.c", 11245, .cut⟩
  | .netdevTxQueues => ⟨48, "netdevTxQueues", "net/core/dev.c", 10419, .cut⟩
  | .netdevRxQueues => ⟨49, "netdevRxQueues", "net/core/dev.c", 10352, .cut⟩
  | .ptrRingInit => ⟨57, "ptrRingInit", "include/linux/ptr_ring.h", 471, .cut⟩
  -- seccomp (design section 3.1; indices 58-68, since 28-57 hold A's and
  -- wgen's `70 + index` ids, see AllocSite.hiddenId), one install in order: seccomp_prepare_filter's
  -- kzalloc (seccomp.c:688); bpf_prog_alloc_no_stats's __vmalloc (core.c:105,
  -- unrecorded: reached from mm/vmalloc.c), kzalloc of aux (:109) and
  -- alloc_percpu_gfp of active (:114, unrecorded: percpu); bpf_prog_alloc's
  -- alloc_percpu_gfp of stats (:151, unrecorded); bpf_prog_store_orig_filter's
  -- kmalloc (filter.c:1156) and kmemdup (:1163); check_load_and_stores's
  -- kmalloc_array of masks (:935); bpf_migrate_filter's kmemdup_array
  -- (:1277); bpf_prog_realloc's __vmalloc (core.c:260, unrecorded, below the
  -- cut); bpf_convert_filter's second-pass kcalloc of addrs (filter.c:594).
  | .kzallocSfilter => ⟨58, "kzallocSfilter", "kernel/seccomp.c", 688, .exact 1⟩
  | .vmallocBpfProg => ⟨59, "vmallocBpfProg", "kernel/bpf/core.c", 105, .unrecorded⟩
  | .kzallocBpfAux => ⟨60, "kzallocBpfAux", "kernel/bpf/core.c", 109, .exact 1⟩
  | .percpuBpfActive => ⟨61, "percpuBpfActive", "kernel/bpf/core.c", 114, .unrecorded⟩
  | .percpuBpfStats => ⟨62, "percpuBpfStats", "kernel/bpf/core.c", 151, .unrecorded⟩
  | .kmallocOrigFprog => ⟨63, "kmallocOrigFprog", "net/core/filter.c", 1156, .exact 1⟩
  | .kmemdupOrigFilter => ⟨64, "kmemdupOrigFilter", "net/core/filter.c", 1163, .exact 1⟩
  | .kmallocArrayMasks => ⟨65, "kmallocArrayMasks", "net/core/filter.c", 935, .exact 1⟩
  | .kmemdupOldProg => ⟨66, "kmemdupOldProg", "net/core/filter.c", 1277, .exact 1⟩
  | .vmallocBpfProgRealloc => ⟨67, "vmallocBpfProgRealloc", "kernel/bpf/core.c", 260, .unrecorded⟩
  | .kcallocAddrs => ⟨68, "kcallocAddrs", "net/core/filter.c", 594, .exact 1⟩
  -- epoll (design 3.1), direct calls, one record per consultation:
  -- ep_alloc's kzalloc (:1331), ep_alloc_epitem's kmem_cache_zalloc (:1764),
  -- ep_ptable_queue_proc's kmem_cache_alloc (:1550), ep_attach_file's
  -- kmem_cache_zalloc (:1722). Their site ids are 192-195 of epoll's block
  -- (docs/2026-10-11-interface.md): indices 122-125 under the 70 + index rule
  -- [merge of the representation batch, stream T 2026-10-13].
  | .kzallocEp => ⟨122, "kzallocEp", "fs/eventpoll.c", 1331, .exact 1⟩
  | .kmemCacheZallocEpi => ⟨123, "kmemCacheZallocEpi", "fs/eventpoll.c", 1764, .exact 1⟩
  | .kmemCacheAllocPwq => ⟨124, "kmemCacheAllocPwq", "fs/eventpoll.c", 1550, .exact 1⟩
  | .kmemCacheZallocEphead => ⟨125, "kmemCacheZallocEphead", "fs/eventpoll.c", 1722, .exact 1⟩
  -- B4: a direct site in the receive worker (kworker context, record-only:
  -- the class is not steerable); index 69 is the first after seccomp's
  -- 58-68 whose id, 139, is free
  | .kmemCacheAllocRlEntry => ⟨69, "kmemCacheAllocRlEntry", "drivers/net/wireguard/ratelimiter.c", 138, .exact 1⟩

def AllocSite.all : List AllocSite :=
  [.kmallocEventfdCtx, .filpAlloc, .dAllocPseudo, .kmallocFdtable, .kvmallocFdArray, .kvmallocFdBitmaps,
   .kmemCacheZallocPeer, .allocNode190, .allocNode205, .allocNode234, .kzallocKeypair,
   .sendBufSkb, .replySkb, .keepaliveSkb, .skbCowHead, .skbChecksumHelp, .skbCowDataTx, .skbCowDataRx,
   .nlmsgNew, .netlinkAllocLargeSkb, .sockAllocSendPskb, .netlinkDump, .netlinkTrim,
   .kzallocPipeInfo, .kcallocPipeBufs, .allocPipePage, .dAllocSlabDebugfs, .allocUeventSkb, .ipAppendDataSkb,
   .netdevAlloc, .netdevTxQueues, .netdevRxQueues, .ptrRingInit,
   .kzallocSfilter, .vmallocBpfProg, .kzallocBpfAux, .percpuBpfActive, .percpuBpfStats,
   .kmallocOrigFprog, .kmemdupOrigFilter, .kmallocArrayMasks, .kmemdupOldProg, .vmallocBpfProgRealloc,
   .kcallocAddrs,
   .kzallocEp, .kmemCacheZallocEpi, .kmemCacheAllocPwq, .kmemCacheZallocEphead,
   .kmemCacheAllocRlEntry]

/-- An allocation site's hidden-site id: A's block 70-99 by index
    (docs/2026-10-05-a-alloc.md, section 6.1) and `70 + index` above it
    (wgen's 48, 49, 57: ids 118, 119, 127, clear of the timer sections'
    100-117; epoll's 122-125: ids 192-195 of its block); seccomp's sites,
    indices 58-68, take 400 + (index - 58), in seccomp's block 400-419
    (docs/2026-10-11-interface.md; 200-219 would meet `Worker.sectionId`'s
    ids from index 15) [AGENT, seccomp X merges]; B4's ratelimiter entry,
    index 69, takes id 139 under the `70 + index` rule. -/
def AllocSite.hiddenId (s : AllocSite) : Nat :=
  let i := s.info.index
  if 58 ≤ i ∧ i ≤ 68 then 400 + (i - 58) else 70 + i

/-- The below-cut allocation consumers (consumed at cut points). -/
def AllocSite.cuts : List AllocSite := AllocSite.all.filter (·.info.count == .cut)

/-! ## Choices (docs/2026-10-03-choice-stream-strategy.md)

A value the C consumes that the trace does not determine (a random draw, a
clock read) is recorded by the patched kernel at a generic interception point
(`kcov_choice_ip`, in the RNG entry points and the clock readers), with the
consumer's call site. The check maps each record to a site of this table by
the consumer frame of its symbolized call chain, orders records by their
sequence number, and passes them to the mirror, which consumes them in order:
- a **mirror** site is consumed exactly where the C consumes it;
- a **cut** site is consumed below the mirror's cut, at a declared cut point
  (`skipCut`), and its value is discarded; how many such records a cut
  produces is not checked (e.g. `ip_idents_reserve` draws only when `jiffies`
  moved), which is weaker than the mirror sites' check;
- an **ambient** site is consumed by code the mirror does not model at all
  (the scheduler), wherever it occurs. -/

/-- A deferred unit the kernel dispatches in a KCOV section (D1 sprint,
    stream 1): the work item's, softirq's or (D3) timer callback's function.
    `Worker.index` is the function's position in `harness/linux.py`
    `DISPATCH_SYMBOLS`. -/
inductive Worker where
  | sendWorker | receiveWorker | encryptWorker | txWorker | netRx | decryptWorker
  /-- D3 (docs/2026-10-05-d3-timers.md, sections 3.1 and 5.2): the five
      timer callbacks, each run by `call_timer_fn` in `TIMER_SOFTIRQ`, and
      the zero-key work item (`clear_peer_work` on `handshake_send_wq`). -/
  | timerRetransmit | timerSendKeepalive | timerNewHandshake | timerZeroKey | clearPeerWorker
  | timerPersistentKeepalive
  /-- W8 (docs/2026-10-06-w8-w9-netns-routing.md, section 3.2): the creating
      namespace's teardown (`cleanup_net` on `netns_wq`, armed by a
      foreign-creator trace) and the linkwatch run its `netif_carrier_off`
      queues (`linkwatch_event` on `system_unbound_wq`; W8b, armed by no
      trace yet). -/
  | netnsCleanup | linkwatch
  -- Reserved for the W streams (the interface commit,
  -- docs/2026-10-11-interface.md): W8-W9's `cleanup_net` and
  -- `linkwatch_event` units at indices 12-13, W5-W6's two units at 14-15
  -- (`Worker.sectionId` gives 114-119 and 200-201). A stream appends its
  -- constructors in its own block here and in `symbol`, `index`, `all`,
  -- `timer?`, `resched?`, and its symbols to `harness/linux.py`
  -- `DISPATCH_SYMBOLS` in the same order.
  deriving Repr, BEq, DecidableEq

def Worker.symbol : Worker → String
  | .sendWorker => "wg_packet_handshake_send_worker"
  | .receiveWorker => "wg_packet_handshake_receive_worker"
  | .encryptWorker => "wg_packet_encrypt_worker"
  | .txWorker => "wg_packet_tx_worker"
  | .netRx => "net_rx_action"
  | .decryptWorker => "wg_packet_decrypt_worker"
  | .timerRetransmit => "wg_expired_retransmit_handshake"
  | .timerSendKeepalive => "wg_expired_send_keepalive"
  | .timerNewHandshake => "wg_expired_new_handshake"
  | .timerZeroKey => "wg_expired_zero_key_material"
  | .clearPeerWorker => "wg_queued_expired_zero_key_material"
  | .timerPersistentKeepalive => "wg_expired_send_persistent_keepalive"
  | .netnsCleanup => "cleanup_net"
  | .linkwatch => "linkwatch_event"

def Worker.index : Worker → Nat
  | .sendWorker => 0 | .receiveWorker => 1 | .encryptWorker => 2 | .txWorker => 3 | .netRx => 4
  | .decryptWorker => 5
  | .timerRetransmit => 6 | .timerSendKeepalive => 7 | .timerNewHandshake => 8 | .timerZeroKey => 9
  | .clearPeerWorker => 10 | .timerPersistentKeepalive => 11
  | .netnsCleanup => 12 | .linkwatch => 13

def Worker.all : List Worker :=
  [.sendWorker, .receiveWorker, .encryptWorker, .txWorker, .netRx, .decryptWorker,
   .timerRetransmit, .timerSendKeepalive, .timerNewHandshake, .timerZeroKey, .clearPeerWorker,
   .timerPersistentKeepalive, .netnsCleanup, .linkwatch]

/-- D3: the timer callbacks (sections opened by `call_timer_fn`), with the
    peer timer each runs for. -/
def Worker.timer? : Worker → Option WG.PeerTimer
  | .timerRetransmit => some .retransmitHandshake
  | .timerSendKeepalive => some .sendKeepalive
  | .timerNewHandshake => some .newHandshake
  | .timerZeroKey => some .zeroKeyMaterial
  | .timerPersistentKeepalive => some .persistentKeepalive
  | _ => none

/-- The queued units whose work struct lives in `struct wg_peer`
    (`transmit_handshake_work`, `transmit_packet_work`, `clear_peer_work`):
    their dispatch identity dies with the peer. The others live in
    `struct wg_device` (the device-level units), in the net namespace
    (`cleanup_net`) or nowhere (a softirq, a timer callback). -/
def Worker.perPeer : Worker → Bool
  | .sendWorker | .txWorker | .clearPeerWorker => true
  | _ => false

/-- The queued units whose work struct lives in `struct wg_device` or in a
    peer: both die with the device (`free_netdev`, after `peer_remove_all`). -/
def Worker.deviceOwned : Worker → Bool
  | .netnsCleanup | .linkwatch => false
  | _ => true

inductive HiddenSite where
  | initEphemeral | respEphemeral | tai64nNow | indexDraw
  | resetLastSent | birthdateExpired | initLastSent | initLastSentAgain | respLastSent | respLastSentAgain
  | floodNow | consumptionNow | deriveKeysBirthdate | retransmitJitter
  | walltimeLastHandshake
  | ipIdentReserve | ipIdentKey | icmpCredit | flowHashSecret
  | schedDlTimer
  /-- A dispatch section's start and stop records (kinds 300 and 301): the
      site is the dispatched function; start carries its address, stop the
      count of records dropped in the section. -/
  | sectionStart (w : Worker) | sectionStop (w : Worker)
  /-- A reschedule at a worker's `cond_resched` (kind 302): written only
      when `__cond_resched` is about to schedule, inside a task section. -/
  | reschedReceive | reschedEncrypt | reschedTx
  /-- D2: the decrypt worker's `cond_resched`, and `wg_timers_data_sent`'s
      jitter draw. -/
  | reschedDecrypt | newHandshakeJitter
  /-- D2 stream B: `wg_timers_handshake_complete`'s wall-clock read on key
      confirmation by a data message (its tail jump attributes the record to
      the caller, `wg_packet_consume_data_done`). -/
  | walltimeLastHandshakeData
  /-- D3 (docs/2026-10-05-d3-timers.md, sections 3.3-3.4 and 13.4): the
      kind-303 arm record `{jiffies at mod_timer, expires}` written at
      `mod_timer` for a timer of the dispatch set (consumer `timers.c:37`,
      `mod_peer_timer`, inlined into its seven callers; gated by
      `harness/linux.py` `ARM_RECORDS`), and the kind-304 record
      `{jiffies before, jiffies after}` of the `wg_advance` operation, in
      the trace process's task stream. -/
  | modTimerArm | timeAdvance | jiffiesEnd
  /-- B3 (docs/2026-10-15-design-b3-timer-wheel.md, sections 3.2, 4 and 7):
      the timer wheel's two records at an arm, written by `__mod_timer` for a
      timer of the armed set and resolved at the arming line like the arm
      record: kind 313 `{base->clk, timer}` right after `forward_timer_base`
      on both paths (the hidden input the slot depends on), and kind 314
      `{idx, bucket_expiry, timer}` at the enqueue (the slot and bucket
      expiry the C stored; absent on the same-slot path, so the mirror's own
      same-slot decision is checked by the record's presence). -/
  | timerClk | timerEnqueue
  /-- Pre-release review, finding 2 (docs/2026-10-14-pre-release-review.md,
      section 2): the caller's `jiffies` read that computes a peer timer's
      expiry, recorded as kind 311 `{jiffies}` on the caller's own line in
      timers.c (`kcov_timer_jiffies`, an identity through which each of
      `mod_peer_timer`'s seven callers reads). Consumed before the guard,
      as the C evaluates the argument; `armTimer` computes the expiry from
      it and compares with the arm record's published expiry, so a delay
      wrong by one tick no longer disappears into a reconstructed read.
      One site per caller: ids 420-426. -/
  | timerJiffiesRetransmitZeroKey | timerJiffiesExpiredKeepalive | timerJiffiesDataSent
  | timerJiffiesDataReceived | timerJiffiesHandshakeInitiated | timerJiffiesSessionDerived
  | timerJiffiesTraversal
  /-- Dispatch order (docs/2026-10-11-dispatch-order.md): the kind-307 queue
      record `{work, func}` written at `__queue_work` for a work item of the
      dispatch set; its site is the work function. Consumed where the mirror
      queues the unit, once per `queue_work` whose PENDING test passes
      (`recordQueued`, `queueDeviceWork`); the address names the unit at its
      dispatch (`resolveUnit`). -/
  | queued (w : Worker)
  /-- E-A: `wg_cookie_message_consume`'s birthdate of a stored cookie. -/
  | cookieBirthdate
  /-- L (docs/2026-10-05-l-lifecycle.md, section 3.1): `wg_cookie_checker_init`'s
      clock read and secret (`wg_newlink`), the public-key hashtable's key,
      the ratelimiter's key (first creation) and its GC's clock read (last
      destruction), `udp_lib_get_port`'s draw for a random port, and the two
      `neigh_rand_reach_time` draws of `register_netdevice` (a cut). -/
  | cookieSecretBirthdate | cookieSecret | pubkeyHashKey | ratelimiterKey | ratelimiterGcNow
  | udpPortDraw | neighReachTime
  /-- W2 (id 170): `netlink_autobind`'s random port id (af_netlink.c:820) on
      the stepped dump socket's first `sendmsg`: the process's id is the
      fixture socket's, so the collision draws once below -4096. The port
      id reaches no modeled path (a cut). -/
  | netlinkAutobindPort
  /-- An allocation outcome (kind 305) at a consumer frame: ids 70-99 are
      A's (docs/2026-10-05-a-alloc.md, section 6.1). -/
  | alloc (s : AllocSite)
  /-- seccomp (docs/2026-10-12-seccomp-design.md, section 3.3; id 411 of
      the stream's 400-419): the kind-309 record of the translated program,
      class `program`, one per emitted `bpf_insn` (its eight bytes) and then
      one with the eBPF length, written in `bpf_migrate_filter` after the
      second pass and before `bpf_prog_select_runtime` (net/core/filter.c,
      between :1305 and :1315 of the locked source; stream W's line-preserving
      hook fixes the consumer at :1315). The length record comes first, then
      one per instruction (stream W's measurement); consumed in order at the
      end of the mirror's translation (4.3) through the bridge, which reads
      the length first and holds it in `World.translatedLen`. -/
  | bpfProgInsn
  /-- seccomp, pre-release review finding 11 (id 414 of the stream's 400-419):
      the instruction pointer `populate_seccomp_data` stores (`KSTK_EIP(task)`,
      kernel/seccomp.c:265), one kind-312 record of 8 bytes per
      `__seccomp_filter` entry that builds its own `seccomp_data`, before the
      cache check; class `address` like kind 308 (a value resolved by its
      consumer frame). A filter that loads offsets 8..15 branches on it. -/
  | seccompIp
  /-- seccomp (stream V, measured on stream W's scratch kernel): the two
      clock reads of `copy_process` in the parent's window of a child probe,
      `p->start_time = ktime_get_ns()` at `kernel/fork.c:2532` (kind 206) and
      `p->start_boottime = ktime_get_boottime_ns()` at :2533 (kind 207),
      8 bytes each, consumed in that order at the child's creation
      (`Env.forkClocks`). -/
  | forkStartTime | forkStartBoottime
  /-- P (pipes): `current_time` (fs/inode.c:2648), the coarse real-time
      clock read through `ktime_get_coarse_real_ts64` (kind 215), shared by
      all five callers on the pipe paths (design section 3). -/
  | currentTime
  /-- E-B (docs/2026-10-05-e-dos.md §5): the `under_load` clock read when a
      handshake crosses the queue threshold (`last_under_load =
      ktime_get_coarse_boottime_ns()`, receive.c:115), seen only in the
      discarded flood section; and `wg_cookie_message_create`'s nonce
      (`get_random_bytes_wait`, cookie.c:190, 24 bytes) of a cookie reply. -/
  | underLoadNow | cookieNonce
  /-- make_cookie's secret rotation (cookie.c:96-102, COOKIE_SECRET_MAX_AGE
      120 s): the new birthdate's coarse clock read and the 32 random bytes.
      Reachable only after a `wg_advance` (the receive audit's F7). -/
  | cookieSecretRotateNow | cookieSecretRotated
  /-- E-B arm C: `wg_ratelimiter_allow`'s coarse-boot-time reads, on a bucket
      hit (`ratelimiter.c:121`) and on a new-entry insert (`ratelimiter.c:146`). -/
  | ratelimiterNow | ratelimiterInsertNow
  /-- W5+W6 (docs/2026-10-06-w5-w6-receive.md, 3.2; id 140 of the stream's
      140-149): the TCP established-hash secret, `net_get_random_once` in
      `inet_ehashfn` (net/ipv4/inet_hashtables.c:36), drawn by the first TCP
      segment's lookup of a boot (early demux, or the socket lookup): a cut
      before the stack's RST re-enters `wg_xmit`. -/
  | inetEhashSecret
  /-- W9 (docs/2026-10-06-w8-w9-netns-routing.md, sections 4.1 and 5): the
      `jiffies` the dst cache stores, recorded by the kernel (kind 306):
      at `dst_cache_reset` (include/net/dst_cache.h:79, the inline, under
      `dst_cache_init`, `dst_cache_reset_now` and socket.c's callers) and
      at the refresh of a miss (`dst_cache_per_cpu_get`'s fail label,
      net/core/dst_cache.c:62). The mirror computes the cache's
      `time_after` from them (`WG.dstCacheGet`). -/
  | dstCacheResetTs | dstCacheRefreshTs
  /-- W8: `cleanup_net`'s own `cond_resched` (net/core/net_namespace.c:174,
      the pernet exits' loop) inside its section: a scheduler choice the
      mirror runs nothing across (no other armed unit runs in the teardown),
      so ambient. -/
  | reschedNetnsCleanup
  /-- `rhashtable_free_and_destroy`'s `cond_resched` (lib/rhashtable.c:1161),
      scheduling inside cleanup_net's section while the exiting namespace's
      hashtables are torn down: ambient, as `reschedNetnsCleanup` [AGENT, wgen]. -/
  | reschedRhashtableDestroy
  /-- `default_device_exit_batch`'s `cond_resched` (net/core/dev.c:12174,
      the pernet `exit_batch` of the device layer, run by `cleanup_net`'s
      `ops_exit_list` at net/core/net_namespace.c:178 while the exiting
      namespace's devices are moved out): a scheduler choice inside
      cleanup_net's section, written only under load, across which the
      mirror runs nothing (no other armed unit runs in the teardown), so
      ambient as `reschedNetnsCleanup` [AGENT, fork of the coordinator,
      2026-10-14: the integration record c047e64's named follow-on]. -/
  | reschedDefaultDeviceExit
  /-- epoll (docs/2026-10-12-epoll-design.md, 3.2; id 190 of epoll's block
      190-199): the kind-308 record of the `struct file` address an epoll
      item is keyed by, written by `kcov_epoll_insert` at the end of
      `ep_rbtree_insert` (fs/eventpoll.c:1585, on the line of
      `rb_insert_color_cached` so the file's numbering is kept), once per call: at
      every ADD that reaches the insert, including the ones
      `reverse_path_check` or a `pwq` allocation failure undo. Consumed by
      `epRbtreeInsert`. -/
  | epollInsertAddress
  -- Reserved id ranges for the W streams (the interface commit,
  -- docs/2026-10-11-interface.md), outside every range above: W5-W6
  -- 140-149 (`.inetEhashSecret`), W8-W9 150-169 (`.dstCacheResetTs`,
  -- `.dstCacheRefreshTs`, kind 306), W1-W2 170-179, W3-W12 180-189;
  -- W4-W7 adds no site. A stream appends its constructors in its own
  -- block here, in `info` and in `all`, as D3, L and E-B did.
  deriving Repr, BEq, DecidableEq

inductive SiteRole where
  | mirror | cut | ambient
  deriving Repr, BEq, DecidableEq

structure HiddenSiteInfo where
  /-- The number the check passes for records of this site. -/
  id : Nat
  label : String
  /-- `random`, `clock`, `section`, `resched`, `timer` (kind 303),
      `advance` (kind 304) or `alloc` (kind 305): the interception point's
      kind. Kind 306 (the dst-cache `jiffies` records, class `jiffies`) is
      reserved for W9 (docs/2026-10-11-interface.md) and unused until it lands. -/
  kind : String
  /-- The consumer frame: the first frame of the call chain outside the
      random and clock helpers. -/
  file : String
  line : Nat
  /-- Bytes recorded (the record carries whole words, zero-padded). -/
  len : Nat
  role : SiteRole

/-- A worker's section-start site id (its stop is the next id). The D1/D2
    units keep `40 + 2·index` (40-51); `40 + 2·index` for the D3 units
    (indices 6-11) would reach the resched sites (60-63), so they take
    102-113 in the D3 range, and indices 12-14 continue to 114-119. From
    index 15 the ids start at 200: `102 + 2·(index - 6)` would reach L's
    120-126 (the interface commit's reservation, docs/2026-10-11-interface.md). -/
def Worker.sectionId (w : Worker) : Nat :=
  if w.index < 6 then 40 + 2 * w.index
  else if w.index < 15 then 102 + 2 * (w.index - 6)
  else 200 + 2 * (w.index - 15)

/-- The queue-record site of a work item's function (dispatch order): ids
    from 300, above every section id. -/
def Worker.queueId (w : Worker) : Nat := 300 + w.index

def HiddenSite.info : HiddenSite → HiddenSiteInfo
  | .initEphemeral => ⟨1, "init_ephemeral", "random", "drivers/net/wireguard/noise.c", 541, 32, .mirror⟩
  | .respEphemeral => ⟨2, "resp_ephemeral", "random", "drivers/net/wireguard/noise.c", 688, 32, .mirror⟩
  | .tai64nNow => ⟨3, "tai64n_now", "clock", "drivers/net/wireguard/noise.c", 501, 16, .mirror⟩
  | .indexDraw => ⟨4, "index_draw", "random", "drivers/net/wireguard/peerlookup.c", 132, 4, .mirror⟩
  | .resetLastSent => ⟨5, "reset_last_sent", "clock", "drivers/net/wireguard/noise.h", 103, 8, .mirror⟩
  | .birthdateExpired => ⟨6, "birthdate_has_expired", "clock", "drivers/net/wireguard/timers.h", 28, 8, .mirror⟩
  | .initLastSent => ⟨7, "initiation_last_sent", "clock", "drivers/net/wireguard/send.c", 29, 8, .mirror⟩
  | .initLastSentAgain => ⟨8, "initiation_last_sent_again", "clock", "drivers/net/wireguard/send.c", 39, 8, .mirror⟩
  | .respLastSent => ⟨9, "response_last_sent", "clock", "drivers/net/wireguard/send.c", 89, 8, .mirror⟩
  | .respLastSentAgain => ⟨10, "response_last_sent_again", "clock", "drivers/net/wireguard/send.c", 102, 8, .mirror⟩
  | .floodNow => ⟨11, "flood_now", "clock", "drivers/net/wireguard/noise.c", 637, 8, .mirror⟩
  | .consumptionNow => ⟨12, "consumption_now", "clock", "drivers/net/wireguard/noise.c", 650, 8, .mirror⟩
  | .deriveKeysBirthdate => ⟨13, "derive_keys_birthdate", "clock", "drivers/net/wireguard/noise.c", 396, 8, .mirror⟩
  | .retransmitJitter => ⟨14, "retransmit_jitter", "random", "drivers/net/wireguard/timers.c", 186, 1, .mirror⟩
  -- D1 stream B. `ktime_get_real_ts64(&peer->walltime_last_handshake)`
  -- (timers.c:197) is a tail jump (`jmp ktime_get_real_ts64`), so the
  -- record's consumer frame is the caller of `wg_timers_handshake_complete`:
  -- the response arm of `wg_receive_handshake_packet`, inlined into the
  -- receive worker (return address - 1 resolves to receive.c:179 in the
  -- net-choice build); confirmed against the D1 kernel (resolved records
  -- of the full check).
  | .walltimeLastHandshake => ⟨15, "walltime_last_handshake", "clock", "drivers/net/wireguard/receive.c", 179, 16, .mirror⟩
  | .ipIdentReserve => ⟨20, "ip_idents_reserve", "random", "net/ipv4/route.c", 482, 4, .cut⟩
  | .ipIdentKey => ⟨21, "ip_ident_key", "random", "net/ipv4/route.c", 497, 16, .cut⟩
  | .icmpCredit => ⟨22, "icmp_global_consume", "random", "net/ipv4/icmp.c", 268, 1, .cut⟩
  | .flowHashSecret => ⟨23, "flow_hash_secret", "random", "net/core/flow_dissector.c", 1710, 16, .cut⟩
  | .schedDlTimer => ⟨30, "start_dl_timer", "clock", "kernel/sched/deadline.c", 1153, 8, .ambient⟩
  | .sectionStart w => ⟨w.sectionId, s!"section_start:{w.symbol}", "section", w.symbol, 0, 16, .mirror⟩
  | .sectionStop w => ⟨w.sectionId + 1, s!"section_stop:{w.symbol}", "section", w.symbol, 1, 8, .mirror⟩
  | .queued w => ⟨w.queueId, s!"queued:{w.symbol}", "queue", w.symbol, 0, 16, .mirror⟩
  | .reschedReceive => ⟨60, "resched:wg_packet_handshake_receive_worker", "resched", "drivers/net/wireguard/receive.c", 216, 8, .mirror⟩
  | .reschedEncrypt => ⟨61, "resched:wg_packet_encrypt_worker", "resched", "drivers/net/wireguard/send.c", 307, 8, .mirror⟩
  | .reschedTx => ⟨62, "resched:wg_packet_tx_worker", "resched", "drivers/net/wireguard/send.c", 283, 8, .mirror⟩
  | .reschedDecrypt => ⟨63, "resched:wg_packet_decrypt_worker", "resched", "drivers/net/wireguard/receive.c", 505, 8, .mirror⟩
  -- `get_random_u32_below(REKEY_TIMEOUT_JITTER_MAX_JIFFIES)` in
  -- wg_timers_data_sent (timers.c:150), the inline u8 path as for
  -- `.retransmitJitter`. Confirmed in the net-choice build (D2 stream A):
  -- wg_timers_data_sent is its own symbol, get_random_u32_below is inlined
  -- into it, and the records of the d2a transmit traces resolve to
  -- timers.c:150.
  | .newHandshakeJitter => ⟨16, "new_handshake_jitter", "random", "drivers/net/wireguard/timers.c", 150, 1, .mirror⟩
  -- D2 stream B. As for `.walltimeLastHandshake`, the tail jump
  -- (`jmp ktime_get_real_ts64`) leaves the caller's frame: the call in
  -- wg_packet_consume_data_done (receive.c:347), inlined into
  -- wg_packet_rx_poll; return address - 1 resolves to receive.c:347 in the
  -- net-choice build (checked with the check's symbolizer).
  | .walltimeLastHandshakeData => ⟨17, "walltime_last_handshake_data", "clock", "drivers/net/wireguard/receive.c", 347, 16, .mirror⟩
  -- E-A (ids 64-69 are E-A's): `peer->latest_cookie.birthdate =
  -- ktime_get_coarse_boottime_ns()` (cookie.c:225), the inline coarse
  -- boot-time read in wg_cookie_message_consume.
  | .cookieBirthdate => ⟨64, "cookie_birthdate", "clock", "drivers/net/wireguard/cookie.c", 225, 8, .mirror⟩
  -- D3 (ids 100-115 reserved for D3: docs/2026-10-05-d3-timers.md, section
  -- 14). `kcov_timer_arm(fn, jiffies, expires, _RET_IP_)` in `mod_timer`:
  -- the return address - 1 resolves to timers.c:37 for all seven callers
  -- (stream K, section 13.4). The advance record is written by the ioctl
  -- handler; its call site is `vfs_ioctl` (fs/ioctl.c:51), the only caller
  -- of `kcov_ioctl`.
  | .modTimerArm => ⟨100, "mod_timer_arm", "timer", "drivers/net/wireguard/timers.c", 37, 24, .mirror⟩
  | .timeAdvance => ⟨101, "time_advance", "advance", "fs/ioctl.c", 51, 16, .mirror⟩
  -- Review item 7 (docs/2026-10-13-review-items-7-8.md, section 5): the end of
  -- a guest idle wait, `jiffies` read by the KCOV_LEANUX_JIFFIES ioctl and
  -- written as kind 310 (class `jiffies`) into the remote stream from the
  -- same call site as the advance; consumed by `Env.idleTimers` and
  -- `Env.afterAdvance` as the firing window's exact end. Id 128: the first
  -- free id after L's block (120-127).
  | .jiffiesEnd => ⟨128, "jiffies_end", "jiffies", "fs/ioctl.c", 51, 8, .mirror⟩
  -- B3: the wheel's records at mod_peer_timer's line (the caller's return
  -- address passed through __mod_timer), kind classes `clk` and `wheel`;
  -- ids 428 and 429 continue the review's 420-427.
  | .timerClk => ⟨428, "timer_clk", "clk", "drivers/net/wireguard/timers.c", 37, 16, .mirror⟩
  | .timerEnqueue => ⟨429, "timer_enqueue", "wheel", "drivers/net/wireguard/timers.c", 37, 24, .mirror⟩
  -- Pre-release review finding 2: the caller's jiffies read before each
  -- mod_peer_timer, kind 311, 8 bytes, at the caller's line (the `_THIS_IP_`
  -- of the `kcov_timer_jiffies(jiffies, _THIS_IP_)` expression); ids 420-426.
  | .timerJiffiesRetransmitZeroKey => ⟨420, "timer_jiffies_retransmit_zero_key", "jiffies", "drivers/net/wireguard/timers.c", 62, 8, .mirror⟩
  | .timerJiffiesExpiredKeepalive => ⟨421, "timer_jiffies_expired_keepalive", "jiffies", "drivers/net/wireguard/timers.c", 87, 8, .mirror⟩
  | .timerJiffiesDataSent => ⟨422, "timer_jiffies_data_sent", "jiffies", "drivers/net/wireguard/timers.c", 149, 8, .mirror⟩
  | .timerJiffiesDataReceived => ⟨423, "timer_jiffies_data_received", "jiffies", "drivers/net/wireguard/timers.c", 159, 8, .mirror⟩
  | .timerJiffiesHandshakeInitiated => ⟨424, "timer_jiffies_handshake_initiated", "jiffies", "drivers/net/wireguard/timers.c", 185, 8, .mirror⟩
  | .timerJiffiesSessionDerived => ⟨425, "timer_jiffies_session_derived", "jiffies", "drivers/net/wireguard/timers.c", 206, 8, .mirror⟩
  | .timerJiffiesTraversal => ⟨426, "timer_jiffies_traversal", "jiffies", "drivers/net/wireguard/timers.c", 216, 8, .mirror⟩
  -- L (ids 120-126, outside E-A's 64-69, A's 70-99 and D3's 100-115). The
  -- consumer frames were confirmed on the built kernel by stream G's L0 probe
  -- (scripts/wg-l0-probe.py): kind 208 at cookie.c:23 and ratelimiter.c:57,
  -- kind 1 at cookie.c:24, peerlookup.c:29 and ratelimiter.c:192, kind 104 at
  -- udp.c:257, and exactly two kind-110 records at neighbour.c:115 per
  -- creation.
  | .cookieSecretBirthdate => ⟨120, "cookie_secret_birthdate", "clock", "drivers/net/wireguard/cookie.c", 23, 8, .mirror⟩
  | .cookieSecret => ⟨121, "cookie_secret", "random", "drivers/net/wireguard/cookie.c", 24, 32, .mirror⟩
  | .pubkeyHashKey => ⟨122, "pubkey_hash_key", "random", "drivers/net/wireguard/peerlookup.c", 29, 16, .mirror⟩
  | .ratelimiterKey => ⟨123, "ratelimiter_key", "random", "drivers/net/wireguard/ratelimiter.c", 192, 16, .mirror⟩
  | .ratelimiterGcNow => ⟨124, "ratelimiter_gc_now", "clock", "drivers/net/wireguard/ratelimiter.c", 57, 8, .mirror⟩
  | .udpPortDraw => ⟨125, "udp_port_draw", "random", "net/ipv4/udp.c", 257, 4, .mirror⟩
  -- `reachable_time` of the new device's ARP and ND parms: exported only in
  -- IFLA_INET6_CACHEINFO and the neighbour sysctls, which the harness never
  -- reads, and read by no modeled path (unobserved)
  | .neighReachTime => ⟨126, "neigh_reach_time", "random", "net/core/neighbour.c", 115, 4, .cut⟩
  -- W2 (ids 170-179): the stepped dump socket's autobind draw, kind 104 at
  -- af_netlink.c:820 (`get_random_u32_below`), seen on the W9 build
  | .netlinkAutobindPort => ⟨170, "netlink_autobind_port", "random", "net/netlink/af_netlink.c", 820, 4, .cut⟩
  -- W9 (ids 150-169): the dst cache's jiffies, kind 306, resolved by the
  -- innermost frame of the record's `_THIS_IP_` minus one (the resolver,
  -- evaluator/coverage.py symbolize, takes every address as a return
  -- address): the patched files' lines, confirmed on the W9 build
  -- (identity 313c2cc9...): the reset's four callers (dst_cache_init,
  -- wg_socket_set_peer_endpoint:294, send4:59, dst_cache_reset_now:177)
  -- share the inline's frame dst_cache.h:90, the refresh is
  -- dst_cache_per_cpu_get's dst_cache.c:63 (the design's 79/62 are the
  -- pristine lines)
  | .dstCacheResetTs => ⟨150, "dst_cache_reset_ts", "jiffies", "include/net/dst_cache.h", 90, 8, .mirror⟩
  | .reschedNetnsCleanup => ⟨152, "resched:cleanup_net", "resched", "net/core/net_namespace.c", 174, 8, .ambient⟩
  | .reschedRhashtableDestroy => ⟨153, "resched:rhashtable_free_and_destroy", "resched", "lib/rhashtable.c", 1161, 8, .ambient⟩
  | .reschedDefaultDeviceExit => ⟨427, "resched:default_device_exit_batch", "resched", "net/core/dev.c", 12174, 8, .ambient⟩
  | .dstCacheRefreshTs => ⟨151, "dst_cache_refresh_ts", "jiffies", "net/core/dst_cache.c", 63, 8, .mirror⟩
  | .alloc s => let i := s.info
    -- `AllocSite.hiddenId`: 70 + index, unique by construction (the indices skip D3's
    -- 100-117 and the epoll sites sit at 122-125 for their block's 192-195), and
    -- seccomp's 400 block
    ⟨s.hiddenId, i.label, "alloc", i.file, i.line, 40, if i.count == .cut then .cut else .mirror⟩
  -- epoll: kind 308, class `address` (evaluator/check.py EPOLL_INSERT_ADDRESS),
  -- the consumer frame the `_THIS_IP_` of the hook resolves to
  | .epollInsertAddress => ⟨190, "epoll_insert_address", "address", "fs/eventpoll.c", 1585, 8, .mirror⟩
  -- P (pipes, design section 3): id 18 is free on main and on every task
  -- branch (E-A uses 64-69, A 70-99); the records are consumed in sequence
  -- order by whichever of the five callers runs
  | .currentTime => ⟨18, "current_time", "clock", "fs/inode.c", 2648, 16, .mirror⟩
  -- E-B (ids 130-139, outside E-A's 64-69, A's 70-99, D3's 100-115 and L's
  -- 120-126; P's current_time is 18). receive.c:115 is read only in the
  -- discarded flood section; cookie.c:190 is the cookie reply's nonce.
  | .underLoadNow => ⟨130, "under_load_now", "clock", "drivers/net/wireguard/receive.c", 115, 8, .mirror⟩
  | .cookieNonce => ⟨131, "cookie_nonce", "random", "drivers/net/wireguard/cookie.c", 190, 24, .mirror⟩
  | .cookieSecretRotateNow => ⟨129, "cookie_secret_rotate_now", "clock", "drivers/net/wireguard/cookie.c", 99, 8, .mirror⟩
  | .cookieSecretRotated => ⟨134, "cookie_secret_rotated", "random", "drivers/net/wireguard/cookie.c", 100, 32, .mirror⟩
  | .ratelimiterNow => ⟨132, "ratelimiter_now", "clock", "drivers/net/wireguard/ratelimiter.c", 121, 8, .mirror⟩
  | .ratelimiterInsertNow => ⟨133, "ratelimiter_insert_now", "clock", "drivers/net/wireguard/ratelimiter.c", 146, 8, .mirror⟩
  -- W5+W6 (ids 140-149)
  | .inetEhashSecret => ⟨140, "inet_ehash_secret", "random", "net/ipv4/inet_hashtables.c", 36, 4, .cut⟩
  -- seccomp (ids 400-419; 400-410 are `AllocSite.hiddenId`'s)
  | .bpfProgInsn => ⟨411, "bpf_prog_insn", "program", "net/core/filter.c", 1315, 8, .mirror⟩
  | .seccompIp => ⟨414, "seccomp_ip", "address", "kernel/seccomp.c", 265, 8, .mirror⟩
  | .forkStartTime => ⟨412, "fork_start_time", "clock", "kernel/fork.c", 2532, 8, .mirror⟩
  | .forkStartBoottime => ⟨413, "fork_start_boottime", "clock", "kernel/fork.c", 2533, 8, .mirror⟩

def HiddenSite.all : List HiddenSite :=
  [.initEphemeral, .respEphemeral, .tai64nNow, .indexDraw, .resetLastSent, .birthdateExpired, .initLastSent,
   .initLastSentAgain, .respLastSent, .respLastSentAgain, .floodNow, .consumptionNow, .deriveKeysBirthdate,
   .retransmitJitter, .walltimeLastHandshake, .ipIdentReserve, .ipIdentKey, .icmpCredit, .flowHashSecret, .schedDlTimer]
  ++ Worker.all.flatMap (fun w => [.sectionStart w, .sectionStop w])
  ++ [.reschedReceive, .reschedEncrypt, .reschedTx, .reschedDecrypt, .newHandshakeJitter, .walltimeLastHandshakeData,
      .cookieBirthdate]
  ++ [.modTimerArm, .timeAdvance, .jiffiesEnd, .timerClk, .timerEnqueue]
  ++ [.timerJiffiesRetransmitZeroKey, .timerJiffiesExpiredKeepalive, .timerJiffiesDataSent, .timerJiffiesDataReceived,
      .timerJiffiesHandshakeInitiated, .timerJiffiesSessionDerived, .timerJiffiesTraversal]
  ++ (Worker.all.filter fun w => w.timer?.isNone && w != .netRx).map .queued
  ++ [.cookieSecretBirthdate, .cookieSecret, .pubkeyHashKey, .ratelimiterKey, .ratelimiterGcNow, .udpPortDraw,
      .neighReachTime, .netlinkAutobindPort]
  ++ [.dstCacheResetTs, .dstCacheRefreshTs, .reschedNetnsCleanup, .reschedRhashtableDestroy, .reschedDefaultDeviceExit]
  ++ AllocSite.all.map .alloc
  ++ [.currentTime]
  ++ [.underLoadNow, .cookieNonce, .ratelimiterNow, .ratelimiterInsertNow, .cookieSecretRotateNow, .cookieSecretRotated]
  ++ [.bpfProgInsn, .forkStartTime, .forkStartBoottime, .seccompIp]
  ++ [.inetEhashSecret]
  ++ [.epollInsertAddress]

/-- The resched site of a worker's `cond_resched`, for the workers that
    have one on the modeled paths. -/
def Worker.resched? : Worker → Option HiddenSite
  | .receiveWorker => some .reschedReceive
  | .encryptWorker => some .reschedEncrypt
  | .txWorker => some .reschedTx
  | .decryptWorker => some .reschedDecrypt
  | _ => none

/-- W7 phase 2 (docs/2026-10-06-w4-w7-transmit-bulk.md 17.15; the
    simulation-target review's rank 6): a draining worker's activation, a
    value in the world rather than a Lean call frame. Its kind, its peer (the
    tx worker's `container_of(work, struct wg_peer, transmit_packet_work)`)
    and its loop position: the iterations run so far, for the loop's bound.
    Between two yields the C loop holds no other local: each iteration starts
    at the ring or queue poll, and what a run keeps across runs (the tx
    worker's peeked item) is in the queue, as data. An activation lives from
    its section's start to its stop; suspended at a `cond_resched` it waits
    in `World.suspended` until the records resume it (`Env.schedule`). -/
structure Activation where
  worker : Worker
  pid : Option Nat := none
  iterations : Nat := 0
  deriving Repr, BEq

def SiteRole.name : SiteRole → String
  | .mirror => "mirror" | .cut => "cut" | .ambient => "ambient"

/-- One recorded value: the site's number and its bytes (whole words). -/
structure HiddenRecord where
  site : Nat
  bytes : List UInt8
  deriving Repr, BEq

/-- Timing facts the environment supplies (`Leanux/Env.lean`); the mirror has
    no clock. D3 (docs/2026-10-05-d3-timers.md, section 5.3): the bounds of
    the firing window, in ticks, for the domain filter's prediction only
    (review item 7): with records the window ends at the recorded end of the
    wait (kind 310, `HiddenSite.jiffiesEnd`), and these constants are not
    consulted. Without records the filter predicts a firing iff the timer is
    pending with `expires < J_hi`, `J_hi` the advance's `jiffies` after plus
    `advanceWait` inside `wg_advance`, and the last known `jiffies` plus
    `traceBound` plus `advanceWait` at the other idle points. -/
structure Timing where
  /-- The guest's wait after an advance has been absorbed (`W`). -/
  advanceWait : Nat
  /-- The trace's real-time bound (`R`), which also bounds the time since the
      last recorded `jiffies`. -/
  traceBound : Nat

/-- A datagram wg0's socket sent (`wg_socket_send_buffer_to_peer`, a cut
    point): the endpoint's family, address and port, and the bytes. -/
structure SentDatagram where
  family : Nat
  addr : Nat
  port : Nat
  bytes : List UInt8
  /-- L: the source port, wg0's `incoming_port` when it sent (its socket's
      bound port): what the receiving fixture socket reports. -/
  sport : Nat := 0
  /-- The outer DS field `send4`/`send6` are given (`PACKET_CB(skb)->ds`;
      0 for handshake messages): the outer IPv4 TOS / IPv6 traffic class
      (`iptunnel_xmit`, `ip6_flow_hdr`), which the fixture's listeners and
      sender report (W5). -/
  ds : Nat := 0
  /-- W9: the source address `send4`/`send6` chose (the cached or routed
      `fl.saddr`): what the receiving fixture socket's `recvfrom` reports. -/
  src : Nat := 0
  deriving Repr, BEq

/-- A datagram at the fixture's sender socket, with its source as
    `recvfrom` reports it (D2: wg0's own datagrams and delivered inner
    packets share the socket). -/
structure InboxDatagram where
  family : Nat
  addr : Nat
  port : Nat
  bytes : List UInt8
  /-- W5: the TOS / traffic class the sender's `recvmsg` reports (the
      outer DS of wg0's datagram, the inner TOS of a delivered packet). -/
  tos : Nat := 0
  /-- W5: the destination `IPV6_PKTINFO` reports on the dual-stack sender
      (an IPv4 datagram's as v4-mapped): wg0's address for a delivered
      inner packet, the endpoint's address for wg0's own datagram. -/
  dst : Nat := 0
  deriving Repr, BEq

structure World where
  k : Kernel
  /-- The pipe sites' environment oracle (`EnvSite`). -/
  env : EnvSite → Nat → Bool
  timing : Timing
  envCalls : List (EnvSite × Nat) := []
  steps : Array Step := #[]
  /-- seccomp (design 4.2, 4.5): the repeatable decisions of the checker,
      the translation, the cache's emulation and the entry path are emitted
      once per operation as a set of (decision, outcome, operands); the keys
      emitted so far in this operation (`Seccomp.Bridge`). -/
  emitted : Std.HashSet String := {}
  /-- seccomp: the kind-309 length record, read before the instructions
      (stream W's order) and answered to the translation after them. -/
  translatedLen : Option Nat := none
  /-- The caller's buffer (user memory), as written by `copy_to_iter` (an
      eventfd read's 8 bytes) or `copy_page_to_iter` (a pipe read). -/
  userOut : Option ByteArray := none
  /-- The descriptor pair `do_pipe2` copied to the caller (`fd[0]`, `fd[1]`,
      fs/pipe.c:1026): the `fds` observation field. -/
  userFds : Option (Nat × Nat) := none
  /-- Observation fields beyond the return value: a dump's `device`, or what
      `wg_observe` saw (`datagrams`, `stats`). -/
  extraOut : List (String × Lean.Json) := []
  /-- Fixture state, not kernel state: the datagrams waiting at the network
      fixture's UDP listeners (each with the outer TOS / traffic class the
      listener's cmsg reports, W5) and at its sender, which `wg_observe`
      drains. -/
  listenerV4 : List (Nat × List UInt8) := []
  listenerV6 : List (Nat × List UInt8) := []
  senderInbox : List InboxDatagram := []
  /-- Datagrams wg0's sockets sent, oldest first, not yet delivered. The
      environment decides which fixture socket receives them. -/
  sent : List SentDatagram := []
  /-- The current operation's hidden-input records not yet consumed, in
      order (task stream, then remote). `none`: no records were supplied. -/
  hidden : Option (List HiddenRecord) := none
  /-- Without records, `hidden` returns placeholders (`leanux-model --domain`,
      which runs before Linux). -/
  hiddenPlaceholders : Bool := false
  placeholderCount : Nat := 0
  /-- W7 phase 2: the draining workers' activations suspended at a
      `cond_resched`, oldest first, each resumed when the records name it
      (`Activation`, `Env.schedule`). An operation ends with none suspended
      (`Runner.executeTrace`). -/
  suspended : List Activation := []
  /-- Dispatch order (docs/2026-10-11-dispatch-order.md): each work unit's
      address from its queue record (`unitPeers`: address, worker index,
      peer, 0 for a device-level unit); each armed timer's address from its
      arm record (`timerUnits`: address, peer, timer); and the device-level
      work units whose `WORK_STRUCT_PENDING` bit is set (`pendingWork`:
      worker indices), set by a `queue_work` that queues and cleared when
      the unit's section starts (`process_one_work`). A per-peer unit's
      pending bit is its membership of its queue.
      An association lives as long as the C object that embeds the work
      struct or the timer: a peer's (`transmit_handshake_work`,
      `transmit_packet_work`, `clear_peer_work`, the five timers) until the
      peer's release (`kref_release`, `retirePeerUnits`), the device's
      (`incoming_handshake_work`, the per-CPU crypt work) until
      `free_netdev` (`retireDeviceUnits`). After that the address may be
      reused by a new object with a new record, and a fresh device's peer
      ids restart (the simulation-target review, 2026-10-12, section 4.3). -/
  unitPeers : List (Nat × Nat × Nat) := []
  timerUnits : List (Nat × Nat × WG.PeerTimer) := []
  /-- B3 (docs/2026-10-15-design-b3-timer-wheel.md, section 3.3): the bucket
      expiry of the step a timer pass is at while one of its callbacks runs
      (`Env.runTimers`), for the check that an arm inside the pass sees a
      base clock past that step (`base->clk++`, timer.c:2416); `none`
      outside a callback. -/
  timerPassStep : Option UInt64 := none
  /-- B3 (section 3.4): the last `wg_advance`'s `{before, after}`, for the
      pass bound after the advance (`J_pass = before` when the end-of-wait
      read equals `after`: no tick has followed the jump). -/
  lastAdvance : Option (UInt64 × UInt64) := none
  /-- B3 (section 3.4, E2): the later operations' records, for the lookahead
      that tells a deferred timer softirq (its section appears later) from a
      due timer that never fires; `none` without records. -/
  hiddenAhead : Option (List (List HiddenRecord)) := none
  pendingWork : List Nat := []
  /-- W8 (docs/2026-10-06-w8-w9-netns-routing.md, 3.1): the foreign-creator
      fixture, where wg0's creating namespace C is held by the fixture's
      listeners, injector and pin (`netnsCHolders`: descriptors 9, 8, 5, 4)
      until the trace's `wg_netns_close` drops them. -/
  foreignCreator : Bool := false
  netnsCHolders : List Nat := []
  /-- A NET_RX softirq raised by a loopback transmission (`netif_rx` from
      `send4`/`send6` or an ICMP error), whose section has not been consumed
      yet: see `WG.loopbackSoftirq`. An operation ends with none pending
      (`Runner.executeTrace`). -/
  netRxRaised : Bool := false
  /-- The placements of the decrypt worker's NAPI poll that its records do
      not determine (`Env.napiIrqExit`): for each such poll in turn, whether
      it ran at the interrupt exit inside `wg_queue_enqueue_per_peer_rx`
      (`true`) or after it; the check enumerates them. Missing entries are
      `false`. `napiAmbiguous` counts the polls met. -/
  napiBeforePut : List Bool := []
  napiAmbiguous : Nat := 0
  /-- W7 stream H: the NET_RX section starts consumed so far in the
      operation (`noteNetRxStart`: run or skipped, every one the records
      carry) and the one open now (0: none), stamped on every step
      (`Step.section`). -/
  netRxSections : Nat := 0
  netRxSection : Nat := 0
  /-- A steered trace's schedule (site label, value or a draw), which the
      placeholders follow: the domain filter's verdict is then exact for the
      steered sites. -/
  steerValues : List (String × Option (List UInt8)) := []
  /-- Peers whose handshake work this system call queued, while the call has
      not slept. The kernel is `CONFIG_PREEMPT_NONE` on one CPU, so their
      worker cannot have run yet. -/
  queuedThisCall : List Nat := []
  /-- D3, fixture knowledge (docs/2026-10-05-d3-timers.md, section 5.4): the
      last `jiffies` a record told (kinds 303 and 304), the C's `unsigned
      long` (64-bit on x86_64, review item 8); `none` before the first. -/
  jiffiesLast : Option UInt64 := none
  /-- D3: whether this run's records include the kind-303 arm records (the
      wire's `A` line, `harness/linux.py` `ARM_RECORDS`; the check passes
      the same value as the input's `arm_records`). Without them the mirror
      consumes none and a timer's `expires` is nominal. -/
  armRecords : Bool := false
  /-- W9: whether this run's records include the kind-306 dst-cache jiffies
      (every live run: the kernel writes them with the arm records; the
      check never clears it). False only for the replay tests' captures made
      before the record existed (`evaluator/test_model_replay.py`
      `widen`), under which the mirror keeps the pre-W9 rule: the cache
      always misses and no record is consumed. -/
  dstCacheRecords : Bool := true
  /-- D3: the timer sections the environment ran in this operation, by
      callback symbol, for the trace's `fired:<symbol>` expectations
      (`Env.runTimerSection`). -/
  fired : Array String := #[]
  /-- W9 (docs/2026-10-06-w8-w9-netns-routing.md, sections 2.6 and 4.2),
      the fixture namespace's tables, replacing L's single `routesViaWg0`:
      wg0's addresses (added by `route_into_wg0` after a successful
      `wg_up`; the IPv4 one survives a down, the IPv6 one does not; both go
      with `wg_delete` and `wg_deladdr`), the default route per family via
      wg0 (removed by `wg_down`, `wg_delete`, `wg_delroute`, and, for IPv4,
      with the device's last address), whether the IPv4 default route was
      ever looked up (`FA_S_ACCESSED`: its deletion bumps the generation
      only then), and the two route generations the dst cache's validity
      check reads (`rt_genid`; the IPv6 fib sernum), bumped by every table
      change. The loopback prefixes are constants (`World.route4/6`). -/
  addrs4 : List Nat := []
  addrs6 : List Nat := []
  defaultRoute4 : Bool := false
  defaultRoute6 : Bool := false
  defaultRoute4Accessed : Bool := false
  ipv4Gen : Nat := 0
  ipv6Gen : Nat := 0
  /-- W9 (design 14.3b): a successful flag-changing `wg_up` gets its
      addresses and routes after the operation's wait (the guest's
      `route_into_wg0` follows the wait), so the table changes apply after
      the send workers and the idle timers of that operation
      (`Env.routeIntoWg0`). -/
  routesPending : Bool := false
  /-- W4, fixture state: the routes `net_fixture.routes` adds into wg0 at
      every `wg_up` (family, destination, the route's MTU): `dst_mtu` of a
      datagram to that destination (`Env.xmitPackets`). -/
  routes : List (Nat × Nat × Nat) := []
  /-- L, environment: whether a fixture socket holds UDP port `p` so that a
      wildcard bind there conflicts (`Env.portBound`; the runner supplies
      it, as it supplies `env`). -/
  portBound : Nat → Bool := fun _ => false
  /-- W1 (docs/2026-10-06-w1-w2-netlink.md, 3.2), environment: the fixture
      namespace's devices other than wg0, as `lookup_interface` sees them:
      name, ifindex, `rtnl_link_ops->kind` (`none`: no link ops). The
      runner supplies it (`Env.fixtureNetDevices`); wg0's row comes from
      `Kernel.wg`. -/
  fixtureNetDevices : List (String × Nat × Option String) := []
  /-- The allocation sites whose records this run carries: the sites inside
      the ranges the evaluator armed (harness/steer.py `alloc_armed_labels`).
      Every other site answers ok without a record — the transitional
      unarmed answer of docs/2026-10-05-a-alloc.md section 6.6, declared,
      and never applied to a site the run armed. -/
  allocArmed : List String := []
  /-- In the domain filter: the allocation sites the steering schedule
      names. Their every encounter needs an entry (design section 5.1). -/
  allocSteered : List String := []
  /-- The function-static `last_under_load` of `wg_receive_handshake_packet`
      (receive.c:100): the coarse boot time of the last under-load handshake,
      or `none` for the C's 0 (never under load, or reset by the decay at
      receive.c:119). Kernel-global and never reset by teardown; per trace
      here because the checker runs each flooding trace in its own guest
      (docs/2026-10-05-e-dos.md §4.2), so a leak between traces is a
      control-flow mismatch. Every flood packet the receive worker handles
      sets or decays it as the C does (B4: the flood runs exactly). -/
  lastUnderLoad : Option Int64 := none

/-- Why a mirror execution stopped without an observation. -/
inductive Stop where
  /-- The C leaves the modeled domain at `site` (the condition of the last
      recorded decision): a blocking wait, table expansion, a waiter, ... -/
  | outsideDomain (site : String) (what : String)
  /-- The mirror's own state is inconsistent (a dangling identity, an
      out-of-range slot, a NULL `f_op`): a mirror defect, never a C path. -/
  | invariant (what : String)
  /-- The hidden-input records disagree with the mirror's reads: a different
      site, a wrong length, a missing record, or one left unconsumed. -/
  | hidden (what : String)
  deriving Repr

def Stop.message : Stop → String
  | .outsideDomain site what => s!"unsupported at {site}: {what}"
  | .invariant what => s!"mirror invariant violated: {what}"
  | .hidden what => s!"hidden-input records disagree: {what}"

/-- The mirror monad; `Stop` ends the execution fail-noisily. -/
abbrev M := StateT World (Except Stop)

/-! ## W9: the fixture namespace's routing (docs/2026-10-06-w8-w9-netns-routing.md, 2.6, 4.2) -/

/-- A route the fixture's tables give: the output device (`lo` 1, wg0 3)
    and the source address the lookup selects (`prefsrc`, or
    `inet_select_addr` for the device route). -/
structure Route where
  dev : Nat
  src : Nat
  deriving Repr, BEq

def LO_IFINDEX : Nat := 1
def WG0_IFINDEX : Nat := 3
def LOOPBACK4 : Nat := 0x7f000001
/-- W5 (docs/2026-10-06-w5-w6-receive.md, 2.5): the link-local address the
    fixture adds on `lo`, fe80::ffff:1/128 (harness/guest.c `network_fixture`;
    not fe80::1, which existing traces transmit to through wg0): a local
    destination and source over `lo` (W9's tables), the source of a
    `from: "ll"` injection. -/
def LO_LINK_LOCAL : Nat := 0xfe8000000000000000000000ffff0001

/-- `ip_route_output_flow` on the fixture's tables (route.c): a set source
    must be local (`127/8` or a wg0 address), else `-ENETUNREACH`
    (route.c:2751-2754; the `-EINVAL` class of :2706-2712 needs a multicast
    or zeronet source the fixture never configures); a `127/8` destination
    or a wg0 address takes the local route over `lo` with `prefsrc`
    (`127.0.0.1` for `127/8`, the address itself otherwise; :2833-2838);
    anything else the default route via wg0 while it exists, with the
    device's address as source, else `-ENETUNREACH` (:2714). -/
def World.route4 (w : World) (saddr daddr : Nat) : Except Int Route :=
  let isLocal (a : Nat) := a / 2 ^ 24 == 127 || w.addrs4.contains a
  if saddr != 0 && !isLocal saddr then .error (-101)   -- -ENETUNREACH
  else if isLocal daddr then
    .ok { dev := LO_IFINDEX, src := if saddr != 0 then saddr else if daddr / 2 ^ 24 == 127 then LOOPBACK4 else daddr }
  else match w.defaultRoute4, w.addrs4.head? with
    | true, some a => .ok { dev := WG0_IFINDEX, src := if saddr != 0 then saddr else a }
    | _, _ => .error (-101)

/-- `ipv6_dst_lookup_flow` on the fixture's tables: `::1` and wg0's address
    are local over `lo`; else the default route via wg0 (source: the
    device's address) or `ip6_null_entry`'s `-ENETUNREACH`. -/
def World.route6 (w : World) (saddr daddr : Nat) : Except Int Route :=
  let isLocal (a : Nat) := a == 1 || a == LO_LINK_LOCAL || w.addrs6.contains a   -- W5: the link-local address on lo
  if saddr != 0 && !isLocal saddr then .error (-101)
  else if isLocal daddr then .ok { dev := LO_IFINDEX, src := if saddr != 0 then saddr else daddr }
  else match w.defaultRoute6, w.addrs6.head? with
    | true, some a => .ok { dev := WG0_IFINDEX, src := if saddr != 0 then saddr else a }
    | _, _ => .error (-101)

/-- A lookup, noting a resolution through the IPv4 default route
    (`fib_alias_accessed`, the `FA_S_ACCESSED` flag `wg_delroute`'s
    generation bump depends on). -/
def routeLookup (family saddr daddr : Nat) : M (Except Int Route) := do
  let w ← get
  if family == 4 then
    let r := w.route4 saddr daddr
    if let .ok { dev := d, .. } := r then
      if d == WG0_IFINDEX then set { w with defaultRoute4Accessed := true }
    return r
  else return w.route6 saddr daddr

/-- W9: whether a fixture socket receives at `addr:port` for `family`: the
    dual-stack sender is bound to the wildcard address at `SENDER_PORT`, so
    it receives at every local address (`127/8`, `::1`, wg0's addresses). -/
def World.wildcardLocal (w : World) (family addr : Nat) : Bool :=
  (family == 2 && (addr / 2 ^ 24 == 127 || w.addrs4.contains addr))
  || (family == 10 && (addr == 1 || addr == LO_LINK_LOCAL || w.addrs6.contains addr))   -- W5: the link-local address on lo

/-- The C leaves the modeled domain here. The site is the last decision the
    mirror recorded, which is the C condition that led here. -/
def unsupported (what : String) : M α := do
  let site := match (← get).steps.back? with
    | some s => s!"{s.decision.info.file}:{s.decision.info.line}"
    | none => "syscall entry"
  throw (.outsideDomain site what)

/-- A mirror defect: the state is inconsistent with the C's invariants. -/
def invariant (what : String) : M α := throw (.invariant what)

def getK : M Kernel := return (← get).k
def modifyK (f : Kernel → Kernel) : M Unit := modify fun w => { w with k := f w.k }

/-- The task `t` names (design 4.1). Reading the child while none exists
    is a runner invariant: no path reaches a child outside its probe. -/
def getTask (t : TaskRef) : M Task := do
  let k ← getK
  match t with
  | .task => return k.task
  | .child =>
    match k.child with
    | some c => return c
    | none => invariant "a kernel path targets the child, and there is no child"

/-- Update the task `t` names; the missing child is the same invariant. -/
def modifyTask (t : TaskRef) (f : Task → Task) : M Unit := do
  let k ← getK
  match t with
  | .task => modifyK fun k => { k with task := f k.task }
  | .child =>
    match k.child with
    | some c => modifyK fun k => { k with child := some (f c) }
    | none => invariant "a kernel path targets the child, and there is no child"

/-- The task the runner is executing: `Kernel.current` resolved. -/
def getCurrent : M Task := do getTask (← getK).current
def getFiles : M FilesStruct := return (← getK).task.files
def modifyFiles (f : FilesStruct → FilesStruct) : M Unit :=
  modifyK fun k => { k with task := { k.task with files := f k.task.files } }
def modifyFdt (f : Fdtable → Fdtable) : M Unit :=
  modifyFiles fun fs => { fs with fdt := f fs.fdt }

/-- Record a C decision point with its outcome and return the outcome. -/
def branch (d : Decision) (outcome : Bool) : M Bool := do
  modify fun w => { w with steps := w.steps.push { decision := d, outcome, netRx := w.netRxSection } }
  return outcome

/-- What one iteration of a draining worker's loop did (W7 phase 2): the
    poll found nothing and the loop ended; an item was processed and the loop
    goes on; an item was processed and the worker switched away at its
    `cond_resched`, so its activation is suspended (`Env.schedule`). -/
inductive IterResult where
  | ended | continued | yielded
  deriving Repr, BEq, DecidableEq

/-- One iteration of a draining worker's loop (`wg_packet_encrypt_worker`,
    `wg_packet_tx_worker`, `wg_packet_decrypt_worker`,
    `wg_packet_handshake_receive_worker`): `step`, one ring or queue poll
    and its item, then `afterItem`, the `cond_resched` and its decision
    (whether the kernel switched away), when an item was processed. The loop
    body between two yields is the C's, direct sequential code; the iteration
    is the unit an activation resumes at (W7 phase 2, design 17.15). `w` and
    `pid` name the activation. -/
def workerIter (w : Worker) (pid : Option Nat) (step : M Bool) (afterItem : M Bool) : M IterResult := do
  let _ := (w, pid)
  if !(← step) then return .ended
  return if ← afterItem then .yielded else .continued

/-- A worker's whole loop on the mirror's own stack (the flood's receive
    worker, `Env.flood`, whose yields `Env.nestedResched` serves in place):
    `workerIter` until the queue drains, under the C's bound. -/
def workerLoop (w : Worker) (pid : Option Nat) (step : M Bool) (afterItem : M Unit) (bound : Nat)
    (drained : String) : M Unit := do
  for _ in [0:bound] do
    if (← workerIter w pid step (do afterItem; pure false)) == .ended then return
  invariant drained

/-- `iput(inode)` (fs/inode.c:1889-1904) where the mirror holds no inode of
    its own: the last-reference test (`atomic_dec_and_lock`, :1895) and, on
    the last reference, the lazytime test (:1896), false for every such
    inode. The shared anonymous inode of eventfd and epoll keeps its pinned
    reference (`last` false); a socket's or a namespace pin's inode holds its
    only reference (`last` true). A pipefs inode's own count decides it in
    `iputPipefs` (Leanux/FS/Inode.lean). The mutation campaign's finding 1
    (2026-10-14): a leaked inode was invisible without the declaration. -/
def iputReport (last : Bool) : M Unit := do
  if ← branch .iputLastReference last then
    _ ← branch .iputLazytime false

/-- Record a C value comparison: its outcome and the two values the C
    compares at the condition. The check matches them against
    `KCOV_TRACE_CMP` records at the condition line. -/
def branchCmp (d : Decision) (outcome : Bool) (a b : Int) : M Bool := do
  modify fun w => { w with steps := w.steps.push { decision := d, outcome, operands := some (a, b), netRx := w.netRxSection } }
  return outcome

/-- Record a C value comparison at a declared operand exclusion (a call site
    whose operand is a guest-wide value the mirror does not model; see
    `OperandExclusion`): the outcome, which the contract fixes, without the
    operands. The check requires Linux's comparison at the declared call site. -/
def branchCmpExcluded (d : Decision) (outcome : Bool) (x : OperandExclusion) : M Bool := do
  modify fun w => { w with steps := w.steps.push { decision := d, outcome, excluded := some x, netRx := w.netRxSection } }
  return outcome

/-- The kernel's `jiffies` comparisons (include/linux/jiffies.h:127-150,
    review item 8): `time_after(a, b)` is `(long)((b) - (a)) < 0` on
    `unsigned long`, a signed 64-bit difference, so a wrapped `jiffies`
    compares as the C compares it. These are the C's macros, not
    approximations of them. -/
def timeAfter (a b : UInt64) : Bool := (b - a).toInt64 < 0
/-- `time_before(a, b)` is `time_after(b, a)` (jiffies.h:138). -/
def timeBefore (a b : UInt64) : Bool := timeAfter b a
/-- `time_after_eq(a, b)` is `(long)((a) - (b)) >= 0` (jiffies.h:147-150). -/
def timeAfterEq (a b : UInt64) : Bool := (a - b).toInt64 ≥ 0
/-- `time_before_eq(a, b)` is `time_after_eq(b, a)` (jiffies.h:151). -/
def timeBeforeEq (a b : UInt64) : Bool := timeAfterEq b a

/-- Ask the environment oracle; the site's call count is part of the query. -/
def envOk (site : EnvSite) : M Bool := do
  let w ← get
  let n := (w.envCalls.find? (·.1 == site)).map (·.2) |>.getD 0
  set { w with envCalls := (site, n + 1) :: w.envCalls.filter (·.1 != site) }
  return w.env site n

/-- Word `k` of a record's bytes (little-endian). -/
def recordWordOf (bs : List UInt8) (k : Nat) : Nat :=
  ((bs.drop (8 * k)).take 8).foldr (fun b acc => acc * 256 + b.toNat) 0

/-- Whether the consumers pass over a site's records: ambient ones, dropped
    wherever they occur. -/
def HiddenSite.passive (site : Nat) : Bool :=
  HiddenSite.all.any fun s => s.info.id == site && s.info.role == .ambient

/-- Drop ambient records at the head of the current operation's records. -/
def skipAmbient : M Unit := do
  let w ← get
  if let some rs := w.hidden then
    set { w with hidden := some (rs.dropWhile fun r => HiddenSite.passive r.site) }

/-- W7 stream H: a `net_rx_action` section start, consumed by any consumer
    (`hidden`, a cut, the flood discard), advances the NET_RX ordinal
    (`World.netRxSections`): the ordinal counts every NET_RX section the
    records carry, in the order the mirror consumes them, which is how the
    guest numbers its blocks (`evaluator/check.py`, `netrx_sections`); a
    section the environment only skips (a loopback transmission's, a flood
    producer's) counts like one it runs [AGENT, 2026-10-14: the mutation
    campaign's finding 4]. -/
def noteNetRxStart (site : Nat) : M Unit := do
  if site == (HiddenSite.sectionStart .netRx).info.id then
    modify fun w => { w with netRxSections := w.netRxSections + 1 }

/-- Consume the next choice record, which must come from `s`. -/
def hidden (s : HiddenSite) : M (List UInt8) := do
  skipAmbient
  noteNetRxStart s.info.id
  let w ← get
  let i := s.info
  match w.hidden with
  | none =>
    if !w.hiddenPlaceholders then throw (.hidden s!"no record supplied for {i.label}")
    -- A placeholder of the right shape, for the domain filter (which runs
    -- before Linux): distinct values, so index draws do not collide; a
    -- clock that advances; a jitter byte that is accepted at once.
    let n := w.placeholderCount + 1
    set { w with placeholderCount := n }
    -- a steered site takes the schedule's next value for it
    match w.steerValues.findIdx? (·.1 == i.label) with
    | some k =>
      set { w with placeholderCount := n, steerValues := w.steerValues.eraseIdx k }
      if let some v := w.steerValues[k]!.2 then
        if v.length != i.len then throw (.hidden s!"steer: {i.label} takes {i.len} bytes")
        return v
    | none => pure ()
    let le (v width : Nat) := (List.range width).map fun k => UInt8.ofNat (v / 256 ^ k % 256)
    return match i.kind with
      -- a sane timespec64 (tv_nsec < 10^9) for `current_time` (P design
      -- section 3); the other 16-byte clocks keep their placeholder
      | "clock" => if s == .currentTime then le (1700000000 + n) 8 ++ le 0 8
          else le (1000000000000 + n * 1000000000) i.len
      | _ => if s == .retransmitJitter then [200] else
          (List.range i.len).map fun k => UInt8.ofNat ((n * 131 + k * 29 + 7) % 256)
  | some [] => throw (.hidden s!"no record left for {i.label}")
  | some (r :: rest) =>
    if r.site != i.id then throw (.hidden s!"expected {i.label} (site {i.id}), the record is site {r.site}")
    let words := (i.len + 7) / 8
    if r.bytes.length != 8 * words || (r.bytes.drop i.len).any (· != 0) then
      throw (.hidden s!"{i.label}: {r.bytes.length} bytes, expected {i.len} padded to {8 * words}")
    set { w with hidden := some rest }
    -- dispatch order: `process_one_work` clears the unit's PENDING bit before
    -- it calls the function, which is where its section starts
    if let .sectionStart ws := s then
      modify fun st => { st with pendingWork := st.pendingWork.filter (· != ws.index) }
    return r.bytes.take i.len

/-- A record's bytes as a little-endian natural (the 8-byte `jiffies`
    records of kind 306, W9). -/
def hiddenU64 (s : HiddenSite) : M Nat := do
  let bs ← hidden s
  return bs.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- The site of the next record to consume (after ambient ones), without
    consuming it: how the environment's scheduler reads a recorded
    scheduling choice. `none` without records (the domain filter). -/
def peekHiddenSite : M (Option Nat) := do
  skipAmbient
  return match (← get).hidden with
    | some (r :: _) => some r.site
    | _ => none

/-- The records of the current operation not yet consumed (0 without
    records). The measure of the record-driven loops (review item 7). -/
def recordsLeft : M Nat := do
  return ((← get).hidden.map (·.length)).getD 0

/-- The value of the first record of site `s` among the operation's remaining
    records, without consuming it (`none` if there is none, or without
    records): how `Env.idleTimers` learns the end of a wait before it
    consumes the timer sections that precede the read. -/
def peekSiteU64 (s : HiddenSite) : M (Option UInt64) := do
  let i := s.info
  return match (← get).hidden with
    | some rs =>
      (rs.find? (·.site == i.id)).map fun r =>
        ((r.bytes.take i.len).foldr (fun (b : UInt8) (acc : Nat) => acc * 256 + b.toNat) 0).toUInt64
    | none => none

/-- The domain filter's own turn bound for the loops that the records drive
    when there are records (review item 7): without records (the filter runs
    before Linux) a loop has no measure but the filter's patience, and its
    exhaustion is the filter's `unsupported`, never an `invariant`. -/
def DOMAIN_FILTER_TURNS : Nat := 4096

/-- The fuel of a record-driven loop: with records, one turn per remaining
    record plus the turn that finds none (every productive turn consumes at
    least one record); without records, the filter's bound. -/
def recordBudget : M Nat := do
  let w ← get
  return match w.hidden with
    | some rs => rs.length + 1
    | none => DOMAIN_FILTER_TURNS

/-- A record-driven loop ran out of fuel: with records that is a turn that
    consumed nothing, a genuine non-progress (`invariant`); without records
    the filter's bound (`unsupported "runner budget: ..."`). -/
def budgetExhausted (name : String) : M α := do
  if (← get).hidden.isSome then invariant s!"{name}: a turn consumed no record"
  else unsupported s!"runner budget: {name} (domain filter)"

/-- Dispatch order: the unit the next record names, if it starts `w`'s
    section with the identity word (kind 300 since 2026-10-11): the work
    item's or the timer's address. `none` without records, for a record of
    another site (the consumer then mismatches), and for a record without
    the word or with a zero word (a softirq; a capture made before the
    identity existed, where the legacy queue-order rule applies). -/
def peekUnit (w : Worker) : M (Option Nat) := do
  skipAmbient
  match (← get).hidden with
  | some (r :: _) =>
    if r.site != (HiddenSite.sectionStart w).info.id || r.bytes.length < 16 then return none
    let u := recordWordOf r.bytes 1
    return if u == 0 then none else some u
  | _ => return none

/-- Dispatch order: `queue_work` of a unit of worker `w` whose PENDING test
    passed (the caller's: the peer's queue membership, `pendingWork` for a
    device-level unit): the kernel wrote the queue record there, whose first
    word is the unit's address. The address names the unit (`unitPeers`); a
    unit's address never changes while its owner lives, so a re-queue with
    another address is a hidden mismatch. Without records (the domain
    filter) the placeholder is not kept. -/
def recordQueued (w : Worker) (pid : Nat) : M Unit := do
  -- the kernel writes the queue record iff the dispatch set was armed with
  -- KCOV_DISPATCH_ARM_RECORDS (`harness/linux.py` ARM_RECORDS), like the arm
  -- record: without it (captures made before the records) nothing to consume
  if !(← get).armRecords then return
  let bs ← hidden (.queued w)
  let st ← get
  if st.hidden.isNone then return
  let a := recordWordOf bs 0
  match st.unitPeers.find? fun (e : Nat × Nat × Nat) => e.2.1 == w.index && e.2.2 == pid with
  | some (a', _, _) =>
    if a' != a then throw (.hidden s!"{w.symbol} of peer {pid}: queued at address {a}, before at {a'}")
  | none => set { st with unitPeers := st.unitPeers ++ [(a, w.index, pid)] }

/-- Dispatch order: whether the next record is the queue record of the unit
    of worker `w` for `pid`, by the address its earlier queue record gave
    (`unitPeers`). The kernel writes the record iff `queue_work`'s PENDING
    test passed; `process_one_work` clears PENDING when it takes the item,
    before the function's section starts. So a unit the mirror still holds
    queued whose queue record comes next was dequeued by the kernel and is
    being queued a second time: the record is the kernel's statement of the
    test's outcome, and the mirror follows it (w7_multi_tx_2 under eight
    guests, 2026-10-13). `false` without records, for a record of another
    site, or for a unit whose address no record gave yet. -/
def peekQueuedUnit (w : Worker) (pid : Nat) : M Bool := do
  if !(← get).armRecords then return false
  skipAmbient
  let st ← get
  match st.hidden with
  | some (r :: _) =>
    if r.site != (HiddenSite.queued w).info.id || r.bytes.length < 8 then return false
    let some (a, _, _) := st.unitPeers.find? (fun (e : Nat × Nat × Nat) => e.2.1 == w.index && e.2.2 == pid)
      | return false
    return recordWordOf r.bytes 0 == a
  | _ => return false

/-- `queue_work_on` of a device-level unit (one work struct: the encrypt and
    decrypt workers' per-CPU work on the one CPU, `incoming_handshake_work`):
    `test_and_set_bit(WORK_STRUCT_PENDING_BIT)` queues it iff it was not
    pending, with its record; pending until its section starts. A second
    queueing after the kernel's dequeue and before the section
    (`peekQueuedUnit`) would need a second instance of the device-level
    unit, which the mirror does not hold: fail-noisy. -/
def queueDeviceWork (w : Worker) : M Unit := do
  if (← get).pendingWork.contains w.index then
    if ← peekQueuedUnit w 0 then
      unsupported s!"{w.symbol} queued again after its dequeue, before its section (a second instance of a device-level unit)"
    return
  recordQueued w 0
  modify fun st => { st with pendingWork := st.pendingWork ++ [w.index] }

/-- Dispatch order: the queued unit of worker `w` that a dispatch names by
    address `unit`, among `queue` (the mirror's queued peers of that kind).
    Fail-noisy: an address no queue record gave, or a unit whose peer is not
    queued, is a hidden mismatch. -/
def resolveUnit (w : Worker) (unit : Nat) (queue : List Nat) : M Nat := do
  match (← get).unitPeers.find? fun (e : Nat × Nat × Nat) => e.1 == unit && e.2.1 == w.index with
  | some (_, _, pid) =>
    if !queue.contains pid then throw (.hidden s!"{w.symbol}: the dispatched unit is peer {pid}'s, which is not queued")
    return pid
  | none => throw (.hidden s!"{w.symbol}: the dispatched unit {unit} was never queued")

/-- The release of peer `pid` (`kref_release`, peer.c:200-221, then the
    `call_rcu` free): the work structs and timers embedded in the peer go
    with it, so their dispatch identities are retired. A later record at
    one of those addresses belongs to whatever object the allocator put
    there, which starts its own association. -/
def retirePeerUnits (pid : Nat) : M Unit :=
  modify fun st => { st with
    unitPeers := st.unitPeers.filter fun (e : Nat × Nat × Nat) =>
      !((Worker.all.find? (·.index == e.2.1)).any Worker.perPeer && e.2.2 == pid),
    timerUnits := st.timerUnits.filter (·.2.1 != pid) }

/-- `free_netdev` (wg_destruct's end): the device's work structs, and every
    peer's (all released by then), die with it; their pending bits and
    identities are retired, and the next device starts its own. The net
    namespace's `cleanup_net` unit outlives the device. -/
def retireDeviceUnits : M Unit :=
  modify fun st => { st with
    unitPeers := st.unitPeers.filter fun (e : Nat × Nat × Nat) =>
      !((Worker.all.find? (·.index == e.2.1)).any Worker.deviceOwned),
    pendingWork := st.pendingWork.filter fun i => !((Worker.all.find? (·.index == i)).any Worker.deviceOwned),
    timerUnits := [] }

/-- A recorded clock read: the value, a signed 64-bit count of nanoseconds. -/
def hiddenClock (s : HiddenSite) : M Int := do
  let bs ← hidden s
  let u : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0
  return if u ≥ 2 ^ 63 then (u : Int) - (2 ^ 64 : Int) else (u : Int)

/-- A recorded clock read as the C's `s64` (review item 8,
    docs/2026-10-13-review-items-7-8.md section 4): the 8 bytes as a
    little-endian 64-bit word, reinterpreted signed. The age tests
    (`wg_birthdate_has_expired`, timers.h:25-29) compute and compare in this
    type, wrapping as the C's `s64` does. -/
def hiddenClock64 (s : HiddenSite) : M Int64 := do
  let bs ← hidden s
  let u : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0
  return u.toUInt64.toInt64

/-- A recorded `jiffies` (kinds 303, 304, 306) as the C's `unsigned long`:
    an 8-byte little-endian word, 64 bits on x86_64 (review item 8). -/
def hiddenJiffies (s : HiddenSite) : M UInt64 := do
  let bs ← hidden s
  let u : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0
  return u.toUInt64

/-- A recorded `struct timespec64` (16 bytes: `tv_sec`, then `tv_nsec`,
    little-endian signed 64-bit words). -/
def hiddenTimespec (s : HiddenSite) : M Timespec64 := do
  let bs ← hidden s
  if bs.length != 16 then throw (.hidden s!"{s.info.label}: a timespec64 needs 16 bytes")
  let word (b : List UInt8) : Int :=
    let u : Nat := b.foldr (fun b acc => acc * 256 + b.toNat) 0
    if u ≥ 2 ^ 63 then (u : Int) - (2 ^ 64 : Int) else (u : Int)
  return ⟨word (bs.take 8), word (bs.drop 8)⟩

/-- A cut point: consume the head records that come from these cut sites
    (any number, as the cut's own code may or may not draw), with the
    ambient records and pending section stops among them; return the cut
    records' sites, in order. An ambient record (the scheduler's) may lie
    between two cut records: the run continues past it (a contended host
    showed `start_dl_timer` inside a loopback NET_RX section). An allocation
    cut site's records are consumed the same way, but a failed one is
    outside the domain: the cut's code would take an error path the mirror
    does not follow. -/
def skipCutSites (sites : List HiddenSite) : M (List Nat) := do
  let ids := sites.map (·.info.id)
  let allocIds := AllocSite.cuts.map fun s => (HiddenSite.alloc s).info
  let mut taken := []
  -- record-driven (review item 7): every turn consumes one record or returns
  for _ in [0:(← recordBudget)] do
    skipAmbient
    let w ← get
    match w.hidden with
    | some (r :: rest) =>
      if !ids.contains r.site then return taken
      if let some i := allocIds.find? (·.id == r.site) then
        if r.bytes.headD 1 != 1 then unsupported s!"a below-cut allocation failed ({i.label}, {i.file}:{i.line})"
      set { w with hidden := some rest }
      noteNetRxStart r.site
      taken := taken ++ [r.site]
    | _ => return taken
  budgetExhausted "a cut point's records"

def skipCut (sites : List HiddenSite) : M Unit := discard <| skipCutSites sites

/-- A cut point whose consumer draws a fixed number of times on the modeled
    path (`.neighReachTime`: one draw per `neigh_parms_alloc`): with records,
    exactly `n` head records (after ambient ones, and after records of the
    `between` cut sites, which may precede each draw: an armed run's
    below-cut allocations between the draws) come from `site`, and are
    dropped; without records (the domain filter), nothing. -/
def skipCutExactly (site : HiddenSite) (n : Nat) (between : List HiddenSite := []) : M Unit := do
  for _ in [0:n] do
    skipCut between
    skipAmbient
    let w ← get
    match w.hidden with
    | none => return
    | some (r :: rest) =>
      if r.site != site.info.id then
        throw (.hidden s!"expected {site.info.label} (cut, {n} records), the record is site {r.site}")
      set { w with hidden := some rest }
      noteNetRxStart r.site
    | some [] => throw (.hidden s!"expected {site.info.label} (cut, {n} records), no record left")
  skipCut between
  skipAmbient
  if let some (r :: _) := (← get).hidden then
    if r.site == site.info.id then throw (.hidden s!"more than {n} records of {site.info.label}")
/-- The below-cut allocation consumers, as cut sites, for `skipCut`. -/
def allocCuts : List HiddenSite := AllocSite.cuts.map .alloc

/-- One allocation encounter's outcome at an armed site: the record's
    outcome byte (1 ok, 0 NULL; anything else is not a kind-305 outcome). -/
private def allocRecord (s : AllocSite) : M Bool := do
  let bs ← hidden (.alloc s)
  match bs.headD 2 with
  | 1 => return true
  | 0 => return false
  | b => throw (.hidden s!"{s.info.label}: outcome byte {b}, expected 0 or 1")

/-- One allocation encounter's outcome in the domain filter (placeholders):
    ok, unless the steering schedule names the site, in which case its next
    entry decides (a draw is ok; the only value is the fail word). -/
private def allocPlaceholder (s : AllocSite) : M Bool := do
  let w ← get
  match w.steerValues.findIdx? (·.1 == s.info.label) with
  | none =>
    -- the kernel would record this encounter of a named site against no
    -- entry: the schedule must list every encounter
    if w.allocSteered.contains s.info.label then
      unsupported s!"steer: an encounter of {s.info.label} beyond its schedule"
    return true
  | some k =>
    set { w with steerValues := w.steerValues.eraseIdx k }
    match w.steerValues[k]!.2 with
    | none => return true
    | some v =>
      if v.length != 8 || v.any (· != 0) then throw (.hidden s!"steer: {s.info.label} takes draw or the fail word")
      return false

/-- An allocation outcome at this consumer frame (design section 6.1): `ok`,
    or the failure arm.
    - An exact site consumes its declared number of records, in order, and
      stops at a failed one (an `__alloc_skb` site: the `sk_buff`, then the
      data buffer). A missing, unexpected or malformed record is a hidden
      mismatch, as for every choice.
    - A lax site with count 0 answers ok and consumes nothing (A0 found no
      allocation there on this fixture, section 16.2.3): a record of it
      would be left over, failing the run.
    - A site the run did not arm answers ok: the transitional unarmed
      answer (section 6.6), declared in `World.allocArmed`.
    In the domain filter the steering schedule decides (`allocPlaceholder`). -/
def hiddenAlloc (s : AllocSite) : M Bool := do
  let i := s.info
  match i.count with
  | .laxZero => return true
  | .unrecorded => return true   -- never recorded by construction (seccomp, section 3.1)
  | .cut => invariant s!"{i.label} is a below-cut consumer, consumed only at a cut point"
  | .exact n =>
    let w ← get
    let placeholders := w.hidden.isNone && w.hiddenPlaceholders
    if !placeholders && !w.allocArmed.contains i.label then return true   -- unarmed (section 6.6)
    let encounter : M Bool := if placeholders then allocPlaceholder s else allocRecord s
    let mut k := 0
    while k < n do
      if !(← encounter) then return false
      k := k + 1
    return true

/-- Drop the next choice record (after ambient ones) and return its site;
    `none` when none remain (the domain filter, or an exhausted stream). -/
def dropHiddenRecord : M (Option Nat) := do
  skipAmbient
  match (← get).hidden with
  | some (r :: rest) =>
    modify fun s => { s with hidden := some rest }
    noteNetRxStart r.site
    return some r.site
  | _ => return none

def getFile (id : FileId) : M File := do
  match (← getK).files.get? id with
  | some f => return f
  | none => invariant s!"dangling file identity {id}"

def setFile (id : FileId) (f : File) : M Unit :=
  modifyK fun k => { k with files := k.files.insert id f }

def freeFile (id : FileId) : M Unit :=
  modifyK fun k => { k with files := k.files.erase id }

def getCtx (id : CtxId) : M EventfdCtx := do
  match (← getK).ctxs.get? id with
  | some c => return c
  | none => invariant s!"dangling eventfd context {id}"

def setCtx (id : CtxId) (c : EventfdCtx) : M Unit :=
  modifyK fun k => { k with ctxs := k.ctxs.insert id c }

def freeCtx (id : CtxId) : M Unit :=
  modifyK fun k => { k with ctxs := k.ctxs.erase id }

def getInode (id : PipefsInodeId) : M Inode := do
  match (← getK).inodes.get? id with
  | some i => return i
  | none => invariant s!"dangling pipefs inode identity {id}"

def setInode (id : PipefsInodeId) (i : Inode) : M Unit :=
  modifyK fun k => { k with inodes := k.inodes.insert id i }

def getPipe (id : PipeId) : M PipeInodeInfo := do
  match (← getK).pipes.get? id with
  | some p => return p
  | none => invariant s!"dangling pipe identity {id}"

def setPipe (id : PipeId) (p : PipeInodeInfo) : M Unit :=
  modifyK fun k => { k with pipes := k.pipes.insert id p }

def getPage (id : PageId) : M Page := do
  match (← getK).pages.get? id with
  | some p => return p
  | none => invariant s!"dangling page identity {id}"

def setPage (id : PageId) (p : Page) : M Unit :=
  modifyK fun k => { k with pages := k.pages.insert id p }

/-! ## epoll stores (lifetime identities) -/

def getEp (id : EpId) : M Eventpoll := do
  match (← getK).eps.get? id with
  | some e => return e
  | none => invariant s!"dangling eventpoll identity {id}"

def setEp (id : EpId) (e : Eventpoll) : M Unit :=
  modifyK fun k => { k with eps := k.eps.insert id e }

def freeEp (id : EpId) : M Unit :=
  modifyK fun k => { k with eps := k.eps.erase id }

def getEpi (id : EpiId) : M Epitem := do
  match (← getK).epis.get? id with
  | some e => return e
  | none => invariant s!"dangling epitem identity {id}"

def setEpi (id : EpiId) (e : Epitem) : M Unit :=
  modifyK fun k => { k with epis := k.epis.insert id e }

def freeEpi (id : EpiId) : M Unit :=
  modifyK fun k => { k with epis := k.epis.erase id }

def getPwq (id : PwqId) : M EppollEntry := do
  match (← getK).pwqs.get? id with
  | some p => return p
  | none => invariant s!"dangling eppoll_entry identity {id}"

def setPwq (id : PwqId) (p : EppollEntry) : M Unit :=
  modifyK fun k => { k with pwqs := k.pwqs.insert id p }

def freePwq (id : PwqId) : M Unit :=
  modifyK fun k => { k with pwqs := k.pwqs.erase id }

/-! ## Bounds-checked descriptor-table access -/

private def at? (a : Array α) (n : Nat) (what : String) : M α :=
  match a[n]? with
  | some x => return x
  | none => invariant s!"{what}[{n}] beyond max_fds"

/-- `fdt->fd[n]`. -/
def fdtSlot (fdt : Fdtable) (n : Nat) : M (Option FileId) := at? fdt.fd n "fdt->fd"
/-- `test_bit(n, fdt->open_fds)`. -/
def fdtOpen (fdt : Fdtable) (n : Nat) : M Bool := at? fdt.openFds n "fdt->open_fds"
/-- `test_bit(n, fdt->close_on_exec)`. -/
def fdtCloexec (fdt : Fdtable) (n : Nat) : M Bool := at? fdt.closeOnExec n "fdt->close_on_exec"

private def setAt (a : Array α) (n : Nat) (x : α) (what : String) : M (Array α) :=
  if n < a.size then return a.set! n x else invariant s!"{what}[{n}] beyond max_fds"

def setFdtSlot (n : Nat) (v : Option FileId) : M Unit := do
  let t := (← getFiles).fdt
  let fd ← setAt t.fd n v "fdt->fd"
  modifyFdt fun t => { t with fd }
def setFdtOpen (n : Nat) (b : Bool) : M Unit := do
  let t := (← getFiles).fdt
  let openFds ← setAt t.openFds n b "fdt->open_fds"
  modifyFdt fun t => { t with openFds }
def setFdtCloexec (n : Nat) (b : Bool) : M Unit := do
  let t := (← getFiles).fdt
  let closeOnExec ← setAt t.closeOnExec n b "fdt->close_on_exec"
  modifyFdt fun t => { t with closeOnExec }

end Leanux
