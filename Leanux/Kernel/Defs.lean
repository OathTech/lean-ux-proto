import Leanux.Kernel.Decision
import Leanux.WG.Types
import Std.Data.TreeMap
import Std.Data.TreeSet
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

/-- The `struct file_operations` table a file's `f_op` points to. Fixture files
    (console, KCOV, /dev/null) are opened by the harness outside the trace; their
    operations are outside the modeled slice. -/
inductive FopsId where
  | eventfd
  /-- `pipefifo_fops` (fs/pipe.c:1232-1241). -/
  | pipefifo
  | fixture (name : String)
  deriving Repr, BEq, DecidableEq

/-- What a file's `private_data` points to. -/
inductive PrivateData where
  | eventfdCtx (ctx : CtxId)
  /-- A pipe file's `private_data` is its `pipe_inode_info` (fs/pipe.c:947,957). -/
  | pipe (id : PipeId)
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
  /-- `f_ep`: the file is linked into an epoll set (never, in this slice). -/
  fEp : Bool := false
  /-- `f_pipe` (include/linux/fs.h:1092), written at fs/pipe.c:948,958 and
      read only by `pipe_poll`. -/
  fPipe : Nat := 0
  deriving Repr, BEq

/-- `struct eventfd_ctx`. `wqh` is represented only by its waiter count; the
    single-threaded domain has no waiters. `id` is the `eventfd_ida` number. -/
structure EventfdCtx where
  kref : Nat
  count : UInt64
  flags : UInt32
  /-- `none` until `ctx->id = ida_alloc(...)` (eventfd.c:401): kmalloc leaves it unset. -/
  id : Option Int
  waiters : Nat := 0
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
    dereference. The mutex and the wait queues are cuts (one task, no
    waiters); `watch_queue` and `note_loss` do not exist in this build;
    `fasync_readers`/`fasync_writers` are NULL lists, kept as booleans. -/
structure PipeInodeInfo where
  head : UInt32 := 0
  tail : UInt32 := 0
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
  -- L: wg_newlink's allocations (device.c:325-367) and wg_ratelimiter_init's
  -- (ratelimiter.c:164-185); `register_netdevice` (A's domain: assumed
  -- success in the harness)
  | pubkeyHashtableAlloc | indexHashtableAlloc | allocWorkqueue | packetQueueInit
  | ratelimiterCache | ratelimiterTable | registerNetdevice
  -- P (pipes, design section 5). `allocInode` is the inode-allocation cut:
  -- new_inode_pseudo -> alloc_inode -> alloc_inode_sb, inode_init_always_gfp
  -- and get_next_ino, no decisions (audit M3)
  | allocInode | kcallocResizeBufs
  | copyPageToIter | copyPageFromIter | sigqueueAlloc
  -- E-B arm C: wg_ratelimiter_allow's per-entry kmem_cache_alloc (ratelimiter.c:138)
  | ratelimiterEntry
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
  -- the pipe paths' direct sites (b-task; A section 19.6, integration)
  | kzallocPipeInfo | kcallocPipeBufs | allocPipePage
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

def AllocSite.all : List AllocSite :=
  [.kmallocEventfdCtx, .filpAlloc, .dAllocPseudo, .kmallocFdtable, .kvmallocFdArray, .kvmallocFdBitmaps,
   .kmemCacheZallocPeer, .allocNode190, .allocNode205, .allocNode234, .kzallocKeypair,
   .sendBufSkb, .replySkb, .keepaliveSkb, .skbCowHead, .skbChecksumHelp, .skbCowDataTx, .skbCowDataRx,
   .nlmsgNew, .netlinkAllocLargeSkb, .sockAllocSendPskb, .netlinkDump, .netlinkTrim,
   .kzallocPipeInfo, .kcallocPipeBufs, .allocPipePage, .dAllocSlabDebugfs, .allocUeventSkb]

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
  | modTimerArm | timeAdvance
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
  /-- An allocation outcome (kind 305) at a consumer frame: ids 70-99 are
      A's (docs/2026-10-05-a-alloc.md, section 6.1). -/
  | alloc (s : AllocSite)
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
  | .dstCacheRefreshTs => ⟨151, "dst_cache_refresh_ts", "jiffies", "net/core/dst_cache.c", 63, 8, .mirror⟩
  | .alloc s => let i := s.info
    ⟨70 + i.index, i.label, "alloc", i.file, i.line, 40, if i.count == .cut then .cut else .mirror⟩
  -- P (pipes, design section 3): id 18 is free on main and on every task
  -- branch (E-A uses 64-69, A 70-99); the records are consumed in sequence
  -- order by whichever of the five callers runs
  | .currentTime => ⟨18, "current_time", "clock", "fs/inode.c", 2648, 16, .mirror⟩
  -- E-B (ids 130-139, outside E-A's 64-69, A's 70-99, D3's 100-115 and L's
  -- 120-126; P's current_time is 18). receive.c:115 is read only in the
  -- discarded flood section; cookie.c:190 is the cookie reply's nonce.
  | .underLoadNow => ⟨130, "under_load_now", "clock", "drivers/net/wireguard/receive.c", 115, 8, .mirror⟩
  | .cookieNonce => ⟨131, "cookie_nonce", "random", "drivers/net/wireguard/cookie.c", 190, 24, .mirror⟩
  | .ratelimiterNow => ⟨132, "ratelimiter_now", "clock", "drivers/net/wireguard/ratelimiter.c", 121, 8, .mirror⟩
  | .ratelimiterInsertNow => ⟨133, "ratelimiter_insert_now", "clock", "drivers/net/wireguard/ratelimiter.c", 146, 8, .mirror⟩
  -- W5+W6 (ids 140-149)
  | .inetEhashSecret => ⟨140, "inet_ehash_secret", "random", "net/ipv4/inet_hashtables.c", 36, 4, .cut⟩

def HiddenSite.all : List HiddenSite :=
  [.initEphemeral, .respEphemeral, .tai64nNow, .indexDraw, .resetLastSent, .birthdateExpired, .initLastSent,
   .initLastSentAgain, .respLastSent, .respLastSentAgain, .floodNow, .consumptionNow, .deriveKeysBirthdate,
   .retransmitJitter, .walltimeLastHandshake, .ipIdentReserve, .ipIdentKey, .icmpCredit, .flowHashSecret, .schedDlTimer]
  ++ Worker.all.flatMap (fun w => [.sectionStart w, .sectionStop w])
  ++ [.reschedReceive, .reschedEncrypt, .reschedTx, .reschedDecrypt, .newHandshakeJitter, .walltimeLastHandshakeData,
      .cookieBirthdate]
  ++ [.modTimerArm, .timeAdvance]
  ++ (Worker.all.filter fun w => w.timer?.isNone && w != .netRx).map .queued
  ++ [.cookieSecretBirthdate, .cookieSecret, .pubkeyHashKey, .ratelimiterKey, .ratelimiterGcNow, .udpPortDraw,
      .neighReachTime]
  ++ [.dstCacheResetTs, .dstCacheRefreshTs, .reschedNetnsCleanup]
  ++ AllocSite.all.map .alloc
  ++ [.currentTime]
  ++ [.underLoadNow, .cookieNonce, .ratelimiterNow, .ratelimiterInsertNow]
  ++ [.inetEhashSecret]

/-- The resched site of a worker's `cond_resched`, for the workers that
    have one on the modeled paths. -/
def Worker.resched? : Worker → Option HiddenSite
  | .receiveWorker => some .reschedReceive
  | .encryptWorker => some .reschedEncrypt
  | .txWorker => some .reschedTx
  | .decryptWorker => some .reschedDecrypt
  | _ => none

def SiteRole.name : SiteRole → String
  | .mirror => "mirror" | .cut => "cut" | .ambient => "ambient"

/-- One recorded value: the site's number and its bytes (whole words). -/
structure HiddenRecord where
  site : Nat
  bytes : List UInt8
  deriving Repr, BEq

/-- Timing facts the environment supplies (`Leanux/Env.lean`); the mirror has
    no clock. D3 (docs/2026-10-05-d3-timers.md, section 5.3): the bounds of
    the firing window, in ticks. A timer section is accepted iff its timer is
    pending with `expires < J_hi`, where `J_hi` is the advance's `jiffies`
    after plus `advanceWait` inside `wg_advance`, and the last recorded
    `jiffies` plus `traceBound` plus `advanceWait` at the other idle points. -/
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
  /-- Workers that switched away at a `cond_resched` in this operation
      (worker indices), and the section stops of their runs that ended in
      the mirror before Linux recorded them (site ids): see `Env.runWorker`. -/
  yieldedWorkers : List Nat := []
  pendingStops : List Nat := []
  /-- W7 stream B (docs/2026-10-06-w4-w7-transmit-bulk.md, 5.4, phase 1):
      the workers whose sections are open in the mirror, innermost last
      (worker index, the tx worker's peer), for the commuting detector in
      `Env.condResched`. -/
  openWorkers : List (Nat × Option Nat) := []
  /-- Dispatch order (docs/2026-10-11-dispatch-order.md): each work unit's
      address from its queue record (`unitPeers`: address, worker index,
      peer, 0 for a device-level unit); each armed timer's address from its
      arm record (`timerUnits`: address, peer, timer); and the device-level
      work units whose `WORK_STRUCT_PENDING` bit is set (`pendingWork`:
      worker indices), set by a `queue_work` that queues and cleared when
      the unit's section starts (`process_one_work`). A per-peer unit's
      pending bit is its membership of its queue. -/
  unitPeers : List (Nat × Nat × Nat) := []
  timerUnits : List (Nat × Nat × WG.PeerTimer) := []
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
  /-- W7 stream H: the NET_RX sections consumed so far in the operation and
      the one open now (0: none), stamped on every step (`Step.section`). -/
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
      last `jiffies` a record told (kinds 303 and 304), 64-bit, never
      truncated; `none` before the first. -/
  jiffiesLast : Option Nat := none
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
      control-flow mismatch. A flood's invalid tail sets it to that tail's
      last under-load read (`floodTailEffect`). -/
  lastUnderLoad : Option Int := none

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
def getFiles : M FilesStruct := return (← getK).task.files
def modifyFiles (f : FilesStruct → FilesStruct) : M Unit :=
  modifyK fun k => { k with task := { k.task with files := f k.task.files } }
def modifyFdt (f : Fdtable → Fdtable) : M Unit :=
  modifyFiles fun fs => { fs with fdt := f fs.fdt }

/-- Record a C decision point with its outcome and return the outcome. -/
def branch (d : Decision) (outcome : Bool) : M Bool := do
  modify fun w => { w with steps := w.steps.push { decision := d, outcome, netRx := w.netRxSection } }
  return outcome

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

/-- Drop ambient records at the head of the current operation's records,
    and pending section stops (each consumes its one pending entry). -/
def skipAmbient : M Unit := do
  let w ← get
  if let some rs := w.hidden then
    let rec go (rs : List HiddenRecord) (pending : List Nat) : List HiddenRecord × List Nat :=
      match rs with
      | r :: rest =>
        if HiddenSite.passive r.site then go rest pending
        else if pending.contains r.site then go rest (pending.erase r.site)
        else (rs, pending)
      | [] => ([], pending)
    let (rest, pendingStops) := go rs w.pendingStops
    set { w with hidden := some rest, pendingStops }

/-- Consume the next choice record, which must come from `s`. -/
def hidden (s : HiddenSite) : M (List UInt8) := do
  skipAmbient
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

/-- `queue_work_on` of a device-level unit (one work struct: the encrypt and
    decrypt workers' per-CPU work on the one CPU, `incoming_handshake_work`):
    `test_and_set_bit(WORK_STRUCT_PENDING_BIT)` queues it iff it was not
    pending, with its record; pending until its section starts. -/
def queueDeviceWork (w : Worker) : M Unit := do
  if (← get).pendingWork.contains w.index then return
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

/-- A recorded clock read: the value, a signed 64-bit count of nanoseconds. -/
def hiddenClock (s : HiddenSite) : M Int := do
  let bs ← hidden s
  let u : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0
  return if u ≥ 2 ^ 63 then (u : Int) - (2 ^ 64 : Int) else (u : Int)

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
  for _ in [0:4096] do
    skipAmbient
    let w ← get
    match w.hidden with
    | some (r :: rest) =>
      if !ids.contains r.site then return taken
      if let some i := allocIds.find? (·.id == r.site) then
        if r.bytes.headD 1 != 1 then unsupported s!"a below-cut allocation failed ({i.label}, {i.file}:{i.line})"
      set { w with hidden := some rest }
      taken := taken ++ [r.site]
    | _ => return taken
  invariant "a cut point consumed more than 4096 records"

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
    return some r.site
  | _ => return none

/-- E-B, the producer-side discard before a flood's receive-worker section
    (docs/2026-10-05-e-dos.md §4.1): drop head records whose site is in
    `allowed` (the fixture's sends' cut draws and NET_RX brackets) until the
    next record is `stop`, or the stream is exhausted. A record outside
    `allowed` is a hidden mismatch (something the mirror would have modeled
    where it stands). Bounded by the operation's record count. -/
def discardFloodRecords (stop : Nat) (allowed : List Nat) : M Nat := do
  let mut dropped := 0
  for _ in [0:4000000] do
    match ← peekHiddenSite with
    | some s =>
      if s == stop then return dropped
      if !allowed.contains s then
        throw (.hidden s!"flood: a modeled record (site {s}) inside the discarded flood region (a mid-flood injection)")
      _ ← dropHiddenRecord
      dropped := dropped + 1
    | none => return dropped
  throw (.hidden "flood: the record stream did not drain")

/-- The effect contract of a flood's invalid tail (the review's 3.4): the
    packets the receive worker drops at the MAC1 check after the leading
    valids, up to the section's `stop`. Each one runs
    `wg_receive_handshake_packet` to the MAC check: with the counter at or
    over the threshold it saves the clock (`under_load_now`, receive.c:115);
    below it, with `last_under_load` set, it reads the clock for the decay
    (`birthdate_has_expired`, receive.c:117) and resets `last_under_load` when
    the decay has expired (:119); then `cond_resched` (`resched_receive`). The
    contract folds exactly those records, in order, into the new
    `last_under_load`, from `last` (the value the leading valids left): no
    other state changes (a dropped packet is freed; `handshake_queue_len` is
    decremented per packet, to 0 at the drain, which the caller sets). Any
    other record is a hidden mismatch (a mid-flood injection, or a decay read
    with no saved time). Returns the new value and whether an under-load read
    occurred (the flood crossed the threshold). -/
def floodTailEffect (stop : Nat) (cuts : List Nat) (last : Option Int) : M (Option Int × Bool) := do
  let underLoad := (HiddenSite.underLoadNow).info.id
  let decay := (HiddenSite.birthdateExpired).info.id
  let resched := (HiddenSite.reschedReceive).info.id
  let mut last := last
  let mut crossed := false
  for _ in [0:4000000] do
    match ← peekHiddenSite with
    | some s =>
      if s == stop then return (last, crossed)
      if s == underLoad then
        last := some (← hiddenClock .underLoadNow)
        crossed := true
      else if s == decay then
        let some saved := last
          | throw (.hidden "flood: a decay clock read with no saved under-load time (a mid-flood injection)")
        let now ← hiddenClock .birthdateExpired
        if saved + 1000000000 ≤ now then last := none   -- wg_birthdate_has_expired(last_under_load, 1)
      else if s == resched || cuts.contains s then
        _ ← dropHiddenRecord
      else
        throw (.hidden s!"flood: a modeled record (site {s}) inside the discarded flood region (a mid-flood injection)")
    | none => return (last, crossed)
  throw (.hidden "flood: the record stream did not drain")

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
