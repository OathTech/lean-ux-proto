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

/-! ## Environment oracle

Choice points decided by the environment (allocation, user memory) consult
an oracle rather than being excluded by the domain. The harness oracle says
every site succeeds; Linux results outside that assumption are classified as
environment failures by the comparator. -/

inductive EnvSite where
  | kmallocEventfdCtx | idaAlloc | filpAlloc | dAllocPseudo
  | kmallocFdtable | kvmallocFdArray | kvmallocFdBitmaps
  | accessOk | copyToUser | copyFromUser
  | kmemCacheZallocNode | kmemCacheZallocPeer | dstCacheInit | allocSkb | kzallocKeypair
  -- D1 stream C: encrypt_packet's skb surgery
  | skbCowHead | skbCowData | skbToSgvec
  -- D2 stream A: encrypt_packet's `skb_checksum_help` (a cut; its output is
  -- the environment's `Env.checksumHelp`)
  | skbChecksumHelp
  -- P (pipes, design section 5). `allocInode` is the inode-allocation cut:
  -- new_inode_pseudo -> alloc_inode -> alloc_inode_sb, inode_init_always_gfp
  -- and get_next_ino, no decisions (audit M3)
  | allocInode | kzallocPipeInfo | kcallocPipeBufs | allocPipePage | kcallocResizeBufs
  | copyPageToIter | copyPageFromIter | sigqueueAlloc
  deriving Repr, BEq, DecidableEq

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

def Worker.index : Worker → Nat
  | .sendWorker => 0 | .receiveWorker => 1 | .encryptWorker => 2 | .txWorker => 3 | .netRx => 4
  | .decryptWorker => 5
  | .timerRetransmit => 6 | .timerSendKeepalive => 7 | .timerNewHandshake => 8 | .timerZeroKey => 9
  | .clearPeerWorker => 10 | .timerPersistentKeepalive => 11

def Worker.all : List Worker :=
  [.sendWorker, .receiveWorker, .encryptWorker, .txWorker, .netRx, .decryptWorker,
   .timerRetransmit, .timerSendKeepalive, .timerNewHandshake, .timerZeroKey, .clearPeerWorker,
   .timerPersistentKeepalive]

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
  /-- E-A: `wg_cookie_message_consume`'s birthdate of a stored cookie. -/
  | cookieBirthdate
  /-- P (pipes): `current_time` (fs/inode.c:2648), the coarse real-time
      clock read through `ktime_get_coarse_real_ts64` (kind 215), shared by
      all five callers on the pipe paths (design section 3). -/
  | currentTime
  deriving Repr, BEq, DecidableEq

inductive SiteRole where
  | mirror | cut | ambient
  deriving Repr, BEq, DecidableEq

structure HiddenSiteInfo where
  /-- The number the check passes for records of this site. -/
  id : Nat
  label : String
  /-- `random`, `clock`, `section`, `resched`, `timer` (kind 303) or
      `advance` (kind 304): the interception point's kind. -/
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
    102-113 in the D3 range. -/
def Worker.sectionId (w : Worker) : Nat :=
  if w.index < 6 then 40 + 2 * w.index else 102 + 2 * (w.index - 6)

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
  | .sectionStart w => ⟨w.sectionId, s!"section_start:{w.symbol}", "section", w.symbol, 0, 8, .mirror⟩
  | .sectionStop w => ⟨w.sectionId + 1, s!"section_stop:{w.symbol}", "section", w.symbol, 1, 8, .mirror⟩
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
  | .modTimerArm => ⟨100, "mod_timer_arm", "timer", "drivers/net/wireguard/timers.c", 37, 16, .mirror⟩
  | .timeAdvance => ⟨101, "time_advance", "advance", "fs/ioctl.c", 51, 16, .mirror⟩
  -- P (pipes, design section 3): id 18 is free on main and on every task
  -- branch (E-A uses 64-69, A 70-99); the records are consumed in sequence
  -- order by whichever of the five callers runs
  | .currentTime => ⟨18, "current_time", "clock", "fs/inode.c", 2648, 16, .mirror⟩

def HiddenSite.all : List HiddenSite :=
  [.initEphemeral, .respEphemeral, .tai64nNow, .indexDraw, .resetLastSent, .birthdateExpired, .initLastSent,
   .initLastSentAgain, .respLastSent, .respLastSentAgain, .floodNow, .consumptionNow, .deriveKeysBirthdate,
   .retransmitJitter, .walltimeLastHandshake, .ipIdentReserve, .ipIdentKey, .icmpCredit, .flowHashSecret, .schedDlTimer]
  ++ Worker.all.flatMap (fun w => [.sectionStart w, .sectionStop w])
  ++ [.reschedReceive, .reschedEncrypt, .reschedTx, .reschedDecrypt, .newHandshakeJitter, .walltimeLastHandshakeData,
      .cookieBirthdate]
  ++ [.modTimerArm, .timeAdvance]
  ++ [.currentTime]

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
  /-- The outer DS field `send4`/`send6` are given (`PACKET_CB(skb)->ds`;
      0 for handshake messages). Not observed today: the fixture reads no
      TOS. -/
  ds : Nat := 0
  deriving Repr, BEq

/-- A datagram at the fixture's sender socket, with its source as
    `recvfrom` reports it (D2: wg0's own datagrams and delivered inner
    packets share the socket). -/
structure InboxDatagram where
  family : Nat
  addr : Nat
  port : Nat
  bytes : List UInt8
  deriving Repr, BEq

structure World where
  k : Kernel
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
      fixture's UDP listeners and at its sender, which `wg_observe` drains. -/
  listenerV4 : List (List UInt8) := []
  listenerV6 : List (List UInt8) := []
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
  /-- D3: the timer sections the environment ran in this operation, by
      callback symbol, for the trace's `fired:<symbol>` expectations
      (`Env.runTimerSection`). -/
  fired : Array String := #[]

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
  modify fun w => { w with steps := w.steps.push { decision := d, outcome } }
  return outcome

/-- Record a C value comparison: its outcome and the two values the C
    compares at the condition. The check matches them against
    `KCOV_TRACE_CMP` records at the condition line. -/
def branchCmp (d : Decision) (outcome : Bool) (a b : Int) : M Bool := do
  modify fun w => { w with steps := w.steps.push { decision := d, outcome, operands := some (a, b) } }
  return outcome

/-- Record a C value comparison at a declared operand exclusion (a call site
    whose operand is a guest-wide value the mirror does not model; see
    `OperandExclusion`): the outcome, which the contract fixes, without the
    operands. The check requires Linux's comparison at the declared call site. -/
def branchCmpExcluded (d : Decision) (outcome : Bool) (x : OperandExclusion) : M Bool := do
  modify fun w => { w with steps := w.steps.push { decision := d, outcome, excluded := some x } }
  return outcome

/-- Ask the environment oracle; the site's call count is part of the query. -/
def envOk (site : EnvSite) : M Bool := do
  let w ← get
  let n := (w.envCalls.find? (·.1 == site)).map (·.2) |>.getD 0
  set { w with envCalls := (site, n + 1) :: w.envCalls.filter (·.1 != site) }
  return w.env site n

/-- Drop ambient records at the head of the current operation's records,
    and pending section stops (each consumes its one pending entry). -/
def skipAmbient : M Unit := do
  let w ← get
  if let some rs := w.hidden then
    let ambient := HiddenSite.all.filter (·.info.role == .ambient) |>.map (·.info.id)
    let rec go (rs : List HiddenRecord) (pending : List Nat) : List HiddenRecord × List Nat :=
      match rs with
      | r :: rest =>
        if ambient.contains r.site then go rest pending
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
    return r.bytes.take i.len

/-- The site of the next record to consume (after ambient ones), without
    consuming it: how the environment's scheduler reads a recorded
    scheduling choice. `none` without records (the domain filter). -/
def peekHiddenSite : M (Option Nat) := do
  skipAmbient
  return match (← get).hidden with
    | some (r :: _) => some r.site
    | _ => none

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
    showed `start_dl_timer` inside a loopback NET_RX section). -/
def skipCutSites (sites : List HiddenSite) : M (List Nat) := do
  let ids := sites.map (·.info.id)
  let mut taken := []
  for _ in [0:4096] do
    skipAmbient
    let w ← get
    match w.hidden with
    | some (r :: rest) =>
      if !ids.contains r.site then return taken
      set { w with hidden := some rest }
      taken := taken ++ [r.site]
    | _ => return taken
  invariant "a cut point consumed more than 4096 records"

def skipCut (sites : List HiddenSite) : M Unit := discard <| skipCutSites sites

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
