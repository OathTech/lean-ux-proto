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
def O_RDWR : UInt32 := 0o2
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

/-! ## Objects -/

abbrev FileId := Nat
abbrev CtxId := Nat

/-- The `struct file_operations` table a file's `f_op` points to. Fixture files
    (console, KCOV, /dev/null) are opened by the harness outside the trace; their
    operations are outside the modeled slice. -/
inductive FopsId where
  | eventfd
  | fixture (name : String)
  deriving Repr, BEq, DecidableEq

/-- What a file's `private_data` points to. -/
inductive PrivateData where
  | eventfdCtx (ctx : CtxId)
  deriving Repr, BEq, DecidableEq

/-- The inode a file's `f_inode` points to: the shared anonymous inode, or a
    fixture file's inode (outside the slice). -/
inductive InodeId where
  | anon
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
  listeners : WG.Listeners := {}
  /-- `peer_counter` (drivers/net/wireguard/peer.c), a global atomic. -/
  peerCounter : Nat := 0
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
  | kmemCacheZallocNode | kmemCacheZallocPeer | dstCacheInit | allocSkb
  deriving Repr, BEq, DecidableEq

structure World where
  k : Kernel
  env : EnvSite → Nat → Bool
  envCalls : List (EnvSite × Nat) := []
  steps : Array Step := #[]
  /-- The caller's buffer (user memory), as written by `copy_to_iter`. -/
  userOut : Option UInt64 := none
  /-- Observation fields beyond the return value: a dump's `device`, or what
      `wg_observe` saw (`datagrams`, `stats`). -/
  extraOut : List (String × Lean.Json) := []
  /-- Peers whose handshake work this system call queued, while the call has
      not slept. The kernel is `CONFIG_PREEMPT_NONE` on one CPU, so their
      worker cannot have run yet. -/
  queuedThisCall : List Nat := []

/-- Why a mirror execution stopped without an observation. -/
inductive Stop where
  /-- The C leaves the modeled domain at `site` (the condition of the last
      recorded decision): a blocking wait, table expansion, a waiter, ... -/
  | outsideDomain (site : String) (what : String)
  /-- The mirror's own state is inconsistent (a dangling identity, an
      out-of-range slot, a NULL `f_op`): a mirror defect, never a C path. -/
  | invariant (what : String)
  deriving Repr

def Stop.message : Stop → String
  | .outsideDomain site what => s!"unsupported at {site}: {what}"
  | .invariant what => s!"mirror invariant violated: {what}"

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

/-- Ask the environment oracle; the site's call count is part of the query. -/
def envOk (site : EnvSite) : M Bool := do
  let w ← get
  let n := (w.envCalls.find? (·.1 == site)).map (·.2) |>.getD 0
  set { w with envCalls := (site, n + 1) :: w.envCalls.filter (·.1 != site) }
  return w.env site n

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
