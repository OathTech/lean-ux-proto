import Leanux.Kernel.Decision

/-!
# Mirror state and execution monad

State is shaped like the configured C structures (Linux 6.12.110, x86-64):
one structure per C struct, pointers replaced by abstract identities, and each
object owned once in an identity-keyed store. Descriptor slots hold identities,
not ownership. Field names follow the C.
-/

namespace Leanux

/-! ## Constants (x86-64 UAPI and include/linux/fs.h) -/

def O_ACCMODE : UInt32 := 0o3
def O_RDWR : UInt32 := 0o2
def O_APPEND : UInt32 := 0o2000
def O_NONBLOCK : UInt32 := 0o4000
def O_DSYNC : UInt32 := 0o10000
def FASYNC : UInt32 := 0o20000
def O_DIRECT : UInt32 := 0o40000
def O_CLOEXEC : UInt32 := 0o2000000
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

/-- `f_op` together with `private_data`: which operations table the file uses.
    Fixture files (console, KCOV, /dev/null) are opened by the harness outside
    the trace; their operations are outside the modeled slice. -/
inductive FileKind where
  | eventfd (ctx : CtxId)
  | fixture (name : String)
  deriving Repr, BEq, DecidableEq

/-- `struct file`. `fCount` is `f_count`. Fixture files carry references held
    outside the trace (other processes, the KCOV mapping), so trace operations
    never drop them to zero; the exact external count is not observable. -/
structure File where
  fFlags : UInt32
  fMode : UInt32
  fCount : Nat
  kind : FileKind
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

/-- `struct fdtable`. Slots and bits beyond `maxFds` are never consulted.
    `full_fds_bits` is derived from `openFds` (see `fullWord`). -/
structure Fdtable where
  maxFds : Nat
  fd : Nat → Option FileId
  openFds : Nat → Bool
  closeOnExec : Nat → Bool

/-- `struct files_struct`. `count` is the number of tasks sharing it. -/
structure FilesStruct where
  count : Nat
  resizeInProgress : Bool
  nextFd : Nat
  fdt : Fdtable
  /-- Identity of the `files->fdt` table; `expand_fdtable` would replace it. -/
  fdtGeneration : Nat := 0

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

/-- Whole-kernel mirror state. `nrFiles`/`maxFiles` mirror the system-wide
    `nr_files` percpu counter and `files_stat.max_files`, and
    `anonInodeInodeErr` whether the boot-time `anon_inode_inode` is an error
    pointer; the runner supplies these environment facts. -/
structure Kernel where
  task : Task
  files : FileId → Option File
  nextFile : FileId
  ctxs : CtxId → Option EventfdCtx
  nextCtx : CtxId
  idaUsed : Nat → Bool
  nrFiles : Nat
  maxFiles : Nat
  anonInodeInodeErr : Bool

/-! ## Environment oracle

Choice points decided by the environment (allocation, user memory) consult
an oracle rather than being excluded by the domain. The harness oracle says
every site succeeds; Linux results outside that assumption are classified as
environment failures by the comparator. -/

inductive EnvSite where
  | kmallocEventfdCtx | idaAlloc | filpAlloc | dAllocPseudo
  | accessOk | copyToUser | copyFromUser
  deriving Repr, BEq, DecidableEq

structure World where
  k : Kernel
  env : EnvSite → Nat → Bool
  envCalls : List (EnvSite × Nat) := []
  steps : Array Step := #[]
  /-- Bytes the syscall stored into the caller's buffer, if any. -/
  userOut : Option UInt64 := none

/-- The mirror monad. An `Except` error is an explicit, fail-noisy
    `unsupported` outcome: the C would leave the modeled domain here. -/
abbrev M := StateT World (Except String)

def unsupported (what : String) : M α := throw s!"unsupported: {what}"

def getK : M Kernel := return (← get).k
def modifyK (f : Kernel → Kernel) : M Unit := modify fun w => { w with k := f w.k }
def getFiles : M FilesStruct := return (← getK).task.files
def modifyFiles (f : FilesStruct → FilesStruct) : M Unit :=
  modifyK fun k => { k with task := { k.task with files := f k.task.files } }
def modifyFdt (f : Fdtable → Fdtable) : M Unit :=
  modifyFiles fun fs => { fs with fdt := f fs.fdt }

/-- Record a C decision point with its outcome and return the outcome. -/
def branch (d : Decision) (outcome : Bool) : M Bool := do
  modify fun w => { w with steps := w.steps.push ⟨d, outcome⟩ }
  return outcome

/-- Ask the environment oracle; the site's call count is part of the query. -/
def envOk (site : EnvSite) : M Bool := do
  let w ← get
  let n := (w.envCalls.find? (·.1 == site)).map (·.2) |>.getD 0
  set { w with envCalls := (site, n + 1) :: w.envCalls.filter (·.1 != site) }
  return w.env site n

def getFile (id : FileId) : M File := do
  match (← getK).files id with
  | some f => return f
  | none => unsupported s!"dangling file identity {id}"

def setFile (id : FileId) (f : File) : M Unit :=
  modifyK fun k => { k with files := fun n => if n = id then some f else k.files n }

def getCtx (id : CtxId) : M EventfdCtx := do
  match (← getK).ctxs id with
  | some c => return c
  | none => unsupported s!"dangling eventfd context {id}"

def setCtx (id : CtxId) (c : EventfdCtx) : M Unit :=
  modifyK fun k => { k with ctxs := fun n => if n = id then some c else k.ctxs n }

end Leanux
