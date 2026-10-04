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
  /-- `peer_counter` (drivers/net/wireguard/peer.c), a global atomic. -/
  peerCounter : Nat := 0
  /-- `keypair_counter` (drivers/net/wireguard/noise.c), a global atomic. -/
  keypairCounter : Nat := 0
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
    stream 1): the work item's or softirq's function. -/
inductive Worker where
  | sendWorker | receiveWorker | encryptWorker | txWorker | netRx | decryptWorker
  deriving Repr, BEq, DecidableEq

def Worker.symbol : Worker → String
  | .sendWorker => "wg_packet_handshake_send_worker"
  | .receiveWorker => "wg_packet_handshake_receive_worker"
  | .encryptWorker => "wg_packet_encrypt_worker"
  | .txWorker => "wg_packet_tx_worker"
  | .netRx => "net_rx_action"
  | .decryptWorker => "wg_packet_decrypt_worker"

def Worker.index : Worker → Nat
  | .sendWorker => 0 | .receiveWorker => 1 | .encryptWorker => 2 | .txWorker => 3 | .netRx => 4
  | .decryptWorker => 5

def Worker.all : List Worker := [.sendWorker, .receiveWorker, .encryptWorker, .txWorker, .netRx, .decryptWorker]

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
  deriving Repr, BEq, DecidableEq

inductive SiteRole where
  | mirror | cut | ambient
  deriving Repr, BEq, DecidableEq

structure HiddenSiteInfo where
  /-- The number the check passes for records of this site. -/
  id : Nat
  label : String
  /-- `random`, `clock`, `section` or `resched` (the interception point's
      kind). -/
  kind : String
  /-- The consumer frame: the first frame of the call chain outside the
      random and clock helpers. -/
  file : String
  line : Nat
  /-- Bytes recorded (the record carries whole words, zero-padded). -/
  len : Nat
  role : SiteRole

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
  | .sectionStart w => ⟨40 + 2 * w.index, s!"section_start:{w.symbol}", "section", w.symbol, 0, 8, .mirror⟩
  | .sectionStop w => ⟨41 + 2 * w.index, s!"section_stop:{w.symbol}", "section", w.symbol, 1, 8, .mirror⟩
  | .reschedReceive => ⟨60, "resched:wg_packet_handshake_receive_worker", "resched", "drivers/net/wireguard/receive.c", 216, 8, .mirror⟩
  | .reschedEncrypt => ⟨61, "resched:wg_packet_encrypt_worker", "resched", "drivers/net/wireguard/send.c", 307, 8, .mirror⟩
  | .reschedTx => ⟨62, "resched:wg_packet_tx_worker", "resched", "drivers/net/wireguard/send.c", 283, 8, .mirror⟩
  | .reschedDecrypt => ⟨63, "resched:wg_packet_decrypt_worker", "resched", "drivers/net/wireguard/receive.c", 505, 8, .mirror⟩
  -- `get_random_u32_below(REKEY_TIMEOUT_JITTER_MAX_JIFFIES)` in
  -- wg_timers_data_sent (timers.c:150), the inline u8 path as for
  -- `.retransmitJitter`. TO-CONFIRM: the consumer frame in this build
  -- (wg_timers_data_sent may be inlined into its caller).
  | .newHandshakeJitter => ⟨16, "new_handshake_jitter", "random", "drivers/net/wireguard/timers.c", 150, 1, .mirror⟩

def HiddenSite.all : List HiddenSite :=
  [.initEphemeral, .respEphemeral, .tai64nNow, .indexDraw, .resetLastSent, .birthdateExpired, .initLastSent,
   .initLastSentAgain, .respLastSent, .respLastSentAgain, .floodNow, .consumptionNow, .deriveKeysBirthdate,
   .retransmitJitter, .walltimeLastHandshake, .ipIdentReserve, .ipIdentKey, .icmpCredit, .flowHashSecret, .schedDlTimer]
  ++ Worker.all.flatMap (fun w => [.sectionStart w, .sectionStop w])
  ++ [.reschedReceive, .reschedEncrypt, .reschedTx, .reschedDecrypt, .newHandshakeJitter]

/-- The resched site of a worker's `cond_resched`, for the workers that
    have one on the modeled paths. -/
def Worker.resched? : Worker → Option HiddenSite
  | .receiveWorker => some .reschedReceive
  | .encryptWorker => some .reschedEncrypt
  | .txWorker => some .reschedTx
  | .decryptWorker => some .reschedDecrypt
  | .sendWorker | .netRx => none

def SiteRole.name : SiteRole → String
  | .mirror => "mirror" | .cut => "cut" | .ambient => "ambient"

/-- One recorded value: the site's number and its bytes (whole words). -/
structure HiddenRecord where
  site : Nat
  bytes : List UInt8
  deriving Repr, BEq

/-- Timing facts the environment supplies (`Leanux/Env.lean`); the mirror has
    no clock. -/
structure Timing where
  /-- Whether a timer armed now for this many seconds can expire before the
      trace ends. -/
  timerMayExpire : Nat → Bool

/-- A datagram wg0's socket sent (`wg_socket_send_buffer_to_peer`, a cut
    point): the endpoint's family, address and port, and the bytes. -/
structure SentDatagram where
  family : Nat
  addr : Nat
  port : Nat
  bytes : List UInt8
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
  /-- The caller's buffer (user memory), as written by `copy_to_iter`. -/
  userOut : Option UInt64 := none
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
  /-- A steered trace's schedule (site label, value or a draw), which the
      placeholders follow: the domain filter's verdict is then exact for the
      steered sites. -/
  steerValues : List (String × Option (List UInt8)) := []
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
      | "clock" => le (1000000000000 + n * 1000000000) i.len
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

/-- A cut point: consume the head records that come from these cut sites
    (any number, as the cut's own code may or may not draw). -/
def skipCut (sites : List HiddenSite) : M Unit := do
  skipAmbient
  let w ← get
  if let some rs := w.hidden then
    let ids := sites.map (·.info.id)
    let rest := rs.dropWhile fun r => ids.contains r.site
    set { w with hidden := some rest }
    if rest.length != rs.length then skipAmbient

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
