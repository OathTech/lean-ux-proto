import Leanux.FS.Eventfd
import Leanux.FS.ReadWrite
import Leanux.FS.Fcntl
import Leanux.FS.Close
import Leanux.FS.Fput
import Leanux.FS.Eventpoll
import Leanux.FS.Inode
import Leanux.FS.PipeCreate
import Leanux.Env
import Leanux.WG.NetlinkDump
import Leanux.Seccomp.Syscalls

/-!
# System call entry and return to user mode

`SYSCALL_DEFINE` wrappers take `unsigned int` descriptors: the low 32 bits of
the argument register. On return to user mode, `task_work_run` runs queued
`____fput` work (file_table.c:496-500), which calls `__fput`. The entry and
exit machinery itself (arch/x86/entry, kernel/entry/common.c,
kernel/task_work.c) is a cut point.
-/

namespace Leanux

/-- `(unsigned int)` of a 64-bit argument register holding a sign-extended
    32-bit value. -/
def uint (n : Int) : Nat := (n % 4294967296).toNat

inductive Syscall where
  | eventfd2 (count flags : UInt32)
  | dup (fildes : Nat)
  | dup3 (oldfd newfd : Nat) (flags : UInt32)
  | close (fd : Nat)
  /-- `read(fd, buf, count)` into a valid caller buffer. -/
  | read (fd count : Nat)
  /-- `write(fd, buf, count)`; `buf` is the caller's buffer (the trace's
      pattern, Runner `writeBuffer`). -/
  | write (fd count : Nat) (buf : ByteArray)
  /-- `pipe2(fildes, flags)` with a valid `fildes` (P). -/
  | pipe2 (flags : UInt32)
  | fcntl (fd : Nat) (cmd : FcntlCmd) (arg : UInt64)
  /-- epoll (docs/2026-10-12-epoll-design.md, section 6): `epoll_create1(flags)`;
      `epoll_ctl(epfd, op, fd, &{events, data})` with `op` and `fd` the
      kernel's `int`s (the low 32 bits of the wire's u32, signed);
      `epoll_wait(epfd, events, maxevents, timeout)` into the guest's buffer. -/
  | epollCreate1 (flags : UInt32)
  | epollCtl (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64)
  | epollWait (epfd : Nat) (maxevents timeout : Int)
  /-- `sendmsg` of WG_CMD_SET_DEVICE on the fixture's generic-netlink socket,
      then `recvmsg` of the acknowledgement: the result is its error code. -/
  | wgSet (attrs : WG.DeviceAttrs)
  /-- `sendmsg` of a WG_CMD_GET_DEVICE dump request, then `recvmsg` of the
      dump; the device state goes to `extraOut`. -/
  | wgGet (device : WG.DeviceRef)
  /-- W2 (docs/2026-10-06-w1-w2-netlink.md, 4.2): the stepped dump on the
      fixture's second generic-netlink socket (fd 8): `sendmsg` of the dump
      request (the start and the first dump call run inside it; result 0),
      and one `recvmsg(MSG_DONTWAIT)` of one chunk or acknowledgement, whose
      messages go to `extraOut`. -/
  | wgGetStart (device : WG.DeviceRef)
  | wgGetRecv
  /-- `ioctl(6, SIOCSIFFLAGS, flags | IFF_UP)` on the fixture's sender. -/
  | wgUp
  /-- `sendto` of a UDP datagram (`payload`) from the fixture's sender to `addr`
      (W4: `sendmsg` with `UDP_SEGMENT` and `IP_MTU_DISCOVER` per `opts`). -/
  | wgXmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts)
  /-- W4: `ioctl(6, SIOCSIFMTU, {"wg0", mtu})` on the fixture's sender. -/
  | wgSetMtu (mtu : Nat)
  /-- `recvfrom(4, MSG_DONTWAIT)` after the fixture waited for the workers. -/
  | wgObserve
  /-- `sendto` of a WireGuard message from the fixture's sender to `port`
      at the destination `dest` (W9: 0 loopback, 1 wg0's own address, 2 the
      loopback alias), with the DS field `tos` and, with `ll`, from the
      link-local address on lo (W5). -/
  | wgInject (family port : Nat) (message : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat := 0)
  /-- W9: `RTM_DELADDR` of wg0's fixture address and `RTM_DELROUTE` of the
      default route via wg0, per family, on a temporary rtnetlink socket. -/
  | wgDeladdr (family : Nat)
  | wgDelroute (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat)
  /-- Lane C: the routing corpus's requests over the same socket. -/
  | wgAddroute (dst plen oif typeCode metric mtu nlflags : Nat)
  | wgAddaddr (addr plen : Nat)
  /-- E-B: an io_uring flood to wg0's `port`: `count` invalid-MAC1 initiations
      with `messages` valid-MAC1 initiations submitted first. -/
  | wgFlood (count port family : Nat) (messages : List (List UInt8))
  /-- W7: `items` submitted as one io_uring batch; the guest waits `waitMs`
      after it (docs/2026-10-06-w4-w7-transmit-bulk.md, 5.5). -/
  | wgBatch (items : List Env.BatchItem) (waitMs : Nat)
  /-- D3: `ioctl(3, KCOV_LEANUX_TIME_ADVANCE, &ticks)` on the trace's KCOV
      descriptor, then the guest's wait (docs/2026-10-05-d3-timers.md, 4.3). -/
  | wgAdvance (ticks : Nat)
  /-- seccomp (docs/2026-10-12-seccomp-design.md 6.1), ops 30-34:
      `seccomp(2)` or `prctl(PR_SET_SECCOMP)` with a `sock_fprog`; one probe
      call in the trace process or in a sandboxed child; `prctl`'s three
      companions; `capset` dropping `CAP_SYS_ADMIN`; the two queries. -/
  | seccompInstall (via : Seccomp.InstallVia) (flags : UInt32) (filter : Option ClassicProg)
      (len : Option Nat) (bad : Seccomp.BadPtr) (mode : Nat)
  | seccompProbe (nr : Int) (args : Array UInt64) (where_ : Seccomp.ProbeWhere) (strict : Option Seccomp.StrictVia)
  | seccompPrctl (cmd : Seccomp.PrctlCmd) (args : Array UInt64)
  | seccompCapdrop
  | seccompQuery (cmd : Seccomp.QueryCmd) (action flags : UInt32)
  /-- L (docs/2026-10-05-l-lifecycle.md): `RTM_NEWLINK` of wg0 and
      `RTM_DELLINK` of wg0 on a temporary rtnetlink socket, and
      `ioctl(6, SIOCSIFFLAGS, flags & ~IFF_UP)` on the fixture's sender. -/
  | wgCreate
  | wgDown
  | wgDelete
  /-- W8 (docs/2026-10-06-w8-w9-netns-routing.md, 3.2): `close` of the
      creating namespace's holders (the injector 8, the listeners 5 and 4,
      then the pin 9), then the guest's wait for the namespace's teardown. -/
  | wgNetnsClose

/-- The generic-netlink socket at descriptor 7 (`NETLINK_FD` in harness/guest.c). -/
def NETLINK_FD : Nat := 7
/-- W8: the foreign-creator fixture's injector and pin (harness/guest.c). -/
def LISTEN6_FD : Nat := 5
def INJECT_FD : Nat := 8
def PIN_FD : Nat := 9

/-- One call on a fixture socket: `CLASS(fd, f)(fd)` in `__sys_sendto`,
    `__sys_recvfrom` (net/socket.c) and `ioctl` (fs/ioctl.c), which is
    `fdget` and a scoped `fdput`. `fd_empty`, `sock_from_file` and the socket
    and ioctl layers are cut points: traces cannot name descriptors 4-7, and
    they are sockets. -/
def socketCallOn (fd : Nat) (body : M Int) : M Int := do
  let f ← fdget fd
  -- W8: a closed fixture socket (the listeners after wg_netns_close):
  -- `fd_empty(f)` -> -EBADF (net/socket.c), before any socket layer runs
  if f.file.isNone then return -EBADF
  let ret ← body
  fdput f
  return ret

def socketCall (body : M Int) : M Int := socketCallOn NETLINK_FD body

/-- W2: the stepped dump socket, opened by the guest after the one at 7 for
    traces with a stepped operation (`Runner.initialKernel`). -/
def DUMP_FD : Nat := 8

/-- The trace's KCOV descriptor (harness/guest.c), on which `wg_advance`
    issues its ioctl. -/
def KCOV_FD : Nat := 3

/-- The network fixture's UDP listener on 127.0.0.1 and its sender. -/
def LISTEN4_FD : Nat := 4
def SENDER_FD : Nat := 6

/-- `send` of the request, whose generic-netlink handling (including a dump's
    callbacks) runs inside the call, then `recv` of the acknowledgement or the
    dump, whose error code is the operation's result. The netlink core's skb
    allocations are below the cut (allocation cut sites, consumed when the
    run armed the `__alloc_skb` range): the request's
    (`netlink_alloc_large_skb`) before the handler, the acknowledgement's and
    the dump's (`nlmsg_new`, `netlink_dump`, `netlink_trim`) after it. -/
def netlinkRequest (handler : M Int) : M Int := do
  let ret ← socketCall do
    skipCut allocCuts
    let ret ← handler
    skipCut allocCuts
    pure ret
  _ ← socketCall (pure 0)
  return ret

/-- L: `wg_create` and `wg_delete`'s rtnetlink socket (design section 5). The
    guest opens it (`socket`, no `SOCK_CLOEXEC`) before the operation's
    window at the lowest free descriptor (`alloc_fd` from `next_fd`) and
    closes it after; only its `send` (the request, handled inside it) and
    `recv` (the acknowledgement, whose error code is the result) run in the
    window. The open and the close report no decision; the close leaves
    `next_fd` at the slot (`__put_unused_fd`). -/
def rtnetlinkRequest (handler : M Int) : M Int := do
  let fs ← getFiles
  let t := fs.fdt
  let some fd := (List.range t.maxFds).find? (fun n => n ≥ fs.nextFd && !(t.openFds.getD n true))
    | unsupported "no free descriptor in the table for the temporary rtnetlink socket (expansion)"
  if fd ≥ (← getTask .task).rlimitNofile then
    unsupported "no descriptor below RLIMIT_NOFILE for the temporary rtnetlink socket (the guest fails)"
  let fid := (← getK).nextFile
  setFile fid { fFlags := O_RDWR, fMode := FMODE_READ ||| FMODE_WRITE ||| FMODE_OPENED, fCount := 1,
                fOp := some (.fixture "rtnetlink"), fInode := some (.fixture "rtnetlink") }
  modifyK fun k => { k with nextFile := fid + 1 }
  setFdtSlot fd (some fid)
  setFdtOpen fd true
  setFdtCloexec fd false
  -- the request's, the acknowledgement's and the notifications' skbs are
  -- below the cut (allocation cut sites), as in `netlinkRequest`
  let ret ← socketCallOn fd do
    skipCut allocCuts
    let ret ← handler
    skipCut allocCuts
    pure ret
  _ ← socketCallOn fd (pure 0)
  -- close(fd) after the window
  setFdtSlot fd none
  setFdtOpen fd false
  modifyFiles fun fs => { fs with nextFd := fd }
  freeFile fid
  return ret

/-- The fuel of `taskWorkRun`: far above the files a trace can close (at most
    `MAX_OPS` operations), never the bound the C has (none). -/
def TASK_WORK_FUEL : Nat := 1 <<< 16

/-- `task_work_run` on exit to user mode: each queued `____fput` runs `__fput`.
    An `__fput` may queue more work (a release dropping another reference), so
    the loop is fuel-bounded rather than bounded by the queue at entry
    (future-proof-paths note, 3(d)). -/
def taskWorkRun : M Unit := do
  for _ in [0:TASK_WORK_FUEL] do
    match (← getTask .task).taskWorks with
    | [] => return
    | fid :: rest =>
      modifyTask .task fun t => { t with taskWorks := rest }
      fputFinal fid
  invariant "task_work_run did not drain the task's work"

/-- W8 `wg_netns_close` (design 3.2): four `close` system calls on the
    creating namespace's holders, each returning to user mode (its `____fput`
    runs then): the injector and the listeners, whose socket release defers
    `put_net` to RCU (the guest lets those run before the last close), then
    the pin, whose dentry's eviction drops the last reference in task
    context: `cleanup_net` is queued there (`fputFinal`'s pin hook consumes
    the queue record), and its section runs in the guest's wait
    (`Env.netnsCleanup`, after this call). -/
def netnsClose : M Int := do
  if !(← get).foreignCreator then unsupported "wg_netns_close outside the foreign-creator fixture"
  if (← get).netnsCHolders.isEmpty then unsupported "wg_netns_close twice"
  for fd in [INJECT_FD, LISTEN6_FD, LISTEN4_FD, PIN_FD] do
    let ret ← sysClose fd
    if ret != 0 then invariant s!"close({fd}) of a fixture holder returned {ret}"
    taskWorkRun
  return 0

def dispatch : Syscall → M Int
  | .eventfd2 count flags => sysEventfd2 count flags
  | .dup fildes => sysDup fildes
  | .dup3 oldfd newfd flags => ksysDup3 oldfd newfd flags
  | .close fd => sysClose fd
  | .read fd count => ksysRead fd count
  | .write fd count buf => ksysWrite fd buf count
  | .pipe2 flags => sysPipe2 flags
  | .fcntl fd cmd arg => sysFcntl fd cmd arg
  | .epollCreate1 flags => sysEpollCreate1 flags
  | .epollCtl epfd op fd events data => sysEpollCtl epfd op fd events data
  | .epollWait epfd maxevents timeout => sysEpollWait epfd maxevents timeout
  | .wgSet attrs => netlinkRequest (WG.wgSetDevice attrs)
  | .wgGet device => netlinkRequest do
    match ← WG.wgGetDevice device with
    | .error e => return e
    | .ok device =>
      modifyAmbient fun w => { w with extraOut := [("device", device)] }
      return 0
  -- W2 (4.2): one system call each on the stepped socket, the netlink
  -- core's chunk allocations below the cut as in `netlinkRequest`. The
  -- stepped operations that run no WireGuard code are outside the domain
  -- [AGENT, coordinator 2026-10-12: the WireGuard boundary, the af_netlink.c
  -- loop unanchored]: `-EAGAIN` (nothing queued), and a receive that pops
  -- only `NLMSG_DONE` or an acknowledgement (the dump call that produced
  -- it ran in the previous operation).
  | .wgGetStart device => socketCallOn DUMP_FD do
    skipCut allocCuts
    -- netlink_autobind (af_netlink.c:803-830) on the socket's first sendmsg:
    -- its port id, the process's, is the fixture socket's, so the collision
    -- draws once (:820); the port id reaches no modeled path (a cut)
    let sock ← WG.getNlSock DUMP_FD
    if !sock.bound then
      skipCutExactly .netlinkAutobindPort 1 allocCuts
      WG.setNlSock DUMP_FD { sock with bound := true }
    WG.netlinkDumpStart DUMP_FD device
    skipCut allocCuts
    return 0
  | .wgGetRecv => socketCallOn DUMP_FD do
    skipCut allocCuts
    let some messages ← WG.netlinkRecvmsg DUMP_FD
      | unsupported "wg_get_recv with nothing queued (-EAGAIN): no WireGuard code runs"
    skipCut allocCuts
    -- the chunk carrying the DONE and a start error's acknowledgement run no
    -- WireGuard code but carry the dump's data or the lookup's error code; a
    -- lone NLMSG_DONE (one that did not fit its chunk) carries nothing and
    -- stays outside the domain, as does the `-EBUSY` acknowledgement
    -- (netlinkDumpStart stops at the start)
    if messages.all (· matches .done ..) then
      unsupported "wg_get_recv popping a lone NLMSG_DONE: no WireGuard code runs"
    modifyAmbient fun w => { w with extraOut := [("messages", Lean.Json.arr (messages.map (·.toJson)).toArray)] }
    return 0
  | .wgUp => socketCallOn SENDER_FD Env.wgUp
  | .wgXmit family addr payload opts => socketCallOn SENDER_FD do
    -- W9: the sender's `sendto` routes on the fixture's tables
    -- (`World.route4/6`): into wg0 by the default route the guest adds after
    -- a successful wg_up (and removes with a down, a deletion or
    -- `wg_delroute`), else `-ENETUNREACH`; a local destination never
    -- reaches wg0
    let r ← match ← Net.routeLookup family 0 addr with
      | .error err => return err
      | .ok r => pure r
    if r.dev != WG0_IFINDEX then unsupported "a transmit to a local address (not into wg0)"
    -- W4: an MTU change below the family's floor took its routes down with
    -- its IP device, and the fixture re-adds them only at the next wg_up
    if let some d := (← getK).wg then
      if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
        unsupported "a transmit after an MTU change took the family's routes into wg0 down"
    -- udp_sendmsg returns the datagram's length once the device took it
    Env.fixtureSend
    -- lane C: `dst_mtu` is the route's metric when it carries one
    let opts := { opts with routeMtu := opts.routeMtu <|> (if r.mtu != 0 then some r.mtu else none) }
    match ← Env.xmitPackets family addr payload opts with
    | .error e => return e   -- refused by the sender's IP layer before any output
    | .ok (pkts, mtu) =>
      Env.xmitMulticastLoop family addr
      -- lane C: `ip_finish_output2` on wg0: the device's one neighbour
      if family == 4 then Net.neighbourClassify WG0_IFINDEX
      let ret ← WG.wgXmit family addr pkts mtu
      return if ret == 0 then payload.length else ret
  | .wgSetMtu mtu => socketCallOn SENDER_FD (Env.setMtu mtu)
  | .wgInject family port message tos ll dest => socketCallOn SENDER_FD (Env.inject family port message tos ll dest)
  | .wgDeladdr family => rtnetlinkRequest (Env.wgDeladdr family)
  | .wgDelroute family named dst plen oif typeCode metric => rtnetlinkRequest (Env.wgDelroute family named dst plen oif typeCode metric)
  | .wgAddroute dst plen oif typeCode metric mtu nlflags => rtnetlinkRequest (Env.wgAddroute dst plen oif typeCode metric mtu nlflags)
  | .wgAddaddr addr plen => rtnetlinkRequest (Env.wgAddaddr addr plen)
  | .wgFlood count port family messages => Env.flood count port family messages
  -- W7: the io_uring submission's descriptor plumbing (the ring's fdget, each
  -- send's fget of the sender) is the fixture's, as the flood's is: not modeled
  | .wgBatch items _ => Env.batch items
  | .wgObserve => do
    -- the fixture's observation happens whether or not the listener is still
    -- open (W8: after wg_netns_close the `recvfrom(4)` is -EBADF and the
    -- datagrams null, the sender's inbox and the stats are read as always)
    let (ret, observed) ← Env.observe
    modifyAmbient fun w => { w with extraOut := ["datagrams", "replies", "stats"].map fun k => (k, observed.getObjValD k) }
    socketCallOn LISTEN4_FD (pure ret)
  | .wgAdvance ticks => do
    -- `ioctl(3, KCOV_LEANUX_TIME_ADVANCE, &ticks)`: `CLASS(fd, f)(fd)`
    -- (fs/ioctl.c), then the LEANUX case of `kcov_ioctl` (a cut point but
    -- for its kind-304 record)
    let f ← fdget KCOV_FD
    if f.file.isNone then unsupported "wg_advance after the trace closed the KCOV descriptor"
    let ret ← Env.advance ticks
    fdput f
    return ret
  | .wgCreate => rtnetlinkRequest WG.wgCreate
  | .wgDown => socketCallOn SENDER_FD Env.wgDown
  | .wgDelete => rtnetlinkRequest Env.wgDelete
  | .wgNetnsClose => netnsClose
  | .seccompInstall via flags filter len bad mode => Seccomp.sysSeccompInstall via flags filter len bad mode
  | .seccompProbe nr args .self _ => Seccomp.sysSeccompProbeSelf nr args
  | .seccompProbe nr args .child strict => Seccomp.sysSeccompProbeChild nr args strict
  | .seccompPrctl cmd args => Seccomp.sysSeccompPrctl cmd args
  | .seccompCapdrop => Seccomp.sysSeccompCapdrop
  | .seccompQuery cmd action flags => Seccomp.sysSeccompQuery cmd action flags

/-- The x86-64 number of the system call an operation makes, for the entry
    path once a seccomp mode is set (`__secure_computing`, design 4.5):
    `none` for a probe, whose handler enters itself with the probe's
    arguments, and for the network operations, which make several calls
    through the fixture's sockets and are outside the seccomp domain. -/
def syscallNr : Syscall → Option Int
  | .eventfd2 .. => some 290
  | .dup _ => some 32
  | .dup3 .. => some 292
  | .close _ => some 3
  | .read .. => some 0
  | .write .. => some 1
  | .pipe2 _ => some 293
  | .fcntl .. => some 72
  | .seccompInstall .seccomp .. | .seccompQuery .. => some Seccomp.NR_seccomp
  | .seccompInstall .prctl .. | .seccompPrctl .. => some Seccomp.NR_prctl
  | .seccompCapdrop => some Seccomp.NR_capset
  | .seccompProbe .. => none
  | _ => none

def Syscall.isNet : Syscall → Bool
  | .seccompInstall .. | .seccompProbe .. | .seccompPrctl .. | .seccompCapdrop | .seccompQuery .. => false
  | .eventfd2 .. | .dup _ | .dup3 .. | .close _ | .read .. | .write .. | .pipe2 _ | .fcntl .. => false
  | _ => true

/-- One system call: entry, the handler, and the return-to-user work. -/
def syscall (call : Syscall) : M Int := do
  modify fun w => { w with userOut := none, userFds := none, queuedThisCall := [], emitted := {}, translatedLen := none }
  modifyAmbient fun a => { a with steps := #[], extraOut := [], fired := #[], netRxSections := 0, netRxSection := 0 }
  -- seccomp: the entry path of the operation's own call once a mode is set
  -- (a harness call by design 6.2 rule 1: a cache hit); a probe enters itself
  match syscallNr call with
  | some nr => Seccomp.enterHarnessCall nr
  | none =>
    if call.isNet && (← getCurrent).seccomp.mode != .disabled then
      unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)"
  let ret ← dispatch call
  -- harness calls whose entry falls inside the window after the operation's (fixture knowledge)
  for c in Env.windowTailCalls do Seccomp.enterHarnessCall c
  taskWorkRun
  -- the guest waits inside the operations that can queue the handshake send
  -- worker (and in wg_inject); the worker runs during that wait
  -- worker; D3: a timer may fire in these waits (`Env.idleTimers`)
  match call with
  | .wgSet _ | .wgInject .. => Env.runSendWorkers; Env.idleTimers
  -- W9 (design 14.3b): the guest's route adds follow the up's wait
  | .wgUp => Env.runSendWorkers; Env.idleTimers; Env.routeIntoWg0
  | .wgXmit .. => Env.afterXmit; Env.idleTimers
  | .wgBatch .. => Env.idleTimers   -- W7: the batch runs its queued units itself
  -- D3: the guest waits after the advance; the next tick runs the due timers
  | .wgAdvance _ => Env.afterAdvance
  -- W8: the namespace's teardown section runs in the guest's wait
  | .wgNetnsClose => Env.netnsCleanup
  | _ => pure ()
  -- lane C's shape oracle (the design note, 9.4): after an operation that
  -- changes the IPv4 tables, the trie as `/proc/net/fib_trie` prints it,
  -- compared with the guest's read outside the window
  match call with
  | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
  | .wgAddroute .. | .wgAddaddr .. =>
    let shape := Net.Fib.shape (← getK)
    modifyAmbient fun w => { w with extraOut := w.extraOut ++ [("fib_trie", shape)] }
  | _ => pure ()
  return ret

end Leanux
