import Leanux.FS.Eventfd
import Leanux.FS.ReadWrite
import Leanux.FS.Fcntl
import Leanux.FS.Close
import Leanux.FS.Inode
import Leanux.FS.PipeCreate
import Leanux.Env

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
  /-- `sendmsg` of WG_CMD_SET_DEVICE on the fixture's generic-netlink socket,
      then `recvmsg` of the acknowledgement: the result is its error code. -/
  | wgSet (attrs : WG.DeviceAttrs)
  /-- `sendmsg` of a WG_CMD_GET_DEVICE dump request, then `recvmsg` of the
      dump; the device state goes to `extraOut`. -/
  | wgGet
  /-- `ioctl(6, SIOCSIFFLAGS, flags | IFF_UP)` on the fixture's sender. -/
  | wgUp
  /-- `sendto` of a UDP datagram (`payload`) from the fixture's sender to `addr`. -/
  | wgXmit (family addr : Nat) (payload : List UInt8)
  /-- `recvfrom(4, MSG_DONTWAIT)` after the fixture waited for the workers. -/
  | wgObserve
  /-- `sendto` of a WireGuard message from the fixture's sender to `port`. -/
  | wgInject (family port : Nat) (message : List UInt8)
  /-- D3: `ioctl(3, KCOV_LEANUX_TIME_ADVANCE, &ticks)` on the trace's KCOV
      descriptor, then the guest's wait (docs/2026-10-05-d3-timers.md, 4.3). -/
  | wgAdvance (ticks : Nat)
  /-- L (docs/2026-10-05-l-lifecycle.md): `RTM_NEWLINK` of wg0 and
      `RTM_DELLINK` of wg0 on a temporary rtnetlink socket, and
      `ioctl(6, SIOCSIFFLAGS, flags & ~IFF_UP)` on the fixture's sender. -/
  | wgCreate
  | wgDown
  | wgDelete

/-- The generic-netlink socket at descriptor 7 (`NETLINK_FD` in harness/guest.c). -/
def NETLINK_FD : Nat := 7

/-- One call on a fixture socket: `CLASS(fd, f)(fd)` in `__sys_sendto`,
    `__sys_recvfrom` (net/socket.c) and `ioctl` (fs/ioctl.c), which is
    `fdget` and a scoped `fdput`. `fd_empty`, `sock_from_file` and the socket
    and ioctl layers are cut points: traces cannot name descriptors 4-7, and
    they are sockets. -/
def socketCallOn (fd : Nat) (body : M Int) : M Int := do
  let f ← fdget fd
  if f.file.isNone then invariant "a fixture socket is not open"
  let ret ← body
  fdput f
  return ret

def socketCall (body : M Int) : M Int := socketCallOn NETLINK_FD body

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
  if fd ≥ (← getK).task.rlimitNofile then
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

def dispatch : Syscall → M Int
  | .eventfd2 count flags => sysEventfd2 count flags
  | .dup fildes => sysDup fildes
  | .dup3 oldfd newfd flags => ksysDup3 oldfd newfd flags
  | .close fd => sysClose fd
  | .read fd count => ksysRead fd count
  | .write fd count buf => ksysWrite fd buf count
  | .pipe2 flags => sysPipe2 flags
  | .fcntl fd cmd arg => sysFcntl fd cmd arg
  | .wgSet attrs => netlinkRequest (WG.wgSetDevice attrs)
  | .wgGet => netlinkRequest do
    match ← WG.wgGetDevice with
    | .error e => return e
    | .ok device =>
      modify fun w => { w with extraOut := [("device", device)] }
      return 0
  | .wgUp => socketCallOn SENDER_FD Env.wgUp
  | .wgXmit family addr payload => socketCallOn SENDER_FD do
    -- the fixture adds wg0's routes after a successful wg_up; before that,
    -- and after a down or a deletion, no route exists (L)
    if !(← get).routesViaWg0 then return -ENETUNREACH
    -- udp_sendmsg returns the datagram's length once the device took it
    Env.fixtureSend
    Env.xmitMulticastLoop family addr
    let ret ← WG.wgXmit family addr (← Env.xmitPacket family addr payload)
    return if ret == 0 then payload.length else ret
  | .wgInject family port message => socketCallOn SENDER_FD (Env.inject family port message)
  | .wgObserve => socketCallOn LISTEN4_FD do
    let (ret, observed) ← Env.observe
    modify fun w => { w with extraOut := ["datagrams", "replies", "stats"].map fun k => (k, observed.getObjValD k) }
    return ret
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

/-- `task_work_run` on exit to user mode: each queued `____fput` runs `__fput`. -/
partial def taskWorkRun : M Unit := do
  match (← getK).task.taskWorks with
  | [] => return
  | fid :: rest =>
    modifyK fun k => { k with task := { k.task with taskWorks := rest } }
    fputFinal fid
    taskWorkRun

/-- One system call: entry, the handler, and the return-to-user work. -/
def syscall (call : Syscall) : M Int := do
  modify fun w => { w with steps := #[], userOut := none, userFds := none, extraOut := [], queuedThisCall := [], fired := #[] }
  let ret ← dispatch call
  taskWorkRun
  -- the guest waits inside the operations that can queue the handshake send
  -- worker (and in wg_inject); the worker runs during that wait
  -- worker; D3: a timer may fire in these waits (`Env.idleTimers`)
  match call with
  | .wgSet _ | .wgUp | .wgInject .. => Env.runSendWorkers; Env.idleTimers
  | .wgXmit .. => Env.afterXmit; Env.idleTimers
  -- D3: the guest waits after the advance; the next tick runs the due timers
  | .wgAdvance _ => Env.afterAdvance
  | _ => pure ()
  return ret

end Leanux
