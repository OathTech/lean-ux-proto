import Leanux.FS.Eventfd
import Leanux.FS.ReadWrite
import Leanux.FS.Fcntl
import Leanux.FS.Close
import Leanux.WG.Netlink

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
  /-- `write(fd, buf, count)`; `word` is the buffer's first 8 bytes. -/
  | write (fd count : Nat) (word : UInt64)
  | fcntl (fd : Nat) (cmd : FcntlCmd) (arg : UInt64)
  /-- `sendmsg` of WG_CMD_SET_DEVICE on the fixture's generic-netlink socket,
      then `recvmsg` of the acknowledgement: the result is its error code. -/
  | wgSet (attrs : WG.DeviceAttrs)
  /-- `sendmsg` of a WG_CMD_GET_DEVICE dump request, then `recvmsg` of the
      dump; the device state goes to `dumpOut`. -/
  | wgGet

/-- The generic-netlink socket at descriptor 7 (`NETLINK_FD` in harness/guest.c). -/
def NETLINK_FD : Nat := 7

/-- One socket call on the fixture's netlink socket: `CLASS(fd, f)(fd)` in
    `__sys_sendto`/`__sys_recvfrom` (net/socket.c), which is `fdget` and a
    scoped `fdput`. `fd_empty` and `sock_from_file` are cut points: descriptor
    7 cannot be closed by a trace, and it is a socket. -/
def socketCall (body : M Int) : M Int := do
  let f ← fdget NETLINK_FD
  if f.file.isNone then invariant "the fixture's netlink socket is not open"
  let ret ← body
  fdput f
  return ret

/-- `send` of the request, whose generic-netlink handling (including a dump's
    callbacks) runs inside the call, then `recv` of the acknowledgement or the
    dump, whose error code is the operation's result. -/
def netlinkRequest (handler : M Int) : M Int := do
  let ret ← socketCall handler
  _ ← socketCall (pure 0)
  return ret

def dispatch : Syscall → M Int
  | .eventfd2 count flags => sysEventfd2 count flags
  | .dup fildes => sysDup fildes
  | .dup3 oldfd newfd flags => ksysDup3 oldfd newfd flags
  | .close fd => sysClose fd
  | .read fd count => ksysRead fd count
  | .write fd count word => ksysWrite fd word count
  | .fcntl fd cmd arg => sysFcntl fd cmd arg
  | .wgSet attrs => netlinkRequest (WG.wgSetDevice attrs)
  | .wgGet => netlinkRequest do
    match ← WG.wgGetDevice with
    | .error e => return e
    | .ok device =>
      modify fun w => { w with dumpOut := some device }
      return 0

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
  modify fun w => { w with steps := #[], userOut := none, dumpOut := none }
  let ret ← dispatch call
  taskWorkRun
  return ret

end Leanux
