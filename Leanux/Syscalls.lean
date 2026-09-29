import Leanux.FS.Eventfd
import Leanux.FS.ReadWrite
import Leanux.FS.Fcntl
import Leanux.FS.Close

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

def dispatch : Syscall → M Int
  | .eventfd2 count flags => sysEventfd2 count flags
  | .dup fildes => sysDup fildes
  | .dup3 oldfd newfd flags => ksysDup3 oldfd newfd flags
  | .close fd => sysClose fd
  | .read fd count => ksysRead fd count
  | .write fd count word => ksysWrite fd word count
  | .fcntl fd cmd arg => sysFcntl fd cmd arg

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
  modify fun w => { w with steps := #[], userOut := none }
  let ret ← dispatch call
  taskWorkRun
  return ret

end Leanux
