import Leanux.Proofs.Framing.EventpollCalls
import Leanux.Proofs.WG.Lifetimes.FilesystemLocal

/-! The eleven original filesystem dispatch arms and the actual deferred file
release loop. Source coverage is audited separately from the normal-endpoint
frame: file operations, epoll/wait callbacks and signal helpers perform no
tracked peer, keypair or packet-store access. `fputFinal` can queue namespace
cleanup, but does not execute `Env.netnsCleanup` or `WG.netnsPreExit`.

The observers are exact lifts, preserving all input history and original Stops.
The bounded task loop is retained without a drain/fuel-sufficiency premise.
These contracts do not cover the enclosing syscall/environment/Runner tails. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.Proofs.Logged Leanux.Proofs.Framing

/-- Exactly the filesystem constructors of the original `Syscall` dispatcher. -/
inductive FilesystemDispatch where
  | eventfd2 (count flags : UInt32)
  | dup (fildes : Nat)
  | dup3 (oldfd newfd : Nat) (flags : UInt32)
  | close (fd : Nat)
  | read (fd count : Nat)
  | write (fd count : Nat) (buf : ByteArray)
  | pipe2 (flags : UInt32)
  | fcntl (fd : Nat) (cmd : FcntlCmd) (arg : UInt64)
  | epollCreate1 (flags : UInt32)
  | epollCtl (epfd : Nat) (op fd : Int) (events : UInt32) (data : UInt64)
  | epollWait (epfd : Nat) (maxevents timeout : Int)

namespace FilesystemDispatch

def toSyscall : FilesystemDispatch → Syscall
  | .eventfd2 count flags => .eventfd2 count flags
  | .dup fd => .dup fd
  | .dup3 oldfd newfd flags => .dup3 oldfd newfd flags
  | .close fd => .close fd
  | .read fd count => .read fd count
  | .write fd count buf => .write fd count buf
  | .pipe2 flags => .pipe2 flags
  | .fcntl fd cmd arg => .fcntl fd cmd arg
  | .epollCreate1 flags => .epollCreate1 flags
  | .epollCtl epfd op fd events data => .epollCtl epfd op fd events data
  | .epollWait epfd maxevents timeout => .epollWait epfd maxevents timeout

theorem frame (call : FilesystemDispatch) : SameWGKernel (dispatch call.toSyscall) := by
  cases call with
  | eventfd2 count flags => exact FSFrames.sysEventfd2_sameWGKernel count flags
  | dup fd => exact FSFrames.sysDup_sameWGKernel fd
  | dup3 oldfd newfd flags => exact FSFrames.ksysDup3_sameWGKernel oldfd newfd flags
  | close fd => exact FSFrames.sysClose_sameWGKernel fd
  | read fd count => exact FSFrames.ksysRead_sameWGKernel fd count
  | write fd count buf => exact FSFrames.ksysWrite_sameWGKernel fd buf count
  | pipe2 flags => exact FSFrames.sysPipe2_sameWGKernel flags
  | fcntl fd cmd arg => exact FSFrames.sysFcntl_sameWGKernel fd cmd arg
  | epollCreate1 flags => exact EventpollFrames.sysEpollCreate1_sameWGKernel flags
  | epollCtl epfd op fd events data => exact EventpollFrames.sysEpollCtl_sameWGKernel epfd op fd events data
  | epollWait epfd maxevents timeout => exact EventpollFrames.sysEpollWait_sameWGKernel epfd maxevents timeout

end FilesystemDispatch

/-- The dispatch result is Int; the original deferred loop returns Unit. -/
inductive FilesystemCall where
  | dispatch (call : FilesystemDispatch)
  | taskWork

namespace FilesystemCall

def Result : FilesystemCall → Type
  | .dispatch _ => Int
  | .taskWork => Unit

def original : (call : FilesystemCall) → M call.Result
  | .dispatch call => Leanux.dispatch call.toSyscall
  | .taskWork => taskWorkRun

def observed (call : FilesystemCall) : MixedM call.Result := liftPrefix call.original

theorem frame (call : FilesystemCall) : SameWGKernel call.original := by
  cases call with
  | dispatch call => exact call.frame
  | taskWork => exact FSFrames.taskWorkRun_sameWGKernel

theorem erases (call : FilesystemCall) : ErasesPrefix call.observed call.original :=
  erasesPrefix_lift call.original

theorem run (call : FilesystemCall) (w : World) (h : List LifetimeEvent) :
    runPrefix call.observed w h = (call.original.run w, h) := rfl

theorem allocation (call : FilesystemCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  allocation_lift_sameWGKernel call.original call.frame

end FilesystemCall
end Leanux.Proofs.WG.Lifetimes
