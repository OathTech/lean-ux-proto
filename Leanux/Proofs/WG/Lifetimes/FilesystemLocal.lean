import Leanux.Proofs.WG.Lifetimes.AllocationInitial

/-! Local filesystem calls whose original bodies perform no tracked WireGuard
object access. The wait callbacks dispatch only the original epoll callbacks;
pipe copy/allocation choices and signal delivery do not invoke WireGuard. This
source-coverage observation is separate from the normal-endpoint WG frame.
The lift retains the original result/World/Stop and the entire incoming history.
No claim is made about subsequent task work, FS dispatch or an outer runner. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.Proofs.Logged Leanux.Proofs.Framing

/-- Transport the concrete allocation invariant through an explicitly chosen
access-free lift. A frame alone does not establish source access coverage. -/
theorem allocation_lift_sameWGKernel (a : M α) (ha : SameWGKernel a) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift a (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  exact hi.wgKernel (ha w x v hr)

inductive FilesystemLocalCall where
  | wake (fuel : Nat) (queue : WaitQueueRef) (mode : UInt32) (nrExclusive : Int)
      (flags : UInt32) (key : Option UInt32)
  | safewake (fuel : Nat) (ep : EpId) (epi : Option EpiId) (flags : UInt32)
  | callback (fuel : Nat) (pwq : PwqId) (mode flags : UInt32) (key : Option UInt32)
  | read (iocb : Kiocb) (count : Nat)
  | write (iocb : Kiocb) (src : IovIter)
  | release (ino : PipefsInodeId) (fid : FileId)

namespace FilesystemLocalCall

def Result : FilesystemLocalCall → Type
  | .safewake .. => Unit
  | _ => Int

def original : (call : FilesystemLocalCall) → M call.Result
  | .wake fuel queue mode nr flags key => wakeUpCommonAt fuel queue mode nr flags key
  | .safewake fuel ep epi flags => epPollSafewakeAt fuel ep epi flags
  | .callback fuel pwq mode flags key => epPollCallbackAt fuel pwq mode flags key
  | .read iocb count => pipeRead iocb count
  | .write iocb src => pipeWrite iocb src
  | .release ino fid => pipeRelease ino fid

def observed (call : FilesystemLocalCall) : MixedM call.Result := liftPrefix call.original

theorem frame (call : FilesystemLocalCall) : SameWGKernel call.original := by
  cases call with
  | wake fuel queue mode nr flags key =>
    apply SameView.of_wp
    intro initial
    exact WaitFrames.wakeUpCommonAt_spec (fun s => s = initial) fuel queue mode nr flags key
  | safewake fuel ep epi flags =>
    apply SameView.of_wp
    intro initial
    exact WaitFrames.epPollSafewakeAt_spec (fun s => s = initial) fuel ep epi flags
  | callback fuel pwq mode flags key =>
    apply SameView.of_wp
    intro initial
    exact WaitFrames.epPollCallbackAt_spec (fun s => s = initial) fuel pwq mode flags key
  | read iocb count => exact PipeFrames.pipeRead_sameWGKernel iocb count
  | write iocb src => exact PipeFrames.pipeWrite_sameWGKernel iocb src
  | release ino fid => exact PipeFrames.pipeRelease_sameWGKernel ino fid

theorem erases (call : FilesystemLocalCall) : ErasesPrefix call.observed call.original :=
  erasesPrefix_lift call.original

theorem run (call : FilesystemLocalCall) (w : World) (h : List LifetimeEvent) :
    runPrefix call.observed w h = (call.original.run w, h) := rfl

theorem allocation (call : FilesystemLocalCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  allocation_lift_sameWGKernel call.original call.frame

end FilesystemLocalCall
end Leanux.Proofs.WG.Lifetimes
