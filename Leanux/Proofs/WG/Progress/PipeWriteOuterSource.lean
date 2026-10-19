import Leanux.Proofs.WG.Progress.PipeWriteSource

/-! The original outer pipeWrite control flow with only its inner loop replaced.
Wake callbacks and inode time updates remain the concrete original operations. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.PipeWriteOuter
open Leanux

def withToOut (inner : File → PipeId → FS.M (Int × Bool))
    (iocb : Kiocb) (src : IovIter) : FS.M Int := do
  let filp ← getFile iocb.filp
  let pid ← pipeOf filp
  if ← branchCmp .pipeWriteNull (src.count == 0) src.count 0 then return 0
  let (ret, wasEmpty) ← inner filp pid
  let mut ret := ret
  let mut wakeNextWriter := false
  let p ← getPipe pid
  if ← branchCmp .pipeWriteFullAtOut (pipeFull p.head p.tail p.maxUsage)
      (pipeOccupancy p.head p.tail) p.maxUsage then
    wakeNextWriter := false
  let wake ← do
    if ← branch .pipeWriteWasEmpty wasEmpty then pure true
    else branch .pipeWritePollUsage p.pollUsage
  if wake then wakeUpInterruptibleSyncPoll (.pipeRd pid) (EPOLLIN ||| EPOLLRDNORM)
  killFasync p.fasyncReaders
  if ← branch .pipeWriteWakeNextWriter wakeNextWriter then
    wakeUpInterruptibleSyncPoll (.pipeWr pid) (EPOLLOUT ||| EPOLLWRNORM)
  let update ← do
    if ← branchCmp .pipeWritePositive (ret > 0) ret 0 then branch .pipeWriteSbTrylock true
    else pure false
  if update then
    let err ← fileUpdateTime (← getFile iocb.filp)
    if ← branchCmp .pipeWriteUpdateTimeErr (err != 0) err 0 then ret := err
  return ret

def finite (iocb : Kiocb) (src : IovIter) : FS.M Int :=
  withToOut (fun filp pid=>PipeWrite.finite iocb filp pid src) iocb src

theorem original_source (iocb : Kiocb) (src : IovIter) :
    pipeWrite iocb src =
      withToOut (fun filp pid=>pipeWriteToOut iocb filp pid src) iocb src := rfl

theorem finite_source (iocb : Kiocb) (src : IovIter) :
    pipeWrite iocb src=finite iocb src := by
  rw [original_source]
  unfold finite
  exact congrArg (fun inner=>withToOut inner iocb src)
    (funext fun filp=>funext fun pid=>PipeWrite.finite_source iocb filp pid src)

end Leanux.Proofs.WG.Progress.PipeWriteOuter
