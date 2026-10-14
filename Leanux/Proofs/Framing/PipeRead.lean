import Leanux.Proofs.Framing.Pipe

namespace Leanux.Proofs.Framing.PipeFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing
open Leanux.Proofs.Framing.KernelFrames Leanux.Proofs.Framing.SignalFrames
open Leanux.Proofs.Framing.PipeAux Leanux.Proofs.Framing.WaitFrames

set_option pp.structureInstances false
set_option maxHeartbeats 1500000

/-- Exact original read iteration, named only on the proof side. -/
def readStep (iocb : Kiocb) (filp : File) (pid : PipeId) (count : Nat)
    (b : Nat × Int) : M (ForInStep (Nat × Int)) := do
  let mut totalLen := b.1
  let mut ret := b.2
  -- head = smp_load_acquire(&pipe->head); the note_loss block is compiled out
  let p ← getPipe pid
  let head := p.head
  let mut tail := p.tail
  if ← branchCmp .pipeReadNotEmpty (head != tail) head.toNat tail.toNat then
    let i ← pipeBufIdx p tail
    let buf ← getPipeBuf pid i
    let mut chars := buf.len
    if ← branchCmp .pipeReadCharsOver (chars > totalLen) chars totalLen then
      if ← branchCmp .pipeReadWhole (hasFlag buf.flags PIPE_BUF_FLAG_WHOLE)
          (buf.flags &&& PIPE_BUF_FLAG_WHOLE).toNat 0 then
        unsupported "pipe_read: PIPE_BUF_FLAG_WHOLE (a notification buffer)"
      chars := totalLen
    let error ← pipeBufConfirm buf
    if ← branch .pipeReadConfirmError (error != 0) then
      unsupported "pipe_read: pipe_buf_confirm failed"
    let some page := buf.page | invariant "pipe_read: a buffer with a NULL page"
    let written ← copyPageToIter page buf.offset chars count
    if ← branchCmp .pipeReadShortCopy (written < chars) written chars then
      if ← branchCmp .pipeReadFaultNoRet (ret == 0) ret 0 then ret := -EFAULT
      return .done (totalLen, ret)
    ret := ret + chars
    let mut buf := { buf with offset := buf.offset + chars, len := buf.len - chars }
    -- Was it a packet buffer? Clean up and exit
    if ← branchCmp .pipeReadPacket (hasFlag buf.flags PIPE_BUF_FLAG_PACKET)
        (buf.flags &&& PIPE_BUF_FLAG_PACKET).toNat 0 then
      totalLen := chars
      buf := { buf with len := 0 }
    setPipeBuf pid i buf
    if ← branch .pipeReadBufEmpty (buf.len == 0) then
      tail ← pipeUpdateTail pid i tail
    totalLen := totalLen - chars
    if ← branch .pipeReadDone (totalLen == 0) then return .done (totalLen, ret)  -- common path
    if ← branchCmp .pipeReadMore (head != tail) head.toNat tail.toNat then return .yield (totalLen, ret)
  let p ← getPipe pid
  if ← branchCmp .pipeReadNoWriters (p.writers == 0) p.writers 0 then return .done (totalLen, ret)
  if ← branchCmp .pipeReadHaveData (ret != 0) ret 0 then return .done (totalLen, ret)
  -- `(filp->f_flags & O_NONBLOCK) || (iocb->ki_flags & IOCB_NOWAIT)`
  let nonblock ← do
    if ← branchCmp .pipeReadNonblock (hasFlag filp.fFlags O_NONBLOCK) (filp.fFlags &&& O_NONBLOCK).toNat 0 then
      pure true
    else branchCmp .pipeReadNowait (hasFlag iocb.kiFlags IOCB_NOWAIT) (iocb.kiFlags &&& IOCB_NOWAIT).toNat 0
  if nonblock then
    ret := -EAGAIN
    return .done (totalLen, ret)
  unsupported "pipe_read: blocking wait (wait_event_interruptible_exclusive)"
  return .yield (totalLen, ret)

def readLoop (iocb : Kiocb) (filp : File) (pid : PipeId) (count totalLen : Nat)
    (ret : Int) : M Int := do
  let b ← forIn Lean.Loop.mk (totalLen, ret) (fun _ b => readStep iocb filp pid count b)
  return b.2

def read (iocb : Kiocb) (count : Nat) : M Int := do
  let mut totalLen := count
  let filp ← getFile iocb.filp
  let pid ← pipeOf filp
  -- Null read succeeds.
  if ← branchCmp .pipeReadNull (totalLen == 0) totalLen 0 then return 0
  let mut ret : Int := 0
  modify fun w => { w with userOut := some ByteArray.empty }
  -- mutex_lock(&pipe->mutex)
  let p0 ← getPipe pid
  let wasFull := pipeFull p0.head p0.tail p0.maxUsage
  let mut wakeNextReader := false
  let result ← readLoop iocb filp pid count totalLen ret
  let p ← getPipe pid
  if ← branchCmp .pipeReadEmptyAtEnd (p.head == p.tail) p.head.toNat p.tail.toNat then
    wakeNextReader := false
  -- mutex_unlock(&pipe->mutex)
  if ← branch .pipeReadWasFull wasFull then
    wakeUpInterruptibleSyncPoll (.pipeWr pid) (EPOLLOUT ||| EPOLLWRNORM)
  if ← branch .pipeReadWakeNextReader wakeNextReader then
    wakeUpInterruptibleSyncPoll (.pipeRd pid) (EPOLLIN ||| EPOLLRDNORM)
  killFasync p.fasyncWriters
  if ← branchCmp .pipeReadPositive (result > 0) result 0 then
    fileAccessed (← getFile iocb.filp)
  return result

theorem pipeRead_eq (iocb : Kiocb) (count : Nat) :
    pipeRead iocb count = read iocb count := by
  simp only [pipeRead, read, readLoop, readStep, bind_assoc, pure_bind]
  rfl

def occupancy (pid : PipeId) (w : World) : Nat :=
  ((w.k.pipes[pid]?).map (fun p => pipeOccupancy p.head p.tail)).getD 0

theorem pipeOccupancy_tail_lt (head tail : UInt32) (hne : head ≠ tail) :
    pipeOccupancy head (tail + 1) < pipeOccupancy head tail := by
  have h := pipeOccupancy_tail_succ head tail hne
  omega

theorem readStep_progress (iocb : Kiocb) (filp : File) (pid : PipeId)
    (count : Nat) (b : Nat × Int) (entry : World) :
    ⦃fun w => ⌜w = entry⌝⦄ readStep iocb filp pid count b
    ⦃⇓? r w => ⌜wgKernelView w = wgKernelView entry ∧
      match r with
      | .done _ => True
      | .yield _ => occupancy pid w < occupancy pid entry⌝⦄ := by
  have copy_spec := fun page offset bytes cap =>
    sameKernel_wp _ (copyPageToIter_sameKernel page offset bytes cap) (fun k => k = entry.k)
  have release_spec := fun i =>
    pipeBufRelease_view_spec pid i (fun v => v = pipeView pid entry)
  mvcgen [readStep, copy_spec, release_spec, pipeBufConfirm, pipeBufIdx,
    getPipeBuf, setPipeBuf, pipeUpdateTail, getPipe, setPipe, getK, modifyK,
    branch, branchCmp, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [WGKernelView.ofKernel, occupancy, pipeView, wgKernelView]
  all_goals try omega
  all_goals exact pipeOccupancy_tail_lt _ _ (by assumption)

theorem readStep_variant_spec (initial : WGKernelView) (mb : Nat)
    (iocb : Kiocb) (filp : File) (pid : PipeId) (count : Nat) (b : Nat × Int) :
    ⦃fun w => ⌜mb = occupancy pid w ∧ wgKernelView w = initial⌝⦄ readStep iocb filp pid count b
    ⦃⇓? r w => ⌜match r with
      | .done _ => wgKernelView w = initial
      | .yield _ => occupancy pid w < mb ∧ wgKernelView w = initial⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w r w' hp hr
  have hs := (hoare_iff_triple _ _ _).mpr (readStep_progress iocb filp pid count b w)
    w r w' rfl hr
  cases r <;> simp_all

theorem readLoop_sameWGKernel (iocb : Kiocb) (filp : File) (pid : PipeId)
    (count totalLen : Nat) (ret : Int) :
    SameWGKernel (readLoop iocb filp pid count totalLen ret) := by
  apply SameView.of_wp
  intro initial
  have step_spec := readStep_variant_spec initial
  mvcgen [readLoop, step_spec]
  invariants
  | inv1 => fun _ w => ⟨occupancy pid w⟩
  | inv2 => ((⇓? _ w => ⌜wgKernelView w = initial⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (letI : Nonempty World := ⟨by assumption⟩; infer_instance)
  all_goals try intros
  all_goals try simp_all [WGKernelView.ofKernel, WhileVariant.eval, SVal.evalsTo, SVal.uncurry]
  all_goals cases hr : (show ForInStep (Nat × Int) from by assumption) <;>
    simp_all [WGKernelView.ofKernel, SVal.curry]

theorem pipeRead_sameWGKernel (iocb : Kiocb) (count : Nat) :
    SameWGKernel (pipeRead iocb count) := by
  rw [pipeRead_eq]
  have loop_spec := fun P iocb filp pid count totalLen ret =>
    (readLoop_sameWGKernel iocb filp pid count totalLen ret).wp P
  frame_wg [read] using [getFile_spec, pipeOf_spec, getPipe_spec, loop_spec,
    killFasync_spec, fileAccessed_spec, wakeUpInterruptibleSyncPoll_spec]

theorem pipeRead_spec (P : WGKernelView → Prop) (iocb : Kiocb) (count : Nat) :
    ⦃fun w => ⌜P (wgKernelView w)⌝⦄ pipeRead iocb count
    ⦃⇓? _ w => ⌜P (wgKernelView w)⌝⦄ := (pipeRead_sameWGKernel iocb count).wp P

end Leanux.Proofs.Framing.PipeFrames
