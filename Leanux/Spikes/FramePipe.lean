import Leanux.Spikes.FramePipeAux
import Leanux.FS.Pipe

set_option pp.structureInstances false

/-! Local progress measures and receive-state framing for the unchanged pipe
operations. The measures apply to successful continuations from arbitrary
states; inconsistent inputs may stop in the original helpers. -/
namespace Leanux.Spikes.Lifetimes.PipeFrames
open Leanux Leanux.WG Std.Do Leanux.Spikes.Framing
open Leanux.Spikes.Lifetimes Leanux.Spikes.Lifetimes.KernelFrames
open Leanux.Spikes.Lifetimes.PipeAux

set_option maxHeartbeats 1200000

theorem pipeOccupancy_tail_succ (head tail : UInt32) (hne : head ≠ tail) :
    pipeOccupancy head (tail + 1) + 1 = pipeOccupancy head tail := by
  have hn : (head - tail).toNat ≠ 0 := by
    intro hz
    have hz' : head - tail = 0 :=
      UInt32.toNat_inj.mp (by simpa only [UInt32.toNat_zero] using hz)
    exact hne ((UInt32.sub_eq_iff_eq_add.mp hz').trans (UInt32.zero_add tail))
  have hle : (1 : UInt32) ≤ head - tail := by
    apply UInt32.le_iff_toNat_le.mpr
    change 1 ≤ (head - tail).toNat
    omega
  have hs : head - (tail + 1) = (head - tail) - 1 := by
    apply UInt32.toBitVec_inj.mp
    simpa only [UInt32.toBitVec_sub, UInt32.toBitVec_add] using
      (BitVec.sub_sub head.toBitVec tail.toBitVec (1 : UInt32).toBitVec).symm
  unfold pipeOccupancy
  rw [hs, UInt32.toNat_sub_of_le _ _ hle]
  change (head - tail).toNat - 1 + 1 = (head - tail).toNat
  omega

theorem iovIter_count_advance (src : IovIter) (n : Nat) (hn : n ≤ src.count) :
    ({ src with pos := src.pos + n } : IovIter).count + n = src.count := by
  change (src.bytes.size - (src.pos + n)) + n = src.bytes.size - src.pos
  rw [← Nat.sub_sub]
  exact Nat.sub_add_cancel hn

theorem pipeOf_sameSnapshot (f : File) : SameSnapshot (pipeOf f) := by
  frame_same [pipeOf] using []

theorem pipeOf_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ pipeOf f ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (pipeOf_sameSnapshot f).wp P

theorem pipeBufIdx_sameSnapshot (p : PipeInodeInfo) (slot : UInt32) :
    SameSnapshot (pipeBufIdx p slot) := by
  frame_same [pipeBufIdx] using []

theorem getPipeBuf_sameSnapshot (pid : PipeId) (i : Nat) :
    SameSnapshot (getPipeBuf pid i) := by
  frame_same [getPipeBuf] using [getPipe_spec]

theorem setPipeBuf_sameSnapshot (pid : PipeId) (i : Nat) (b : PipeBuffer) :
    SameSnapshot (setPipeBuf pid i b) := by
  frame_same [setPipeBuf] using [getPipe_spec, setPipe_spec]

theorem newPipePage_sameSnapshot : SameSnapshot newPipePage := by
  frame_same [newPipePage] using [setPage_spec]

theorem putPipePage_sameSnapshot (page : PageId) : SameSnapshot (putPipePage page) := by
  frame_same [putPipePage] using [getPage_spec, setPage_spec]

theorem copyPageToIter_sameKernel (page : PageId) (offset bytes cap : Nat) :
    SameKernel (copyPageToIter page offset bytes cap) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [copyPageToIter, envOk, getPage, getK, invariant]

theorem copyPageFromIter_progress (page : PageId) (offset bytes : Nat) (src : IovIter)
    (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ copyPageFromIter page offset bytes src
    ⦃⇓? r w => ⌜P (snapshot w) ∧ r.2.count + r.1 = src.count⌝⦄ := by
  mvcgen [copyPageFromIter, envOk, getPage, setPage, getK, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [snapshot, iovIter_count_advance src _ (Nat.min_le_right bytes src.count)]

theorem killFasync_sameSnapshot (hasList : Bool) : SameSnapshot (killFasync hasList) := by
  frame_same [killFasync] using []

theorem killFasync_spec (P : Snapshot → Prop) (hasList : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ killFasync hasList ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (killFasync_sameSnapshot hasList).wp P

/-- The release chain changes buffers, cached pages and page references, but
retains the ring size and indices used by the local loop measures. -/
def pipeView (pid : PipeId) (w : World) :=
  (snapshot w, (w.k.pipes[pid]?).map fun p => (p.ringSize, p.head, p.tail))

theorem pipeView_eq_ring (pid : PipeId) (w w' : World)
    (h : pipeView pid w' = pipeView pid w) :
    ((w'.k.pipes[pid]?).map (·.ringSize)).getD 0 =
      ((w.k.pipes[pid]?).map (·.ringSize)).getD 0 := by
  have hh := congrArg (fun v => (v.2.map (·.1)).getD 0) h
  simpa [pipeView, Option.map_map, Function.comp_def] using hh

theorem setPipeBuf_view_spec (pid : PipeId) (i : Nat) (buf : PipeBuffer)
    (P : Snapshot × Option (Nat × UInt32 × UInt32) → Prop) :
    ⦃fun w => ⌜P (pipeView pid w)⌝⦄ setPipeBuf pid i buf
    ⦃⇓? _ w => ⌜P (pipeView pid w)⌝⦄ := by
  mvcgen [setPipeBuf, getPipe, setPipe, getK, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [pipeView, snapshot]

theorem putPipePage_view_spec (pid : PipeId) (page : PageId)
    (P : Snapshot × Option (Nat × UInt32 × UInt32) → Prop) :
    ⦃fun w => ⌜P (pipeView pid w)⌝⦄ putPipePage page
    ⦃⇓? _ w => ⌜P (pipeView pid w)⌝⦄ := by
  mvcgen [putPipePage, getPage, setPage, getK, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [pipeView, snapshot]

theorem anonPipeBufRelease_view_spec (pid : PipeId) (buf : PipeBuffer)
    (P : Snapshot × Option (Nat × UInt32 × UInt32) → Prop) :
    ⦃fun w => ⌜P (pipeView pid w)⌝⦄ anonPipeBufRelease pid buf
    ⦃⇓? _ w => ⌜P (pipeView pid w)⌝⦄ := by
  have put_spec := fun page => putPipePage_view_spec pid page P
  mvcgen [anonPipeBufRelease, put_spec, getPipe, setPipe, getPage,
    getK, modifyK, branch, branchCmp, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [pipeView, snapshot]

theorem pipeBufRelease_view_spec (pid : PipeId) (i : Nat)
    (P : Snapshot × Option (Nat × UInt32 × UInt32) → Prop) :
    ⦃fun w => ⌜P (pipeView pid w)⌝⦄ pipeBufRelease pid i
    ⦃⇓? _ w => ⌜P (pipeView pid w)⌝⦄ := by
  have set_spec := fun i buf => setPipeBuf_view_spec pid i buf P
  have anon_spec := fun buf => anonPipeBufRelease_view_spec pid buf P
  mvcgen [pipeBufRelease, getPipeBuf, set_spec, anon_spec, getPipe, getK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [pipeView, snapshot]

theorem pipeBufRelease_sameSnapshot (pid : PipeId) (i : Nat) :
    SameSnapshot (pipeBufRelease pid i) := by
  apply sameSnapshot_of_wp
  intro initial
  exact pipeBufRelease_view_spec pid i (fun v => v.1 = initial)

theorem pipeBufRelease_view_wp (pid : PipeId) (i : Nat) (Q : World → Prop) :
    ⦃fun w => ⌜∀ w', pipeView pid w' = pipeView pid w → Q w'⌝⦄
      pipeBufRelease pid i ⦃⇓? _ w => ⌜Q w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x w' hq hr
  apply hq w'
  exact (hoare_iff_triple _ _ _).mpr
    (pipeBufRelease_view_spec pid i (fun v => v = pipeView pid w)) w x w' rfl hr

theorem pipeBufConfirm_sameSnapshot (buf : PipeBuffer) : SameSnapshot (pipeBufConfirm buf) := by
  frame_same [pipeBufConfirm] using []

theorem accountPipeBuffers_sameSnapshot (old new : Nat) :
    SameSnapshot (accountPipeBuffers old new) := by
  frame_same [accountPipeBuffers] using []

theorem freePipeInfo_sameSnapshot (pid : PipeId) : SameSnapshot (freePipeInfo pid) := by
  apply sameSnapshot_of_wp
  intro initial
  have account_spec := fun old new =>
    (accountPipeBuffers_sameSnapshot old new).wp (fun s => s = initial)
  have page_spec := fun page => (putPipePage_sameSnapshot page).wp (fun s => s = initial)
  mvcgen [freePipeInfo, account_spec, page_spec, pipeBufRelease_view_wp,
    getPipeBuf, getPipe, getK, modifyK, branch, invariant]
  invariants
  | inv1 => fun i w => ⟨((w.k.pipes[pid]?).map (·.ringSize)).getD 0 - i⟩
  | inv2 => ((⇓? _ w => ⌜snapshot w = initial⌝) : PostCond _ (.arg World (.except Stop .pure)))
  case vc4.Q =>
    let current : World := by assumption
    exact fun w' => pipeView pid w' = pipeView pid current
  all_goals try dsimp +zetaDelta only at *
  all_goals try (letI : Nonempty World := ⟨by assumption⟩; infer_instance)
  all_goals try intros
  all_goals try have hr := pipeView_eq_ring pid _ _ (by assumption)
  all_goals try simp_all [WhileVariant.eval, SVal.evalsTo, SVal.uncurry, pipeView, snapshot]
  all_goals try omega

theorem freePipeInfo_spec (P : Snapshot → Prop) (pid : PipeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ freePipeInfo pid ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (freePipeInfo_sameSnapshot pid).wp P

theorem putPipeInfo_sameSnapshot (ino : PipefsInodeId) (pid : PipeId) :
    SameSnapshot (putPipeInfo ino pid) := by
  frame_same [putPipeInfo] using [getPipe_spec, setPipe_spec, getInode_spec,
    setInode_spec, freePipeInfo_spec]

theorem putPipeInfo_spec (P : Snapshot → Prop) (ino : PipefsInodeId) (pid : PipeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ putPipeInfo ino pid ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (putPipeInfo_sameSnapshot ino pid).wp P

theorem pipeRelease_sameSnapshot (ino : PipefsInodeId) (fid : FileId) :
    SameSnapshot (pipeRelease ino fid) := by
  frame_same [pipeRelease] using [getFile_spec, pipeOf_spec, getPipe_spec,
    setPipe_spec, killFasync_spec, putPipeInfo_spec]

/-- Proof-side name for the exact original write-loop continuation. The
following equality checks the factoring against the pinned operational body. -/
def writeLoop (iocb : Kiocb) (filp : File) (pid : PipeId) (src : IovIter)
    (ret : Int) : M Int := do
  let mut src := src
  let mut ret := ret
  repeat
    let p ← getPipe pid
    if ← branch .pipeWriteLoopNoReaders (p.readers == 0) then
      _ ← sendSig SIGPIPE 0
      if ← branchCmp .pipeWriteLoopNoRet (ret == 0) ret 0 then ret := -EPIPE
      break
    let head := p.head
    if ← branchCmp .pipeWriteNotFull (!pipeFull head p.tail p.maxUsage) (pipeOccupancy head p.tail) p.maxUsage then
      let mut page := p.tmpPage
      if ← branch .pipeWriteNoTmpPage page.isNone then
        -- alloc_page(GFP_HIGHUSER | __GFP_ACCOUNT)
        if ← branch .pipeWriteAllocFailed !(← hiddenAlloc .allocPipePage) then
          -- `ret = ret ? : -ENOMEM`
          if !(← branchCmp .pipeWriteAllocRet (ret != 0) ret 0) then ret := -ENOMEM
          break
        let pg ← newPipePage
        page := some pg
        setPipe pid { (← getPipe pid) with tmpPage := some pg }
      let some pg := page | invariant "unreachable"
      -- Allocate a slot in the ring in advance and attach an empty buffer.
      setPipe pid { (← getPipe pid) with head := head + 1 }
      let i ← pipeBufIdx (← getPipe pid) head
      -- `is_packetized(filp)` (411-414): `(file->f_flags & O_DIRECT) != 0`
      let flags := if ← branchCmp .pipeWritePacketized (hasFlag filp.fFlags O_DIRECT)
          (filp.fFlags &&& O_DIRECT).toNat 0 then PIPE_BUF_FLAG_PACKET else PIPE_BUF_FLAG_CAN_MERGE
      setPipeBuf pid i { page := some pg, ops := true, offset := 0, len := 0, flags }
      setPipe pid { (← getPipe pid) with tmpPage := none }
      let (copied, src') ← copyPageFromIter pg 0 PAGE_SIZE src
      src := src'
      -- `unlikely(copied < PAGE_SIZE && iov_iter_count(from))`
      let fault ← do
        if ← branchCmp .pipeWriteShortCopy (copied < PAGE_SIZE) copied PAGE_SIZE then
          branchCmp .pipeWriteShortCopyLeft (src.count != 0) src.count 0
        else pure false
      if fault then
        if ← branchCmp .pipeWriteFaultNoRet (ret == 0) ret 0 then ret := -EFAULT
        break
      ret := ret + copied
      setPipeBuf pid i { (← getPipeBuf pid i) with len := copied }
      if ← branchCmp .pipeWriteDone (src.count == 0) src.count 0 then break
    -- the local `head` (505): one behind `pipe->head` after an insertion (526)
    let p ← getPipe pid
    if ← branch .pipeWriteStaleNotFull (!pipeFull head p.tail p.maxUsage) then
      continue
    -- Wait for buffer space to become available.
    let nonblock ← do
      if ← branchCmp .pipeWriteNonblock (hasFlag filp.fFlags O_NONBLOCK) (filp.fFlags &&& O_NONBLOCK).toNat 0 then
        pure true
      else branchCmp .pipeWriteNowait (hasFlag iocb.kiFlags IOCB_NOWAIT) (iocb.kiFlags &&& IOCB_NOWAIT).toNat 0
    if nonblock then
      if ← branchCmp .pipeWriteNoRet (ret == 0) ret 0 then ret := -EAGAIN
      break
    unsupported "pipe_write: blocking wait (signal_pending, wait_event_interruptible_exclusive)"
  return ret

def writeToOut (iocb : Kiocb) (filp : File) (pid : PipeId) (src : IovIter) : M (Int × Bool) := do
  let totalLen := src.count
  let mut src := src
  -- mutex_lock(&pipe->mutex)
  let p ← getPipe pid
  if ← branchCmp .pipeWriteNoReaders (p.readers == 0) p.readers 0 then
    _ ← sendSig SIGPIPE 0
    return (-EPIPE, false)
  -- If it wasn't empty we try to merge new data into the last buffer.
  let head := p.head
  let wasEmpty := head == p.tail
  let chars := totalLen % PAGE_SIZE  -- total_len & (PAGE_SIZE-1)
  let mut ret : Int := 0
  let merge ← do
    if ← branchCmp .pipeWriteChars (chars != 0) chars 0 then branch .pipeWriteNotWasEmpty !wasEmpty
    else pure false
  if merge then
    let i ← pipeBufIdx p (head - 1)
    let buf ← getPipeBuf pid i
    let offset := buf.offset + buf.len
    let fits ← do
      if ← branchCmp .pipeWriteCanMerge (hasFlag buf.flags PIPE_BUF_FLAG_CAN_MERGE)
          (buf.flags &&& PIPE_BUF_FLAG_CAN_MERGE).toNat 0 then
        branchCmp .pipeWriteFits (offset + chars <= PAGE_SIZE) (offset + chars) PAGE_SIZE
      else pure false
    if fits then
      ret ← pipeBufConfirm buf
      if ← branch .pipeWriteMergeConfirmErr (ret != 0) then return (ret, wasEmpty)
      let some page := buf.page | invariant "pipe_write: a buffer with a NULL page"
      let (n, src') ← copyPageFromIter page offset chars src
      src := src'
      ret := n
      if ← branchCmp .pipeWriteMergeShort (ret < chars) ret chars then return (-EFAULT, wasEmpty)
      setPipeBuf pid i { (← getPipeBuf pid i) with len := buf.len + n }
      if ← branchCmp .pipeWriteMergeDone (src.count == 0) src.count 0 then return (ret, wasEmpty)
  let result ← writeLoop iocb filp pid src ret
  return (result, wasEmpty)

theorem pipeWriteToOut_eq (iocb : Kiocb) (filp : File) (pid : PipeId) (src : IovIter) :
    pipeWriteToOut iocb filp pid src = writeToOut iocb filp pid src := by
  simp only [pipeWriteToOut, writeToOut, writeLoop,
    bind_assoc, pure_bind]
  rfl

theorem writeLoop_sameSnapshot (iocb : Kiocb) (filp : File) (pid : PipeId)
    (src : IovIter) (ret : Int) : SameSnapshot (writeLoop iocb filp pid src ret) := by
  apply sameSnapshot_of_wp
  intro initial
  have copy_spec := fun page offset bytes src =>
    copyPageFromIter_progress page offset bytes src (fun s => s = initial)
  have sig_spec := sendSig_spec (fun s => s = initial)
  have alloc_spec := hiddenAlloc_snapshot_spec (fun s => s = initial)
  have new_spec := newPipePage_sameSnapshot.wp (fun s => s = initial)
  have set_spec := setPipe_spec (fun s => s = initial)
  have setbuf_spec := fun pid i buf =>
    (setPipeBuf_sameSnapshot pid i buf).wp (fun s => s = initial)
  have getbuf_spec := fun pid i =>
    (getPipeBuf_sameSnapshot pid i).wp (fun s => s = initial)
  have idx_spec := fun p slot => (pipeBufIdx_sameSnapshot p slot).wp (fun s => s = initial)
  mvcgen [writeLoop, copy_spec, sig_spec, alloc_spec, new_spec,
    set_spec, setbuf_spec, getbuf_spec, idx_spec,
    getPipe, getK, branch, branchCmp, invariant, unsupported]
  invariants
  | inv1 => fun b _ => ⟨b.1.count⟩
  | inv2 => ((⇓? _ w => ⌜snapshot w = initial⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (letI : Nonempty World := ⟨by assumption⟩; infer_instance)
  all_goals try intros
  all_goals try simp_all [WhileVariant.eval, SVal.evalsTo, SVal.uncurry, snapshot, PAGE_SIZE]
  all_goals try have hn := of_decide_eq_false (p := _ < (4096 : Nat)) (by assumption)
  all_goals omega

theorem copyPageFromIter_sameSnapshot (page : PageId) (offset bytes : Nat) (src : IovIter) :
    SameSnapshot (copyPageFromIter page offset bytes src) := by
  frame_same [copyPageFromIter] using [envOk_spec, getPage_spec, setPage_spec]

theorem pipeWriteToOut_sameSnapshot (iocb : Kiocb) (filp : File) (pid : PipeId)
    (src : IovIter) : SameSnapshot (pipeWriteToOut iocb filp pid src) := by
  rw [pipeWriteToOut_eq]
  have loop_spec := fun P iocb filp pid src ret =>
    (writeLoop_sameSnapshot iocb filp pid src ret).wp P
  have copy_spec := fun P page offset bytes src =>
    (copyPageFromIter_sameSnapshot page offset bytes src).wp P
  have idx_spec := fun P p slot => (pipeBufIdx_sameSnapshot p slot).wp P
  have getbuf_spec := fun P pid i => (getPipeBuf_sameSnapshot pid i).wp P
  have setbuf_spec := fun P pid i buf => (setPipeBuf_sameSnapshot pid i buf).wp P
  have confirm_spec := fun P buf => (pipeBufConfirm_sameSnapshot buf).wp P
  frame_same [writeToOut] using [getPipe_spec, sendSig_spec, loop_spec,
    copy_spec, idx_spec, getbuf_spec, setbuf_spec, confirm_spec]

theorem pipeWriteToOut_spec (P : Snapshot → Prop) (iocb : Kiocb) (filp : File)
    (pid : PipeId) (src : IovIter) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ pipeWriteToOut iocb filp pid src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipeWriteToOut_sameSnapshot iocb filp pid src).wp P

theorem pipeWrite_sameSnapshot (iocb : Kiocb) (src : IovIter) :
    SameSnapshot (pipeWrite iocb src) := by
  frame_same [pipeWrite] using [getFile_spec, pipeOf_spec, pipeWriteToOut_spec,
    getPipe_spec, killFasync_spec, fileUpdateTime_spec]

theorem pipeWrite_spec (P : Snapshot → Prop) (iocb : Kiocb) (src : IovIter) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ pipeWrite iocb src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipeWrite_sameSnapshot iocb src).wp P

end Leanux.Spikes.Lifetimes.PipeFrames
