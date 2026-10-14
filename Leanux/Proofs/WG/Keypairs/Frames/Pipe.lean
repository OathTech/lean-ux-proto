import Leanux.Proofs.Framing.Pipe
import Leanux.Proofs.WG.Keypairs.Frames.PipeAux
import Leanux.Proofs.WG.Keypairs.Frames.Wait
import Leanux.FS.Pipe

set_option pp.structureInstances false

/-! Compatibility progress measures and receive-state framing for the unchanged pipe
operations. The measures apply to successful continuations from arbitrary
states; inconsistent inputs may stop in the original helpers. -/
namespace Leanux.Proofs.WG.Keypairs.PipeFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing
open Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.KernelFrames
open Leanux.Proofs.WG.Keypairs.PipeAux Leanux.Proofs.WG.Keypairs.WaitFrames

set_option maxHeartbeats 1200000

theorem pipeOccupancy_tail_succ (head tail : UInt32) (hne : head ≠ tail) :
    pipeOccupancy head (tail + 1) + 1 = pipeOccupancy head tail := by
  exact Framing.PipeFrames.pipeOccupancy_tail_succ head tail hne

theorem iovIter_count_advance (src : IovIter) (n : Nat) (hn : n ≤ src.count) :
    ({ src with pos := src.pos + n } : IovIter).count + n = src.count :=
  Framing.PipeFrames.iovIter_count_advance src n hn

theorem pipeOf_sameSnapshot (f : File) : SameSnapshot (pipeOf f) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.pipeOf_sameWGKernel

theorem pipeOf_spec (P : Snapshot → Prop) (f : File) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ pipeOf f ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (pipeOf_sameSnapshot f).wp P

theorem pipeBufIdx_sameSnapshot (p : PipeInodeInfo) (slot : UInt32) :
    SameSnapshot (pipeBufIdx p slot) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.pipeBufIdx_sameWGKernel

theorem getPipeBuf_sameSnapshot (pid : PipeId) (i : Nat) :
    SameSnapshot (getPipeBuf pid i) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.getPipeBuf_sameWGKernel

theorem setPipeBuf_sameSnapshot (pid : PipeId) (i : Nat) (b : PipeBuffer) :
    SameSnapshot (setPipeBuf pid i b) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.setPipeBuf_sameWGKernel

theorem newPipePage_sameSnapshot : SameSnapshot newPipePage := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.newPipePage_sameWGKernel

theorem putPipePage_sameSnapshot (page : PageId) : SameSnapshot (putPipePage page) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.putPipePage_sameWGKernel

theorem copyPageToIter_sameKernel (page : PageId) (offset bytes cap : Nat) :
    SameKernel (copyPageToIter page offset bytes cap) := by
  apply Framing.PipeFrames.copyPageToIter_sameKernel

theorem copyPageFromIter_progress (page : PageId) (offset bytes : Nat) (src : IovIter)
    (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ copyPageFromIter page offset bytes src
    ⦃⇓? r w => ⌜P (snapshot w) ∧ r.2.count + r.1 = src.count⌝⦄ :=
  Framing.PipeFrames.copyPageFromIter_progress page offset bytes src (fun v => P (snapshotOfWGKernelView v))

theorem killFasync_sameSnapshot (hasList : Bool) : SameSnapshot (killFasync hasList) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.killFasync_sameWGKernel

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
    ⦃⇓? _ w => ⌜P (pipeView pid w)⌝⦄ :=
  Framing.PipeFrames.setPipeBuf_view_spec pid i buf (fun v => P (snapshotOfWGKernelView v.1, v.2))

theorem putPipePage_view_spec (pid : PipeId) (page : PageId)
    (P : Snapshot × Option (Nat × UInt32 × UInt32) → Prop) :
    ⦃fun w => ⌜P (pipeView pid w)⌝⦄ putPipePage page
    ⦃⇓? _ w => ⌜P (pipeView pid w)⌝⦄ :=
  Framing.PipeFrames.putPipePage_view_spec pid page (fun v => P (snapshotOfWGKernelView v.1, v.2))

theorem anonPipeBufRelease_view_spec (pid : PipeId) (buf : PipeBuffer)
    (P : Snapshot × Option (Nat × UInt32 × UInt32) → Prop) :
    ⦃fun w => ⌜P (pipeView pid w)⌝⦄ anonPipeBufRelease pid buf
    ⦃⇓? _ w => ⌜P (pipeView pid w)⌝⦄ :=
  Framing.PipeFrames.anonPipeBufRelease_view_spec pid buf (fun v => P (snapshotOfWGKernelView v.1, v.2))

theorem pipeBufRelease_view_spec (pid : PipeId) (i : Nat)
    (P : Snapshot × Option (Nat × UInt32 × UInt32) → Prop) :
    ⦃fun w => ⌜P (pipeView pid w)⌝⦄ pipeBufRelease pid i
    ⦃⇓? _ w => ⌜P (pipeView pid w)⌝⦄ :=
  Framing.PipeFrames.pipeBufRelease_view_spec pid i (fun v => P (snapshotOfWGKernelView v.1, v.2))

theorem pipeBufRelease_sameSnapshot (pid : PipeId) (i : Nat) :
    SameSnapshot (pipeBufRelease pid i) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.pipeBufRelease_sameWGKernel

theorem pipeBufRelease_view_wp (pid : PipeId) (i : Nat) (Q : World → Prop) :
    ⦃fun w => ⌜∀ w', pipeView pid w' = pipeView pid w → Q w'⌝⦄
      pipeBufRelease pid i ⦃⇓? _ w => ⌜Q w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x w' hq hr
  apply hq w'
  exact (hoare_iff_triple _ _ _).mpr
    (pipeBufRelease_view_spec pid i (fun v => v = pipeView pid w)) w x w' rfl hr

theorem pipeBufConfirm_sameSnapshot (buf : PipeBuffer) : SameSnapshot (pipeBufConfirm buf) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.pipeBufConfirm_sameWGKernel

theorem accountPipeBuffers_sameSnapshot (old new : Nat) :
    SameSnapshot (accountPipeBuffers old new) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.accountPipeBuffers_sameWGKernel

theorem freePipeInfo_sameSnapshot (pid : PipeId) : SameSnapshot (freePipeInfo pid) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.freePipeInfo_sameWGKernel

theorem freePipeInfo_spec (P : Snapshot → Prop) (pid : PipeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ freePipeInfo pid ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (freePipeInfo_sameSnapshot pid).wp P

theorem putPipeInfo_sameSnapshot (ino : PipefsInodeId) (pid : PipeId) :
    SameSnapshot (putPipeInfo ino pid) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.putPipeInfo_sameWGKernel

theorem putPipeInfo_spec (P : Snapshot → Prop) (ino : PipefsInodeId) (pid : PipeId) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ putPipeInfo ino pid ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ :=
  (putPipeInfo_sameSnapshot ino pid).wp P

theorem pipeRelease_sameSnapshot (ino : PipefsInodeId) (fid : FileId) :
    SameSnapshot (pipeRelease ino fid) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.pipeRelease_sameWGKernel

/-- Proof-side name for the exact original write-loop continuation. The
following equality checks the factoring against the pinned operational body. -/
abbrev writeLoop := Framing.PipeFrames.writeLoop

abbrev writeToOut := Framing.PipeFrames.writeToOut

theorem pipeWriteToOut_eq (iocb : Kiocb) (filp : File) (pid : PipeId) (src : IovIter) :
    pipeWriteToOut iocb filp pid src = writeToOut iocb filp pid src := by
  apply Framing.PipeFrames.pipeWriteToOut_eq

theorem writeLoop_sameSnapshot (iocb : Kiocb) (filp : File) (pid : PipeId)
    (src : IovIter) (ret : Int) : SameSnapshot (writeLoop iocb filp pid src ret) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.writeLoop_sameWGKernel

theorem copyPageFromIter_sameSnapshot (page : PageId) (offset bytes : Nat) (src : IovIter) :
    SameSnapshot (copyPageFromIter page offset bytes src) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.copyPageFromIter_sameWGKernel

theorem pipeWriteToOut_sameSnapshot (iocb : Kiocb) (filp : File) (pid : PipeId)
    (src : IovIter) : SameSnapshot (pipeWriteToOut iocb filp pid src) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.pipeWriteToOut_sameWGKernel

theorem pipeWriteToOut_spec (P : Snapshot → Prop) (iocb : Kiocb) (filp : File)
    (pid : PipeId) (src : IovIter) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ pipeWriteToOut iocb filp pid src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipeWriteToOut_sameSnapshot iocb filp pid src).wp P

theorem pipeWrite_sameSnapshot (iocb : Kiocb) (src : IovIter) :
    SameSnapshot (pipeWrite iocb src) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.pipeWrite_sameWGKernel

theorem pipeWrite_spec (P : Snapshot → Prop) (iocb : Kiocb) (src : IovIter) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ pipeWrite iocb src
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipeWrite_sameSnapshot iocb src).wp P

end Leanux.Proofs.WG.Keypairs.PipeFrames
