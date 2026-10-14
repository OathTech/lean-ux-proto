import Leanux.Proofs.Framing.PipeRead
import Leanux.Proofs.WG.Keypairs.Frames.Pipe

namespace Leanux.Proofs.WG.Keypairs.PipeFrames
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing
open Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.KernelFrames
open Leanux.Proofs.WG.Keypairs.PipeAux Leanux.Proofs.WG.Keypairs.WaitFrames

set_option pp.structureInstances false
set_option maxHeartbeats 1500000

/-- Exact original read iteration, named only on the proof side. -/
abbrev readStep := Framing.PipeFrames.readStep

abbrev readLoop := Framing.PipeFrames.readLoop

abbrev read := Framing.PipeFrames.read

theorem pipeRead_eq (iocb : Kiocb) (count : Nat) :
    pipeRead iocb count = read iocb count := by
  apply Framing.PipeFrames.pipeRead_eq

abbrev occupancy := Framing.PipeFrames.occupancy

theorem pipeOccupancy_tail_lt (head tail : UInt32) (hne : head ≠ tail) :
    pipeOccupancy head (tail + 1) < pipeOccupancy head tail := by
  exact Framing.PipeFrames.pipeOccupancy_tail_lt head tail hne

theorem readStep_progress (iocb : Kiocb) (filp : File) (pid : PipeId)
    (count : Nat) (b : Nat × Int) (entry : World) :
    ⦃fun w => ⌜w = entry⌝⦄ readStep iocb filp pid count b
    ⦃⇓? r w => ⌜snapshot w = snapshot entry ∧
      match r with
      | .done _ => True
      | .yield _ => occupancy pid w < occupancy pid entry⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w r v hw hr
  obtain ⟨hf, hm⟩ := (hoare_iff_triple _ _ _).mpr
    (Framing.PipeFrames.readStep_progress iocb filp pid count b entry) w r v hw hr
  exact ⟨congrArg snapshotOfWGKernelView hf, hm⟩

theorem readStep_variant_spec (initial : Snapshot) (mb : Nat)
    (iocb : Kiocb) (filp : File) (pid : PipeId) (count : Nat) (b : Nat × Int) :
    ⦃fun w => ⌜mb = occupancy pid w ∧ snapshot w = initial⌝⦄ readStep iocb filp pid count b
    ⦃⇓? r w => ⌜match r with
      | .done _ => snapshot w = initial
      | .yield _ => occupancy pid w < mb ∧ snapshot w = initial⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w r w' hp hr
  have hs := (hoare_iff_triple _ _ _).mpr (readStep_progress iocb filp pid count b w)
    w r w' rfl hr
  cases r <;> simp_all

theorem readLoop_sameSnapshot (iocb : Kiocb) (filp : File) (pid : PipeId)
    (count totalLen : Nat) (ret : Int) :
    SameSnapshot (readLoop iocb filp pid count totalLen ret) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.readLoop_sameWGKernel

theorem pipeRead_sameSnapshot (iocb : Kiocb) (count : Nat) :
    SameSnapshot (pipeRead iocb count) := by
  apply sameSnapshot_of_sameWGKernel
  apply Framing.PipeFrames.pipeRead_sameWGKernel

theorem pipeRead_spec (P : Snapshot → Prop) (iocb : Kiocb) (count : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ pipeRead iocb count
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pipeRead_sameSnapshot iocb count).wp P

end Leanux.Proofs.WG.Keypairs.PipeFrames
