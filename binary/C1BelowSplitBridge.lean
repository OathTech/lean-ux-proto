import C1BelowSplitDirect
import C1BelowSplitReconstruct

/- Origin: trial source binary-trials/t5/T5Bridge.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 3 (first piece): t1's machine memory after its 22 instructions,
written as bit-vector `storeInt`s, is the stage-1 memory after the first two
connections (`connectMemory` over natural-number addresses). -/
namespace Binary.Pair.Allowedips.C1Split
open Binary.SplitStage3

theorem slot_ofNat (p b : Nat) : slot (.ofNat 64 p) b=.ofNat 64 (p+8+b*8) := by
  unfold slot
  rw [←BitVec.ofNat_add]
  congr 1
  omega

theorem packed_ofNat (p b : Nat) : packed (.ofNat 64 p) b=.ofNat 64 ((p+(b+1)*8) ||| b) := by
  unfold packed
  rw [slot_ofNat,←BitVec.ofNat_or]
  congr 2
  omega

theorem field_ofNat (p : Nat) : (BitVec.ofNat 64 p)+48=.ofNat 64 (p+48) := by
  rw [BitVec.ofNat_add]
  rfl

/-- t1's `connected` memory is the first two `connectMemory` steps of stage 1. -/
theorem connected_connectMemory (m : DataMem) (node down newnode direction bit : Nat) :
    connected m (.ofNat 64 node) (.ofNat 64 down) (.ofNat 64 newnode) direction bit=
      connectMemory (connectMemory m down (node+8+direction*8) ((node+(direction+1)*8) ||| direction))
        newnode (node+8+bit*8) ((node+(bit+1)*8) ||| bit) := by
  simp only [connected,connectMemory,write64,slot_ofNat,packed_ofNat,field_ofNat]

#print axioms connected_connectMemory
end Binary.Pair.Allowedips.C1Split
