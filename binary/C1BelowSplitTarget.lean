import AllowedipsMutationCodeLayout
import AllowedipsChild
import TrustBase
import Memory

/- Origin: trial source binary-trials/t1/Target.lean (copied in t5) on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-!
Stage 3 of the Ascent probe: the frozen target.

The segment is `Add.entry + 0x338 .. + 0x38c / + 0x6c0` of `add.isra.0` in the s5 image
(regions `Add.r338`, `Add.r35a`, `Add.r373`; 22 instructions, no call). In the C it is the
intermediate-node case of `add()`, after the fresh internal node `node` has been initialized:
the tail of `choose_and_connect_node(node, down)` (the two stores of `connect_node`), then all
of `choose_and_connect_node(node, newnode)`, then the test of `if (!parent)`.

This file holds definitions and the proposition only. `Target.Statement` is what both arms
prove; nothing here is a proof about the execution.
-/

namespace Binary.SplitStage3
open AllowedipsMutationImage TrustBase AllowedipsChild
local instance : Labels := Image.linkedLabels

/-- `sizeof(struct allowedips_node)` in the s5 build. -/
def nodeSize : Nat := 72

/-- `&parent->bit[bit]`: the two child pointers are at offsets 8 and 16. -/
def slot (parent : BitVec 64) (bit : Nat) : BitVec 64 := parent + .ofNat 64 (8 + 8 * bit)

/-- The value of `parent_bit_packed` (offset 48 of the child) that `connect_node` stores:
`(unsigned long)&parent->bit[bit] | bit`. -/
def packed (parent : BitVec 64) (bit : Nat) : BitVec 64 := slot parent bit ||| .ofNat 64 bit

/-- The four stores of the segment, in the image's order: `down->parent_bit_packed`,
`node->bit[direction]`, `newnode->parent_bit_packed`, `node->bit[bit]`. -/
def connected (m : DataMem) (node down newnode : BitVec 64) (direction bit : Nat) : DataMem :=
  (((m.storeInt (down + 48) 8 (packed node direction).toInt).storeInt
      (slot node direction) 8 down.toInt).storeInt
      (newnode + 48) 8 (packed node bit).toInt).storeInt
      (slot node bit) 8 newnode.toInt

/-- The bytes the segment may write. -/
def Writes (node down newnode : BitVec 64) (direction bit : Nat) (a : BitVec 64) : Prop :=
  InRange (down + 48) 8 a ∨ InRange (slot node direction) 8 a ∨
    InRange (newnode + 48) 8 a ∨ InRange (slot node bit) 8 a

/-- The state at `Add.entry + 0x338`. `r12` is `node` (the fresh internal node), `rdi` is
`down`, `r8` is `newnode`. `direction` is the bit `choose(node, down->bits)` selected, as the
instructions before the segment leave it in `rax`, `rdx` and (plus one) `rcx`. `byteIndex` and
`shift` are `node->bit_at_a` and `node->bit_at_b`; `byte` is `newnode->bits[byteIndex]`. The
three loads are in the entry memory. The three node objects do not overlap. -/
structure Entry (s : MachineData) (direction byteIndex shift byte : Nat) : Prop where
  directionBound : direction < 2
  rax : s.regs.rax = .ofNat direction
  rdx : s.regs.rdx = .ofNat direction
  rcx : s.regs.rcx = .ofNat (direction + 1)
  indexRead : s.dmem.loadInt (s.regs.r12.toBitVec + 25) 1 = some (byteIndex : Int)
  shiftRead : s.dmem.loadInt (s.regs.r12.toBitVec + 26) 1 = some (shift : Int)
  byteRead : s.dmem.loadInt (s.regs.r8.toBitVec + 32 + .ofNat 64 byteIndex) 1 = some (byte : Int)
  indexBound : byteIndex < 16
  shiftBound : shift < 8
  byteBound : byte < 256
  downParentMapped : (s.dmem.loadInt (s.regs.rdi.toBitVec + 48) 8).isSome = true
  leftMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 8) 8).isSome = true
  rightMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 16) 8).isSome = true
  newParentMapped : (s.dmem.loadInt (s.regs.r8.toBitVec + 48) 8).isSome = true
  nodeDown : ∀ a, InRange s.regs.r12.toBitVec nodeSize a → ¬InRange s.regs.rdi.toBitVec nodeSize a
  nodeNew : ∀ a, InRange s.regs.r12.toBitVec nodeSize a → ¬InRange s.regs.r8.toBitVec nodeSize a
  downNew : ∀ a, InRange s.regs.rdi.toBitVec nodeSize a → ¬InRange s.regs.r8.toBitVec nodeSize a

/-- The state at the exit: `Add.entry + 0x6c0` when `parent` (`rbx`) is NULL, `Add.entry + 0x38c`
otherwise. The memory is the entry memory with the four stores, the values written in terms of
the entry state. `rax`, `rcx`, `rdx` hold the selected bit, the slot and the packed word; the
registers the code after either exit reads, and the callee-saved ones, are unchanged. -/
def Exit (s : MachineData) (direction shift byte : Nat) (t : MachineState) : Prop :=
  let node := s.regs.r12.toBitVec
  let bit := selected byte shift
  t.pc = (if s.regs.rbx = 0 then Add.entry + 0x6c0 else Add.entry + 0x38c) ∧
  t.data.dmem = connected s.dmem node s.regs.rdi.toBitVec s.regs.r8.toBitVec direction bit ∧
  t.data.regs.rax = .ofNat bit ∧
  t.data.regs.rcx = .ofBitVec (slot node bit) ∧
  t.data.regs.rdx = .ofBitVec (packed node bit) ∧
  t.data.regs.rbx = s.regs.rbx ∧ t.data.regs.rsp = s.regs.rsp ∧ t.data.regs.rbp = s.regs.rbp ∧
  t.data.regs.rdi = s.regs.rdi ∧ t.data.regs.r8 = s.regs.r8 ∧ t.data.regs.r12 = s.regs.r12 ∧
  t.data.regs.r13 = s.regs.r13 ∧ t.data.regs.r14 = s.regs.r14 ∧ t.data.regs.r15 = s.regs.r15

end Binary.SplitStage3

namespace SplitTarget
open Binary Binary.SplitStage3 AllowedipsMutationImage TrustBase

/-- The frozen target. Both arms prove `theorem … : SplitTarget.Statement`. -/
def Statement : Prop :=
  ∀ (fetch : Int64 → Option Decoded), AllowedipsMutationDecoderAgreement fetch →
  ∀ (s : MachineData) (direction byteIndex shift byte : Nat),
    Entry s direction byteIndex shift byte →
    Eventually (@instructionStep Image.linkedLabels fetch)
      (Exit s direction shift byte) ⟨s, Add.entry + 0x338⟩

end SplitTarget
