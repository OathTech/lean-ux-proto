import CommonBitsCalls
import CommonBitsExecution
import CommonBitsResults

namespace Binary.CommonBits
open TrustBase
local instance : Labels := Image.linkedLabels

/-- One concrete byte-level read. Lists below are frames over actual memory,
    not certificates or predicates standing for future execution. -/
structure ReadWord where
  address : BitVec 64
  width : Nat
  value : Int

def ReadsAt (words : List ReadWord) (memory : Mem 64) : Prop :=
  ∀ word ∈ words, memory.loadInt word.address word.width = some word.value

def ReadBytes (words : List ReadWord) (a : BitVec 64) : Prop :=
  ∃ word ∈ words, InRange word.address word.width a

theorem ReadsAt.frame {words before after writes}
    (reads : ReadsAt words before) (frame : EqualOutside writes before after)
    (apart : ∀ a, ReadBytes words a → ¬writes a) : ReadsAt words after := by
  intro word member
  have same := frame.loadInt word.address word.width
    (fun i hi => apart _ ⟨word, member, i, hi, rfl⟩)
  exact same.symm.trans (reads word member)

/-- The data used by this invocation. Unselected family fields impose no reads. -/
structure Input where
  node : UInt64
  key : UInt64
  stack : UInt64
  family : BitVec 8
  stored32 : UInt32
  query32 : UInt32
  storedHigh : UInt64
  queryHigh : UInt64
  storedLow : UInt64
  queryLow : UInt64
  savedBx : UInt64
  savedBp : UInt64
  savedR12 : UInt64
  savedR13 : UInt64
  returnAddress : UInt64

/-- Every path reads the five saved words. Key reads follow the family and
    high-word decision exactly, including the equal-key low-word path. -/
def Input.words (i : Input) : List ReadWord :=
  [⟨i.stack.toBitVec, 8, i.savedBx.toNat⟩,
   ⟨i.stack.toBitVec+8, 8, i.savedBp.toNat⟩,
   ⟨i.stack.toBitVec+16, 8, i.savedR12.toNat⟩,
   ⟨i.stack.toBitVec+24, 8, i.savedR13.toNat⟩,
   ⟨i.stack.toBitVec+32, 8, i.returnAddress.toNat⟩] ++
  if i.family = 32 then
    [⟨i.node.toBitVec+32, 4, i.stored32.toNat⟩, ⟨i.key.toBitVec, 4, i.query32.toNat⟩]
  else if i.family = 128 then
    [⟨i.node.toBitVec+32, 8, i.storedHigh.toNat⟩, ⟨i.key.toBitVec, 8, i.queryHigh.toNat⟩] ++
    if i.storedHigh = i.queryHigh then
      [⟨i.node.toBitVec+40, 8, i.storedLow.toNat⟩, ⟨i.key.toBitVec+8, 8, i.queryLow.toNat⟩]
    else []
  else []

def Input.result (i : Input) : Nat :=
  if i.family = 32 then 32-Leanux.WG.fls (i.stored32.toNat ^^^ i.query32.toNat)
  else if i.family = 128 then
    if i.storedHigh = i.queryHigh then
      128-Leanux.WG.fls (i.storedLow.toNat ^^^ i.queryLow.toNat)
    else 128-(Leanux.WG.fls (i.storedHigh.toNat ^^^ i.queryHigh.toNat)+64)
  else 0

def Input.Writes (i : Input) (c : CommonBitsCoverage.Context) (a : BitVec 64) : Prop :=
  InRange (i.stack.toBitVec-8) 8 a ∨ c.writes a

def Input.Separated (i : Input) (c : CommonBitsCoverage.Context) : Prop :=
  ∀ a, ReadBytes i.words a → ¬i.Writes c a

structure BodyAt (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData) : Prop where
  ready : CommonBitsCoverage.CallsReady c s
  stack : s.regs.rsp = i.stack
  node : s.regs.r12 = i.node
  key : s.regs.r13 = i.key
  reads : ReadsAt i.words s.dmem

theorem BodyAt.same_memory {i c s t} (before : BodyAt i c s)
    (memory : t.dmem = s.dmem) (stack : t.regs.rsp = s.regs.rsp)
    (node : t.regs.r12 = s.regs.r12) (key : t.regs.r13 = s.regs.r13) : BodyAt i c t := by
  exact ⟨before.ready.congr memory stack, stack.trans before.stack,
    node.trans before.node, key.trans before.key, memory ▸ before.reads⟩

theorem BodyAt.after_callback {i c s t} (before : BodyAt i c s)
    (apart : i.Separated c) (ready : CommonBitsCoverage.CallsReady c t)
    (stack : t.regs.rsp = s.regs.rsp) (node : t.regs.r12 = s.regs.r12)
    (key : t.regs.r13 = s.regs.r13)
    (frame : EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ c.writes a)
      s.dmem t.dmem) : BodyAt i c t := by
  refine ⟨ready, stack.trans before.stack, node.trans before.node, key.trans before.key, ?_⟩
  apply before.reads.frame frame
  simpa only [Input.Separated, Input.Writes, before.stack] using apart

theorem BodyAt.stack_words {i c s} (state : BodyAt i c s) :
    s.dmem.loadInt s.regs.rsp.toBitVec 8 = some i.savedBx.toNat ∧
    s.dmem.loadInt (s.regs.rsp.toBitVec+8) 8 = some i.savedBp.toNat ∧
    s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8 = some i.savedR12.toNat ∧
    s.dmem.loadInt (s.regs.rsp.toBitVec+24) 8 = some i.savedR13.toNat ∧
    s.dmem.loadInt (s.regs.rsp.toBitVec+32) 8 = some i.returnAddress.toNat := by
  rw [state.stack]
  exact ⟨state.reads ⟨i.stack.toBitVec, 8, i.savedBx.toNat⟩ (by simp [Input.words]), state.reads ⟨i.stack.toBitVec+8, 8, i.savedBp.toNat⟩ (by simp [Input.words]),
    state.reads ⟨i.stack.toBitVec+16, 8, i.savedR12.toNat⟩ (by simp [Input.words]), state.reads ⟨i.stack.toBitVec+24, 8, i.savedR13.toNat⟩ (by simp [Input.words]),
    state.reads ⟨i.stack.toBitVec+32, 8, i.returnAddress.toNat⟩ (by simp [Input.words])⟩

theorem BodyAt.words32 {i c s} (state : BodyAt i c s) (family : i.family = 32) :
    s.dmem.loadInt (s.regs.r12.toBitVec+32) 4 = some i.stored32.toNat ∧
    s.dmem.loadInt s.regs.r13.toBitVec 4 = some i.query32.toNat := by
  rw [state.node, state.key]
  exact ⟨state.reads ⟨i.node.toBitVec+32, 4, i.stored32.toNat⟩ (by simp [Input.words, family]), state.reads ⟨i.key.toBitVec, 4, i.query32.toNat⟩ (by simp [Input.words, family])⟩

theorem BodyAt.wordsHigh {i c s} (state : BodyAt i c s) (family : i.family = 128) :
    s.dmem.loadInt (s.regs.r12.toBitVec+32) 8 = some i.storedHigh.toNat ∧
    s.dmem.loadInt s.regs.r13.toBitVec 8 = some i.queryHigh.toNat := by
  rw [state.node, state.key]
  exact ⟨state.reads ⟨i.node.toBitVec+32, 8, i.storedHigh.toNat⟩ (by simp [Input.words, family]), state.reads ⟨i.key.toBitVec, 8, i.queryHigh.toNat⟩ (by simp [Input.words, family])⟩

theorem BodyAt.wordsLow {i c s} (state : BodyAt i c s)
    (family : i.family = 128) (equal : i.storedHigh = i.queryHigh) :
    s.dmem.loadInt (s.regs.r12.toBitVec+40) 8 = some i.storedLow.toNat ∧
    s.dmem.loadInt (s.regs.r13.toBitVec+8) 8 = some i.queryLow.toNat := by
  rw [state.node, state.key]
  exact ⟨state.reads ⟨i.node.toBitVec+40, 8, i.storedLow.toNat⟩ (by simp [Input.words, family, equal]),
    state.reads ⟨i.key.toBitVec+8, 8, i.queryLow.toNat⟩ (by simp [Input.words, family, equal])⟩

end Binary.CommonBits
