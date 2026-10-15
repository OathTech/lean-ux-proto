import CommonBitsStack
import History

namespace Binary.CommonBits
local instance : Labels := Image.linkedLabels

private theorem u64_sub_sub (a b c : UInt64) : a-b-c = a-(b+c) := by
  apply UInt64.toBitVec_inj.mp
  exact BitVec.sub_sub _ _ _

def savedCount : Nat → Nat
  | 0 => 0
  | 1 | 2 => 1
  | 3 | 4 => 2
  | 5 | 6 => 3
  | 7 | 8 => 4
  | _ => 5

def prologueData (s : MachineData) (n : Nat) : MachineData :=
  {s with dmem := saveMemory s (savedCount n), regs := {s.regs with
    rsp := s.regs.rsp - UInt64.ofNat (8 * savedCount n)
    r13 := if 2 ≤ n then s.regs.rsi else s.regs.r13
    r12 := if 4 ≤ n then s.regs.rdi else s.regs.r12
    rbp := if 6 ≤ n then .ofBitVec ((s.regs.get (.low .rdx .W32)).setWidth 64) else s.regs.rbp
    rbx := if 8 ≤ n then .ofBitVec ((s.regs.get (.low .rdx .W32)).setWidth 64) else s.regs.rbx}}

def prologueStates (s : MachineData) : List MachineState :=
  [⟨prologueData s 1, AllowedipsImage.CommonBits.entry+2⟩,
   ⟨prologueData s 2, AllowedipsImage.CommonBits.entry+5⟩,
   ⟨prologueData s 3, AllowedipsImage.CommonBits.entry+7⟩,
   ⟨prologueData s 4, AllowedipsImage.CommonBits.entry+10⟩,
   ⟨prologueData s 5, AllowedipsImage.CommonBits.entry+11⟩,
   ⟨prologueData s 6, AllowedipsImage.CommonBits.entry+13⟩,
   ⟨prologueData s 7, AllowedipsImage.CommonBits.entry+14⟩,
   ⟨prologueData s 8, AllowedipsImage.CommonBits.entry+16⟩,
   ⟨prologueData s 9, .ofNat 0xffffffff810f3100⟩]

private theorem history_cons (fetch : Int64 → Option Decoded) (s next : MachineState)
    (history : List MachineState) (n : Nat) (P : Executed → Prop)
    (first : instructionStep fetch s (fun t => t = next))
    (rest : historySteps fetch n P ⟨next, history ++ [next]⟩) :
    historySteps fetch (n+1) P ⟨s, history⟩ := by
  exact instruction_mono fetch s (fun t => t = next) _ (fun t ht => ht ▸ rest) first

private theorem instruction0 (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 0, AllowedipsImage.CommonBits.entry+0⟩
      (fun t => t = ⟨prologueData s 1, AllowedipsImage.CommonBits.entry+2⟩) := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+0) = some _ from rfl)
  have defined := saves_preserve_mapped s 0 _ (mapped 0 (by decide))
  obtain ⟨word, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    RelRegOrMem.interp, ConstExpr.interp,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords, AllowedipsImage.CommonBits.entry] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem instruction1 (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 1, AllowedipsImage.CommonBits.entry+2⟩
      (fun t => t = ⟨prologueData s 2, AllowedipsImage.CommonBits.entry+5⟩) := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+2) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    RelRegOrMem.interp, ConstExpr.interp,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords, AllowedipsImage.CommonBits.entry]
  try rfl

private theorem instruction2 (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 2, AllowedipsImage.CommonBits.entry+5⟩
      (fun t => t = ⟨prologueData s 3, AllowedipsImage.CommonBits.entry+7⟩) := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+5) = some _ from rfl)
  have defined := saves_preserve_mapped s 1 _ (mapped 1 (by decide))
  obtain ⟨word, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    RelRegOrMem.interp, ConstExpr.interp,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords, AllowedipsImage.CommonBits.entry] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem instruction3 (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 3, AllowedipsImage.CommonBits.entry+7⟩
      (fun t => t = ⟨prologueData s 4, AllowedipsImage.CommonBits.entry+10⟩) := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+7) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    RelRegOrMem.interp, ConstExpr.interp,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords, AllowedipsImage.CommonBits.entry]
  try rfl

private theorem instruction4 (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 4, AllowedipsImage.CommonBits.entry+10⟩
      (fun t => t = ⟨prologueData s 5, AllowedipsImage.CommonBits.entry+11⟩) := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+10) = some _ from rfl)
  have defined := saves_preserve_mapped s 2 _ (mapped 2 (by decide))
  obtain ⟨word, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    RelRegOrMem.interp, ConstExpr.interp,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords, AllowedipsImage.CommonBits.entry] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem instruction5 (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 5, AllowedipsImage.CommonBits.entry+11⟩
      (fun t => t = ⟨prologueData s 6, AllowedipsImage.CommonBits.entry+13⟩) := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+11) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    RelRegOrMem.interp, ConstExpr.interp,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords, AllowedipsImage.CommonBits.entry]
  try rfl

private theorem instruction6 (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 6, AllowedipsImage.CommonBits.entry+13⟩
      (fun t => t = ⟨prologueData s 7, AllowedipsImage.CommonBits.entry+14⟩) := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+13) = some _ from rfl)
  have defined := saves_preserve_mapped s 3 _ (mapped 3 (by decide))
  obtain ⟨word, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    RelRegOrMem.interp, ConstExpr.interp,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords, AllowedipsImage.CommonBits.entry] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem instruction7 (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 7, AllowedipsImage.CommonBits.entry+14⟩
      (fun t => t = ⟨prologueData s 8, AllowedipsImage.CommonBits.entry+16⟩) := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+14) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    RelRegOrMem.interp, ConstExpr.interp,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords, AllowedipsImage.CommonBits.entry]
  try rfl

private theorem instruction8 (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 8, AllowedipsImage.CommonBits.entry+16⟩
      (fun t => t = ⟨prologueData s 9, .ofNat 0xffffffff810f3100⟩) := by
  have here := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry+16) = some _ from rfl)
  have defined := saves_preserve_mapped s 4 _ (mapped 4 (by decide))
  obtain ⟨word, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    RelRegOrMem.interp, ConstExpr.interp,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords, AllowedipsImage.CommonBits.entry] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

/-- All nine real successors, through the first callback's actual CALL. -/
theorem prologue_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    historySteps fetch 9 (fun t =>
      t.machine = ⟨prologueData s 9, .ofNat 0xffffffff810f3100⟩ ∧
      t.history = history ++ prologueStates s) ⟨⟨s, AllowedipsImage.CommonBits.entry⟩, history⟩ := by
  have initial : (⟨⟨prologueData s 0, AllowedipsImage.CommonBits.entry+0⟩, history⟩ : Executed) =
      ⟨⟨s, AllowedipsImage.CommonBits.entry⟩, history⟩ := by
    simp [prologueData, savedCount, saveMemory]
  rw [← initial]
  apply history_cons _ _ _ _ _ _ (instruction0 fetch agree s mapped)
  apply history_cons _ _ _ _ _ _ (instruction1 fetch agree s mapped)
  apply history_cons _ _ _ _ _ _ (instruction2 fetch agree s mapped)
  apply history_cons _ _ _ _ _ _ (instruction3 fetch agree s mapped)
  apply history_cons _ _ _ _ _ _ (instruction4 fetch agree s mapped)
  apply history_cons _ _ _ _ _ _ (instruction5 fetch agree s mapped)
  apply history_cons _ _ _ _ _ _ (instruction6 fetch agree s mapped)
  apply history_cons _ _ _ _ _ _ (instruction7 fetch agree s mapped)
  apply history_cons _ _ _ _ _ _ (instruction8 fetch agree s mapped)
  exact ⟨rfl, by simp [prologueStates, List.append_assoc]⟩

end Binary.CommonBits
