import PairAllowedipsState
import PairRequire
import AllowedipsMutationImage

namespace Binary.Pair.Allowedips.Exact

def ownerMemory (s : MachineData) : DataMem :=
  s.dmem.storeInt s.regs.rbx.toBitVec 8 s.regs.r14.toBitVec.toInt

def nextMemory (s : MachineData) (previous next : BitVec 64) : DataMem :=
  (ownerMemory s).storeInt (next+8) 8 previous.toInt

def removedMemory (s : MachineData) (previous next : BitVec 64) : DataMem :=
  (nextMemory s previous next).storeInt previous 8 next.toInt

def headMemory (s : MachineData) : DataMem :=
  s.dmem.storeInt (s.regs.r14.toBitVec+8) 8 s.regs.rdx.toBitVec.toInt

def forwardMemory (s : MachineData) : DataMem :=
  (headMemory s).storeInt (s.regs.rbx.toBitVec+56) 8 s.regs.r14.toBitVec.toInt

def backwardMemory (s : MachineData) : DataMem :=
  (forwardMemory s).storeInt (s.regs.rbx.toBitVec+64) 8 s.regs.rax.toBitVec.toInt

def addedMemory (s : MachineData) : DataMem :=
  (backwardMemory s).storeInt s.regs.rax.toBitVec 8 s.regs.rdx.toBitVec.toInt

def mapped (m : DataMem) (a : BitVec 64) : Except String Unit :=
  require ((m.loadInt a 8).isSome) "exact.store-unmapped"

/-- Executable summary of the callback-free exact reassignment segment. It
reads the destination tail after unlinking, so same-list moves retain aliases. -/
def removeEffect (s : MachineData) : Except String (DataMem × Reg64s) := do
  let before : MachineState := ⟨s,0⟩
  let previous := BitVec.ofNat 64 (← readNat before (s.regs.rbx.toNat+64) 8)
  let next := BitVec.ofNat 64 (← readNat before (s.regs.rbx.toNat+56) 8)
  mapped s.dmem s.regs.rbx.toBitVec
  mapped (ownerMemory s) (next+8)
  mapped (nextMemory s previous next) previous
  let removed := removedMemory s previous next
  let last := BitVec.ofNat 64 (← readNat ⟨{s with dmem := removed},0⟩ (s.regs.r14.toNat+1104) 8)
  return (removed,{s.regs with
    rax := .ofBitVec last,rcx := .ofBitVec next,rdx := .ofBitVec (s.regs.rbx.toBitVec+56),
    r14 := .ofBitVec (s.regs.r14.toBitVec+1096)})

def appendEffect (s : MachineData) : Except String (DataMem × Reg64s) := do
  mapped s.dmem (s.regs.r14.toBitVec+8)
  mapped (headMemory s) (s.regs.rbx.toBitVec+56)
  mapped (forwardMemory s) (s.regs.rbx.toBitVec+64)
  mapped (backwardMemory s) s.regs.rax.toBitVec
  return (addedMemory s,{s.regs with rbx := 0})

def effect (s : MachineData) : Except String (DataMem × Reg64s) := do
  let (memory,regs) ← removeEffect s
  appendEffect {s with dmem := memory,regs}

def check (states : Array MachineState) : Except String Nat := do
  let mut pending : Option (DataMem × Reg64s) := none
  let mut count := 0
  for s in states do
    if s.pc==AllowedipsMutationImage.Add.entry+0x3e5 then
      require pending.isNone "exact.repeated-start"
      pending := some (← effect s.data)
    else if s.pc==AllowedipsMutationImage.Add.entry+0x549 then
      if let some (memory,regs) := pending then
        require (s.data.dmem==memory) "exact.memory-effect"
        require (s.data.regs==regs) "exact.register-effect"
        pending := none
        count := count+1
  require pending.isNone "exact.missing-end"
  return count

end Binary.Pair.Allowedips.Exact
