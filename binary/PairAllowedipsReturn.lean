import PairAllowedipsRoot

namespace Binary.Pair.Allowedips.Return
open AllowedipsMutationImage

/-- Architectural reads use modular addresses, including a stack crossing zero. -/
def saved (s : MachineData) (offset : Nat) : Except String UInt64 :=
  UInt64.ofNat <$> readNat ⟨s,0⟩ ((s.regs.rsp.toBitVec+.ofNat 64 offset).toNat) 8

def addEffect (s : MachineData) : Except String (Reg64s × Int64) := do
  let bx ← saved s 48
  let bp ← saved s 56
  let r12 ← saved s 64
  let r13 ← saved s 72
  let r14 ← saved s 80
  let r15 ← saved s 88
  let ra ← saved s 96
  return ({s.regs with
    rax:=.ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
    rbx:=bx,rbp:=bp,r12,r13,r14,r15,rsp:=s.regs.rsp+104},.ofBitVec ra.toBitVec)

def wrapperEffect (v4 : Bool) (s : MachineData) : Except String (Reg64s × Int64) := do
  let locals := if v4 then 8 else 16
  let bx ← saved s locals
  let bp ← saved s (locals+8)
  let r12 ← saved s (locals+16)
  let r13 ← saved s (locals+24)
  let ra ← saved s (locals+32)
  return ({s.regs with rbx:=bx,rbp:=bp,r12,r13,rsp:=s.regs.rsp+.ofNat (locals+40)},
    .ofBitVec ra.toBitVec)

/-- Return value, stack and callee-saved registers; caller scratch may change
in the final coverage callback. -/
def observed (regs : Reg64s) : List UInt64 :=
  [regs.rax,regs.rsp,regs.rbx,regs.rbp,regs.r12,regs.r13,regs.r14,regs.r15]

/-- Evaluate the return summaries at the same physical cuts used by the proof.
The full register file and unchanged memory are checked at each endpoint. -/
def check (states : Array MachineState) (final : MachineState) : Except String Nat := do
  let mut pending : Option (Reg64s × Int64 × DataMem) := none
  let mut beforeCoverage : Option (Reg64s × Int64) := none
  let mut count := 0
  for s in states.push final do
    if let some (regs,pc,memory) := pending then
      require (s.pc==pc && s.data.regs==regs && s.data.dmem==memory) "return.effect"
      pending := none
      count := count+1
    if s.pc==Add.entry+0x549 then
      require beforeCoverage.isNone "return.repeated-coverage"
      beforeCoverage := some (← addEffect s.data)
    else if s.pc==Add.entry+0x54e then
      let (regs,pc) ← addEffect s.data
      let some (previous,returnPC) := beforeCoverage | throw "return.missing-coverage"
      require (observed previous==observed regs && returnPC==pc) "return.callback-frame"
      beforeCoverage := none
      pending := some (regs,pc,s.data.dmem)
    else if s.pc==Insert4.entry+0x42 || s.pc==Insert6.entry+0x4f then
      let (regs,pc) ← wrapperEffect (s.pc==Insert4.entry+0x42) s.data
      pending := some (regs,pc,s.data.dmem)
  require pending.isNone "return.missing-end"
  require beforeCoverage.isNone "return.missing-callback-return"
  return count

end Binary.Pair.Allowedips.Return
