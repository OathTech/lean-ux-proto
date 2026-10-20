import PairAllowedipsRoot

namespace Binary.Pair.Allowedips.Select

/-- The actual post-initialization selector. Reads occur in image order; the
selected child is saved before the empty/nonempty branch. The effect uses
bytes in the machine state, not a mirror-supplied direction. -/
def effect (s : MachineData) : Except String (DataMem × Reg64s × Nat) := do
  let byteIndex ← readNat ⟨s,0⟩ (s.regs.rbx.toNat+25) 1
  let shift ← readNat ⟨s,0⟩ (s.regs.rbx.toNat+26) 1
  let base ← readNat ⟨s,0⟩ (s.regs.rsp.toNat+24) 8
  let byte ← readNat ⟨s,0⟩ (s.regs.r13.toNat+byteIndex) 1
  require (byteIndex<16 && shift<8) "select.selectors"
  let direction := byte/2^shift%2
  let child ← readNat ⟨s,0⟩ (s.regs.rbx.toNat+8+direction*8) 8
  let memory ← Root.store s.dmem s.regs.rsp.toNat 8 child
  return (memory,{s.regs with
    rax:=.ofNat direction,rdx:=.ofNat direction,
    rcx:=.ofNat child,r8:=.ofNat base},if child=0 then 0x6e0 else 0x241)

def check (states : Array MachineState) : Except String Nat := do
  let mut pending : Option (DataMem × Reg64s × Nat) := none
  let mut count := 0
  for s in states do
    if s.pc==AllowedipsMutationImage.Add.entry+0x212 then
      require pending.isNone "select.repeated-start"
      pending := some (← effect s.data)
    else if s.pc==AllowedipsMutationImage.Add.entry+0x6e0 || s.pc==AllowedipsMutationImage.Add.entry+0x241 then
      match pending with
      | some (memory,regs,offset) =>
        require (s.pc==AllowedipsMutationImage.Add.entry+Int64.ofNat offset &&
          s.data.dmem==memory && s.data.regs==regs) "select.effect"
        pending := none
        count := count+1
      | none =>
        -- The no-parent path enters 0x241 directly from 0x606. The caller
        -- separately compares this check's count with the mirror's selectors.
        require (s.pc==AllowedipsMutationImage.Add.entry+0x241) "select.missing-start"
  require pending.isNone "select.missing-end"
  return count

end Binary.Pair.Allowedips.Select
