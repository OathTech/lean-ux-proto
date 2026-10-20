import PairAllowedipsRoot

namespace Binary.Pair.Allowedips.ChildPublish

/-- Publication after the no-child branch's coverage callback. Keep the
index read after the packed-parent store, as in the image. -/
def effect (s : MachineData) : Except String (DataMem × Reg64s) := do
  let direction ← readNat ⟨s,0⟩ (s.regs.rsp.toNat+8) 1
  let base ← readNat ⟨s,0⟩ s.regs.rsp.toNat 8
  let slot : BitVec 64 := s.regs.rbx.toBitVec + .ofNat 64 (((direction+1)%256)*8)
  let packed := slot ||| .ofNat 64 direction
  let parent ← Root.store s.dmem (base+48) 8 packed.toNat
  let index ← readNat ⟨{s with dmem:=parent},0⟩ (s.regs.rsp.toNat+16) 8
  let memory ← Root.store parent (s.regs.rbx.toNat+index*8+8) 8 base
  return (memory,{s.regs with
    rax:=.ofNat index,rbx:=0,rcx:=.ofBitVec slot,
    rdx:=.ofBitVec packed,r8:=.ofNat base})

def check (states : Array MachineState) : Except String Nat := do
  let mut pending : Option (DataMem × Reg64s) := none
  let mut count := 0
  for s in states do
    if s.pc==AllowedipsMutationImage.Add.entry+0x6f2 then
      require pending.isNone "child-publish.repeated-start"
      pending := some (← effect s.data)
    else if s.pc==AllowedipsMutationImage.Add.entry+0x549 then
      if let some (memory,regs) := pending then
        require (s.data.dmem==memory && s.data.regs==regs) "child-publish.effect"
        pending := none
        count := count+1
  require pending.isNone "child-publish.missing-end"
  return count

end Binary.Pair.Allowedips.ChildPublish
