import PairAllowedipsRoot

namespace Binary.Pair.Allowedips.ChildSetup

def entryEffect (s : MachineData) : Except String (DataMem × Nat) := do
  let memory ← Root.store s.dmem (s.regs.rsp.toNat+24) 8 s.regs.r8.toNat
  return (memory,if s.regs.rbx==0 then 0x601 else 0x20d)

def saveEffect (s : MachineData) : Except String DataMem := do
  let memory ← Root.store s.dmem (s.regs.rsp.toNat+16) 8 s.regs.rax.toNat
  let memory ← Root.store memory (s.regs.rsp.toNat+8) 1 (s.regs.rdx.toNat%256)
  Root.store memory s.regs.rsp.toNat 8 s.regs.r8.toNat

def check (states : Array MachineState) : Except String (Nat × Nat) := do
  let mut entry : Option (DataMem × Reg64s × Nat) := none
  let mut save : Option (DataMem × Reg64s) := none
  let mut entries := 0
  let mut saves := 0
  for s in states do
    if s.pc==AllowedipsMutationImage.Add.entry+0x1ff then
      require entry.isNone "child-setup.repeated-entry"
      let (memory,offset) ← entryEffect s.data
      entry := some (memory,s.data.regs,offset)
    else if s.pc==AllowedipsMutationImage.Add.entry+0x20d || s.pc==AllowedipsMutationImage.Add.entry+0x601 then
      let some (memory,regs,offset) := entry | throw "child-setup.missing-entry"
      require (s.pc==AllowedipsMutationImage.Add.entry+Int64.ofNat offset &&
        s.data.dmem==memory && s.data.regs==regs) "child-setup.entry-effect"
      entry := none
      entries := entries+1
    else if s.pc==AllowedipsMutationImage.Add.entry+0x6e0 then
      require save.isNone "child-setup.repeated-save"
      save := some (← saveEffect s.data,s.data.regs)
    else if s.pc==AllowedipsMutationImage.Add.entry+0x6ed then
      let some (memory,regs) := save | throw "child-setup.missing-save"
      require (s.data.dmem==memory && s.data.regs==regs) "child-setup.save-effect"
      save := none
      saves := saves+1
  require (entry.isNone && save.isNone) "child-setup.missing-end"
  return (entries,saves)

end Binary.Pair.Allowedips.ChildSetup
