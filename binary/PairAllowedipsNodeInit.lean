import PairAllowedipsRoot

namespace Binary.Pair.Allowedips.NodeInit

/-- The nonempty-trie allocation tail before it chooses a publication slot.
Unlike the empty-root tail, it reads the old owner tail before storing the
owner and saves three selector bytes on the stack. Reads retain that order. -/
def effect (s : MachineData) : Except String (DataMem × Nat) := do
  let base ← readNat ⟨s,0⟩ s.regs.rsp.toNat 8
  let width := s.regs.rbp.toNat
  let cidr ← readNat ⟨s,0⟩ (s.regs.rsp.toNat+16) 4
  let peer := s.regs.r14.toNat
  let last ← readNat ⟨s,0⟩ (peer+1104) 8
  require (width==32 || width==128) "node-init.family"
  require (cidr≤width && s.regs.r12.toNat==cidr && s.regs.r15.toNat==width) "node-init.locals"
  let link := base+56
  let mut m ← Root.store s.dmem base 8 peer
  m ← Root.store m (peer+1104) 8 link
  m ← Root.store m (base+64) 8 last
  m ← Root.store m (base+56) 8 (peer+1096)
  m ← Root.store m last 8 link
  let mask := (width/8-1)%8
  m ← Root.store m (s.regs.rsp.toNat+36) 1 mask
  m ← Root.store m (s.regs.rsp.toNat+43) 1 ((cidr/8) ^^^ mask)
  m ← Root.store m (s.regs.rsp.toNat+44) 1 (7-cidr%8)
  m ← Root.store m (base+24) 4 (Root.headerWord width cidr)
  m ← Root.copy {s with regs:={s.regs with rbx:=.ofNat base}} m
  return (m,base)

def registers (before after : Reg64s) (base : Nat) : Bool :=
  after.rsp==before.rsp && after.rbx==before.rbx && after.r12==before.r12 &&
  after.r13==before.r13 && after.r15==before.r15 &&
  after.rbp==UInt64.ofNat (before.rbp.toNat/8) &&
  after.r8==UInt64.ofNat base && after.r14==UInt64.ofNat (base+32)

def check (states : Array MachineState) : Except String Nat := do
  let mut pending : Option (MachineData × DataMem × Nat) := none
  let mut count := 0
  for s in states do
    if s.pc==AllowedipsMutationImage.Add.entry+0x156 then
      require pending.isNone "node-init.repeated-start"
      let (memory,base) ← effect s.data
      pending := some (s.data,memory,base)
    else if s.pc==AllowedipsMutationImage.Add.entry+0x1ff then
      let some (before,memory,base) := pending | throw "node-init.missing-start"
      require (s.data.dmem==memory && registers before.regs s.data.regs base) "node-init.effect"
      pending := none
      count := count+1
  require pending.isNone "node-init.missing-end"
  return count

end Binary.Pair.Allowedips.NodeInit
