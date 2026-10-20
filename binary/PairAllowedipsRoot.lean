import PairAllowedipsExact

namespace Binary.Pair.Allowedips.Root

def store (m : DataMem) (address size value : Nat) : Except String DataMem := do
  require ((m.loadInt (.ofNat 64 address) size).isSome) "root.store-unmapped"
  return m.storeInt (.ofNat 64 address) size value

def headerWord (width cidr : Nat) : Nat :=
  cidr+((cidr/8) ^^^ ((width/8-1)%8))*256+(7-cidr%8)*65536+width*16777216

/-- Executable memory effect of the successful empty-root allocation tail.
Reads follow the image's store order, including the two IPv4 copy reads and
the post-copy saved root slot. This does not supply an allocation outcome. -/
def effect (s : MachineData) : Except String DataMem := do
  let base := s.regs.rbx.toNat
  let peer := s.regs.r14.toNat
  let width := s.regs.rbp.toNat
  require (width==32 || width==128) "root.family"
  let link := base+56
  let mut m ← store s.dmem base 8 peer
  let cidr ← readNat ⟨{s with dmem:=m},0⟩ (s.regs.rsp.toNat+16) 4
  require (cidr≤width) "root.cidr"
  let last ← readNat ⟨{s with dmem:=m},0⟩ (peer+1104) 8
  m ← store m (peer+1104) 8 link
  m ← store m (base+56) 8 (peer+1096)
  m ← store m (base+64) 8 last
  m ← store m last 8 link
  m ← store m (base+24) 4 (headerWord width cidr)
  if width==32 then
    let first ← readNat ⟨{s with dmem:=m},0⟩ s.regs.r13.toNat 4
    m ← store m (base+32) 4 first
    let again ← readNat ⟨{s with dmem:=m},0⟩ s.regs.r13.toNat 4
    m ← store m (base+32) 4 again
  else
    let last ← readNat ⟨{s with dmem:=m},0⟩ (s.regs.r13.toNat+8) 8
    m ← store m (base+40) 8 last
    let first ← readNat ⟨{s with dmem:=m},0⟩ s.regs.r13.toNat 8
    m ← store m (base+32) 8 first
  let slot ← readNat ⟨{s with dmem:=m},0⟩ (s.regs.rsp.toNat+8) 8
  m ← store m (base+48) 8 (slot ||| 2)
  store m slot 8 base

def check (states : Array MachineState) : Except String Nat := do
  let mut pending : Option DataMem := none
  let mut count := 0
  for s in states do
    if s.pc==AllowedipsMutationImage.Add.entry+0x443 then
      require pending.isNone "root.repeated-start"
      pending := some (← effect s.data)
    else if s.pc==AllowedipsMutationImage.Add.entry+0x549 then
      if let some memory := pending then
        require (s.data.dmem==memory) "root.memory-effect"
        require (s.data.regs.rbx==0) "root.success-register"
        pending := none
        count := count+1
  require pending.isNone "root.missing-end"
  return count

end Binary.Pair.Allowedips.Root
