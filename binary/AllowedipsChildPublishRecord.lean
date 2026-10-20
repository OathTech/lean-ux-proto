import AllowedipsChildPublishFrame
import AllowedipsConnectRecord
import AllowedipsChildParent

namespace Binary.Pair.Allowedips.ChildPublish
open AllowedipsMutationImage Root Leanux.WG
local instance : Labels := Image.linkedLabels

private theorem read_agrees {s a size actual expected path}
    (read : readNat s a size=.ok actual) (decoded : word s.data.dmem path a size=.ok expected) :
    actual=expected :=
  Int.ofNat.inj (Option.some.inj ((Trie.readNat_loadInt read).symm.trans (word_loadInt _ _ _ _ _ decoded)))

/-- Resolve the tested byte effect to the C's linkage operation from saved
input words. The index is protected from the first store by a frame premise,
not asserted to have the desired value at an intermediate state. -/
theorem effect_connect {s : MachineData} {memory registers base direction}
    (bit : direction<2) (parentExtent : s.regs.rbx.toNat+24≤2^64)
    (baseRead : readNat ⟨s,0⟩ s.regs.rsp.toNat 8=.ok base)
    (directionRead : readNat ⟨s,0⟩ (s.regs.rsp.toNat+8) 1=.ok direction)
    (indexRead : word s.dmem "saved.index" (s.regs.rsp.toNat+16) 8=.ok direction)
    (indexApart : ∀ a, InRange (.ofNat 64 (s.regs.rsp.toNat+16)) 8 a →
      ¬InRange (.ofNat 64 (base+48)) 8 a)
    (checked : effect s=.ok (memory,registers)) :
    memory=connectMemory s.dmem base (s.regs.rbx.toNat+(direction+1)*8)
      ((s.regs.rbx.toNat+(direction+1)*8) ||| direction) := by
  unfold effect at checked
  obtain ⟨rawDirection,directionLoad,checked⟩ := bind_ok checked
  have directionEq : rawDirection=direction := Except.ok.inj (directionLoad.symm.trans directionRead)
  subst rawDirection
  obtain ⟨rawBase,baseLoad,checked⟩ := bind_ok checked
  have baseEq : rawBase=base := Except.ok.inj (baseLoad.symm.trans baseRead)
  subst rawBase
  obtain ⟨middle,parentStore,checked⟩ := bind_ok checked
  obtain ⟨index,indexLoad,checked⟩ := bind_ok checked
  obtain ⟨last,linkStore,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have middleFrame : EqualOutside (InRange (.ofNat 64 (base+48)) 8) s.dmem middle := by
    rw [(store_facts parentStore).2]
    exact storeInt_frame _ _ _ _
  have savedAfter : word middle "saved.index" (s.regs.rsp.toNat+16) 8=.ok direction :=
    (Trie.word_frame middleFrame _ _ _ indexApart).symm.trans indexRead
  have indexEq : index=direction := read_agrees indexLoad savedAfter
  subst index
  have slotSmall : s.regs.rbx.toNat+(direction+1)*8<2^64 := by omega
  have packedSmall : (s.regs.rbx.toNat+(direction+1)*8) ||| direction<2^64 :=
    Nat.or_lt_two_pow slotSmall (by omega)
  have packedNat : ((s.regs.rbx.toBitVec+.ofNat 64 (((direction+1)%256)*8)) |||
      .ofNat 64 direction).toNat=(s.regs.rbx.toNat+(direction+1)*8) ||| direction := by
    rw [Nat.mod_eq_of_lt (by omega : direction+1<256),←ofNat_uint64,
      ←BitVec.ofNat_add,←BitVec.ofNat_or,BitVec.toNat_ofNat,Nat.mod_eq_of_lt packedSmall]
  have parentEq := (store_facts parentStore).2
  rw [packedNat,store_nat64] at parentEq
  have afterEq := (store_facts linkStore).2
  rw [store_nat64] at afterEq
  rw [afterEq,parentEq]
  have slotEq : s.regs.rbx.toNat+direction*8+8=s.regs.rbx.toNat+(direction+1)*8 := by omega
  rw [slotEq]
  rfl

/-- The linked fresh record decodes to the mirror's child-parent shape.
The old parent's changed child word is exported for whole-trie composition. -/
theorem record_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {names : Names} {s : MachineData} {memory registers base direction id parentId}
    {node : Trie.Node}
    (bit : direction<2) (parentExtent : s.regs.rbx.toNat+24≤2^64)
    (aligned : s.regs.rbx.toNat%8=0) (extent : base+56≤2^64)
    (parentNamed : Trie.pointer names.trie.nodes "node.parent" s.regs.rbx.toNat=.ok (some parentId))
    (baseRead : readNat ⟨s,0⟩ s.regs.rsp.toNat 8=.ok base)
    (directionRead : readNat ⟨s,0⟩ (s.regs.rsp.toNat+8) 1=.ok direction)
    (indexRead : word s.dmem "saved.index" (s.regs.rsp.toNat+16) 8=.ok direction)
    (indexApart : ∀ a, InRange (.ofNat 64 (s.regs.rsp.toNat+16)) 8 a →
      ¬InRange (.ofNat 64 (base+48)) 8 a)
    (core : Trie.decodeNode names.trie nodeOffsets s.dmem base=.ok node)
    (apart : ∀ a, InRange (.ofNat 64 base) 56 a →
      ¬InRange (.ofNat 64 (s.regs.rbx.toNat+(direction+1)*8)) 8 a)
    (checked : effect s=.ok (memory,registers)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.dmem=memory ∧ t.data.regs=registers ∧
      EqualOutside (Writes s.regs t.data.regs) s.dmem t.data.dmem ∧
      decodeNode names nodeOffsets t.data.dmem id base=.ok (id,({
        peer:=node.peer,bit:=node.children,cidr:=node.cidr,bitlen:=node.width,bits:=node.key,
        parent:=.child parentId direction} : AipNode)) ∧
      word t.data.dmem "node.link" (s.regs.rbx.toNat+(direction+1)*8) 8=.ok base)
      ⟨s,Add.entry+0x6f2⟩ := by
  have memoryEq := effect_connect bit parentExtent baseRead directionRead indexRead indexApart checked
  have reconstructed := connect_record (id:=id) extent (by omega)
    (Nat.or_lt_two_pow (by omega : s.regs.rbx.toNat+(direction+1)*8<2^64) (by omega : direction<2^64))
    core (parent_child aligned bit parentNamed) apart
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (publication_checked fetch decoder checked)
  rintro t ⟨position,mem,regs,frame⟩
  refine ⟨position,mem,regs,frame,?_⟩
  simpa only [mem,memoryEq] using reconstructed

#print axioms record_checked
end Binary.Pair.Allowedips.ChildPublish
