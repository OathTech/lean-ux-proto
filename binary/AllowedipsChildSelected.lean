import AllowedipsChildFinish
import AllowedipsSelectLocals
import AllowedipsChildSaveTotal

namespace Binary.Pair.Allowedips.ChildFinish
open Leanux Leanux.WG Root CommonBitsCoverage AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

/-- The actual selector chooses the empty mirror slot. Its register/stack
outputs establish the saving and publication path, which restores the full
projection without assuming a second correspondence point succeeds. -/
theorem selected_finish (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TrustBase.TracePcContract fetch)
    {names : Names} {world : World} {entry : MachineState} {s : MachineData}
    {key cidr pid base parentId : Nat} {memory : DataMem} {registers : Reg64s}
    {d : Device} {parentNode : AipNode} {owner : Peer} (c : Context)
    (fields : NodeInit.BoundaryFields names nodeOffsets world entry key cidr pid base)
    (related : Corresponds names nodeOffsets entry.data.dmem d)
    (heapOk : heap names (target d) entry.data.dmem=.ok ())
    (pending : NodeInit.Pending names entry.data d key cidr pid base s.dmem)
    (parentNamed : (parentId,s.regs.rbx.toNat) ∈ names.trie.nodes)
    (hasParent : d.nodes.get? parentId=some parentNode) (hasPeer : d.peers.get? pid=some owner)
    (sameWidth : entry.data.regs.rbp.toNat=parentNode.bitlen) (measure : parentNode.cidr<cidr)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (query : AllowedipsChild.QueryWords s.dmem s.regs.r13.toBitVec parentNode.bitlen key)
    (saved : readNat ⟨s,0⟩ (s.regs.rsp.toNat+24) 8=.ok base)
    (extent : s.regs.rsp.toNat+24≤2^64)
    (checked : Select.effect s=.ok (memory,registers,0x6e0))
    (baseMapped : (s.dmem.loadInt (.ofNat 64 s.regs.rsp.toNat) 8).isSome=true)
    (directionMapped : (s.dmem.loadInt (.ofNat 64 (s.regs.rsp.toNat+8)) 1).isSome=true)
    (indexMapped : (s.dmem.loadInt (.ofNat 64 (s.regs.rsp.toNat+16)) 8).isSome=true)
    (parentMapped : (s.dmem.loadInt (.ofNat 64 (base+48)) 8).isSome=true)
    (childMapped : (s.dmem.loadInt (.ofNat 64
      (s.regs.rbx.toNat+(key/2^(parentNode.bitlen-1-parentNode.cidr)%2)*8+8)) 8).isSome=true)
    (ready : CallsReady c s)
    (contextApart : ∀ a, c.bytes a → ¬ChildSetup.Writes s.regs.rsp a)
    (publishContextApart : ∀ a, c.bytes a →
      ¬PublishWrites s.regs.rbx base (key/2^(parentNode.bitlen-1-parentNode.cidr)%2) a)
    (savedApart : ∀ a, ChildSetup.Writes s.regs.rsp a → ¬CallWrites s.regs.rsp c a)
    (projectionApart : ∀ span ∈ readSpans (names.allocated base) nodeOffsets,
      ∀ a, span.contains a → ¬SetupWrites s.regs.rsp c a)
    (tableApart : ∀ a, InRange (.ofNat 64 names.table) 24 a → ¬SetupWrites s.regs.rsp c a)
    (destinationsApart : ∀ a, PublishWrites s.regs.rbx base
      (key/2^(parentNode.bitlen-1-parentNode.cidr)%2) a → ¬CallWrites s.regs.rsp c a)
    (indexApart : ∀ a, InRange (.ofNat 64 (s.regs.rsp.toNat+16)) 8 a →
      ¬InRange (.ofNat 64 (base+48)) 8 a) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.regs.rbx=0 ∧ t.data.regs.rsp=s.regs.rsp ∧ CallsReady c t.data ∧
      EqualOutside (fun a => SetupWrites s.regs.rsp c a ∨
        PublishWrites s.regs.rbx base (key/2^(parentNode.bitlen-1-parentNode.cidr)%2) a)
        s.dmem t.data.dmem ∧
      Corresponds (names.allocated base) nodeOffsets t.data.dmem
        (childInstalled d parentId (key/2^(parentNode.bitlen-1-parentNode.cidr)%2)
          key cidr entry.data.regs.rbp.toNat pid parentNode owner) ∧
      heap (names.allocated base)
        (target (childInstalled d parentId (key/2^(parentNode.bitlen-1-parentNode.cidr)%2)
          key cidr entry.data.regs.rbp.toNat pid parentNode owner)) t.data.dmem=.ok ())
      ⟨s,Add.entry+0x212⟩ := by
  have decoded := pending.old_node related parentNamed hasParent
  have short : parentNode.cidr<parentNode.bitlen := by have := fields.cidrBound; omega
  have locals := Select.effect_locals saved checked
  apply eventually_trans (instructionStep fetch) _ _ _
    (Select.selection_checked fetch decoder decoded query short checked)
  rintro a ⟨pcA,memA,regsA,frameA,mappedA,index,byte,empty⟩
  have stack : a.data.regs.rsp=s.regs.rsp := by rw [regsA]; exact locals.1
  have bx : a.data.regs.rbx=s.regs.rbx := by rw [regsA]; exact locals.2.1
  have allocation : a.data.regs.r8.toNat=base := by rw [regsA]; exact locals.2.2
  have frame : EqualOutside (ChildSetup.Writes s.regs.rsp) s.dmem a.data.dmem := by
    intro address outside
    exact frameA address (fun ⟨i,bound,atByte⟩ => outside ⟨i,by omega,atByte⟩)
  have pendingA := pending.frame frame
    (fun span member a inside h => projectionApart span member a inside (.inl h))
    (fun a inside h => tableApart a inside (.inl h))
  have readyA := ready.frame stack frame mappedA contextApart
  have baseMappedA := mappedA _ _ baseMapped
  have directionMappedA := mappedA _ _ directionMapped
  have indexMappedA := mappedA _ _ indexMapped
  rw [←stack] at baseMappedA directionMappedA indexMappedA
  obtain ⟨savedMemory,savedEffect⟩ := ChildSetup.save_total baseMappedA directionMappedA indexMappedA
  have run := finish fetch decoder tracePc c fields related heapOk pendingA
    (by rw [bx]; exact parentNamed) hasParent hasPeer (Nat.mod_lt _ (by decide)) (empty rfl)
    sameWidth measure prefixEq rfl allocation (by rw [stack]; exact extent) index byte savedEffect
    (mappedA _ _ parentMapped) (by rw [bx]; exact mappedA _ _ childMapped) readyA
    (by rw [stack]; exact contextApart) (by rw [bx]; exact publishContextApart)
    (by rw [stack]; exact savedApart) (by rw [stack]; exact projectionApart)
    (by rw [stack]; exact tableApart) (by rw [stack,bx]; exact destinationsApart)
    (by rw [stack]; exact indexApart)
  rw [Placement.at_pc a _ pcA]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨pc,zeroT,stackT,readyT,frameT,relatedT,heapT⟩
  rw [stack,bx] at frameT
  refine ⟨pc,zeroT,stackT.trans stack,readyT,?_,relatedT,heapT⟩
  intro address outside
  exact (frame address (fun h => outside (.inl (.inl h)))).trans (frameT address outside)

#print axioms selected_finish
end Binary.Pair.Allowedips.ChildFinish
