import AllowedipsChildEntryCall
import AllowedipsChildSelected
import AllowedipsSelectTotal

namespace Binary.Pair.Allowedips.ChildFinish
open Leanux Leanux.WG Root CommonBitsCoverage AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

/-- From initialized-node resources, execute both coverage calls, actual child
selection and publication. The empty-slot condition is the source branch case;
all binary phase success and intermediate correspondence are derived. -/
theorem initialized_finish (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TrustBase.TracePcContract fetch)
    {names : Names} {world : World} {entry : MachineState} {s : MachineData}
    {key cidr pid base parentId : Nat} {d : Device} {parentNode : AipNode} {owner : Peer} (c : Context)
    (fields : NodeInit.BoundaryFields names nodeOffsets world entry key cidr pid base)
    (related : Corresponds names nodeOffsets entry.data.dmem d)
    (heapOk : heap names (target d) entry.data.dmem=.ok ())
    (pending : NodeInit.Pending names entry.data d key cidr pid base s.dmem)
    (parentNamed : (parentId,s.regs.rbx.toNat) ∈ names.trie.nodes)
    (hasParent : d.nodes.get? parentId=some parentNode) (hasPeer : d.peers.get? pid=some owner)
    (sameWidth : entry.data.regs.rbp.toNat=parentNode.bitlen) (measure : parentNode.cidr<cidr)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (empty : parentNode.bit[key/2^(parentNode.bitlen-1-parentNode.cidr)%2]?=some none)
    (query : AllowedipsChild.QueryWords s.dmem s.regs.r13.toBitVec parentNode.bitlen key)
    (allocation : s.regs.r8.toNat=base)
    (extent : s.regs.rsp.toNat+32≤2^64)
    (stackMapped : ∀ offset size, offset+size≤32 →
      (s.dmem.loadInt (.ofNat 64 (s.regs.rsp.toNat+offset)) size).isSome=true)
    (parentMapped : (s.dmem.loadInt (.ofNat 64 (base+48)) 8).isSome=true)
    (ready : CallsReady c s)
    (contextApart : ∀ a, c.bytes a → ¬ChildSetup.Writes s.regs.rsp a)
    (publishContextApart : ∀ a, c.bytes a →
      ¬PublishWrites s.regs.rbx base (key/2^(parentNode.bitlen-1-parentNode.cidr)%2) a)
    (savedApart : ∀ a, ChildSetup.Writes s.regs.rsp a → ¬CallWrites s.regs.rsp c a)
    (projectionApart : ∀ span ∈ readSpans (names.allocated base) nodeOffsets,
      ∀ a, span.contains a → ¬SetupWrites s.regs.rsp c a)
    (tableApart : ∀ a, InRange (.ofNat 64 names.table) 24 a → ¬SetupWrites s.regs.rsp c a)
    (queryApart : ∀ a, InRange s.regs.r13.toBitVec (parentNode.bitlen/8) a → ¬SetupWrites s.regs.rsp c a)
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
      ⟨s,Add.entry+0x1ff⟩ := by
  have parentNonzero : s.regs.rbx≠0 := by
    have positive := ((Trie.reconstruct_fields related.trie).nodeRange _ _ parentNamed).1
    intro zero
    rw [zero] at positive
    exact Nat.lt_irrefl 0 positive
  apply eventually_trans (instructionStep fetch) _ _ _
    (entry_call fetch decoder tracePc c ready pending allocation parentNonzero extent
      (stackMapped 24 8 (by decide)) contextApart savedApart projectionApart tableApart)
  rintro a ⟨pcA,stack,bx,keyReg,readyA,frameA,pendingA,saved,mapped⟩
  have named : (parentId,a.data.regs.rbx.toNat) ∈ names.trie.nodes := by rw [bx]; exact parentNamed
  have decoded := pendingA.old_node related named hasParent
  have short : parentNode.cidr<parentNode.bitlen := by have := fields.cidrBound; omega
  have family : parentNode.bitlen=32 ∨ parentNode.bitlen=128 := (Trie.decodeNode_fields decoded).family
  have queryA : AllowedipsChild.QueryWords a.data.dmem a.data.regs.r13.toBitVec parentNode.bitlen key := by
    rw [keyReg]
    exact AllowedipsLoop.query_frame family query frameA queryApart
  have mappedLocal (offset size : Nat) (within : offset+size≤32) :
      (a.data.dmem.loadInt (.ofNat 64 (a.data.regs.rsp.toNat+offset)) size).isSome=true := by
    rw [stack]
    apply mapped _ _ (stackMapped offset size within)
    rintro address ⟨i,bound,location⟩
    apply savedApart address
    refine ⟨offset+i,by omega,?_⟩
    simpa only [BitVec.ofNat_add,ofNat_uint64,BitVec.add_assoc] using location
  have savedA : readNat ⟨a.data,0⟩ (a.data.regs.rsp.toNat+24) 8=.ok base := by
    rw [←stack] at saved
    exact readNat_of_word saved
  obtain ⟨selected,registers,checked,childMapped⟩ := Select.empty_total decoded queryA short empty savedA
    (by simpa only [Nat.add_zero,ofNat_uint64] using mappedLocal 0 8 (by decide))
  have run := selected_finish fetch decoder tracePc c fields related heapOk pendingA named hasParent hasPeer
    sameWidth measure prefixEq queryA savedA (by rw [stack]; omega) checked
    (by simpa only [Nat.add_zero] using mappedLocal 0 8 (by decide))
    (mappedLocal 8 1 (by decide)) (mappedLocal 16 8 (by decide))
    (mapped _ _ parentMapped (fun a inside => destinationsApart a (.inl inside))) childMapped readyA
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
  exact (frameA address (fun h => outside (.inl h))).trans (frameT address outside)

#print axioms initialized_finish
end Binary.Pair.Allowedips.ChildFinish
