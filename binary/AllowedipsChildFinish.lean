import AllowedipsChildSaveCall
import AllowedipsChildPublishHeap
import AllowedipsChildPublishTotal

namespace Binary.Pair.Allowedips.ChildFinish
open Leanux Leanux.WG Root CommonBitsCoverage AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

def PublishWrites (parent : UInt64) (base direction : Nat) (a : BitVec 64) : Prop :=
  InRange (.ofNat 64 (base+48)) 8 a ∨
    InRange (.ofNat 64 (parent.toNat+direction*8+8)) 8 a

theorem publish_writes {before after : Reg64s} {base direction : Nat}
    (baseEq : after.r8.toNat=base) (indexEq : after.rax.toNat=direction) :
    ChildPublish.Writes before after=PublishWrites before.rbx base direction := by
  have baseWord : after.r8.toBitVec=.ofNat 64 base := by rw [←ofNat_uint64,baseEq]
  have indexWord : after.rax.toBitVec=.ofNat 64 direction := by rw [←ofNat_uint64,indexEq]
  funext a
  simp only [ChildPublish.Writes,PublishWrites,baseWord,indexWord,
    BitVec.ofNat_add,BitVec.ofNat_mul,ofNat_uint64]
  rfl

/-- The empty-child branch from its first save through the real coverage call
and publication. Saved inputs, pending-node frames and publication termination
are derived; the old relation and heap are restored at the common success cut.
Entry establishment and the preceding selector remain separate obligations. -/
theorem finish (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TrustBase.TracePcContract fetch)
    {names : Names} {world : World} {entry : MachineState} {s : MachineData}
    {key cidr pid base parentId direction : Nat} {memory : DataMem}
    {d : Device} {parentNode : AipNode} {owner : Peer} (c : Context)
    (fields : NodeInit.BoundaryFields names nodeOffsets world entry key cidr pid base)
    (related : Corresponds names nodeOffsets entry.data.dmem d)
    (heapOk : heap names (target d) entry.data.dmem=.ok ())
    (pending : NodeInit.Pending names entry.data d key cidr pid base s.dmem)
    (parentNamed : (parentId,s.regs.rbx.toNat) ∈ names.trie.nodes)
    (hasParent : d.nodes.get? parentId=some parentNode) (hasPeer : d.peers.get? pid=some owner)
    (bit : direction<2) (empty : parentNode.bit[direction]?=some none)
    (sameWidth : entry.data.regs.rbp.toNat=parentNode.bitlen) (measure : parentNode.cidr<cidr)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (side : key/2^(parentNode.bitlen-1-parentNode.cidr)%2=direction)
    (allocation : s.regs.r8.toNat=base)
    (extent : s.regs.rsp.toNat+24≤2^64)
    (index : s.regs.rax.toNat=direction) (byte : s.regs.rdx.toNat=direction)
    (checked : ChildSetup.saveEffect s=.ok memory)
    (parentMapped : (s.dmem.loadInt (.ofNat 64 (base+48)) 8).isSome=true)
    (childMapped : (s.dmem.loadInt (.ofNat 64 (s.regs.rbx.toNat+direction*8+8)) 8).isSome=true)
    (ready : CallsReady c s)
    (contextApart : ∀ a, c.bytes a → ¬ChildSetup.Writes s.regs.rsp a)
    (publishContextApart : ∀ a, c.bytes a → ¬PublishWrites s.regs.rbx base direction a)
    (savedApart : ∀ a, ChildSetup.Writes s.regs.rsp a → ¬CallWrites s.regs.rsp c a)
    (projectionApart : ∀ span ∈ readSpans (names.allocated base) nodeOffsets,
      ∀ a, span.contains a → ¬SetupWrites s.regs.rsp c a)
    (tableApart : ∀ a, InRange (.ofNat 64 names.table) 24 a → ¬SetupWrites s.regs.rsp c a)
    (destinationsApart : ∀ a, PublishWrites s.regs.rbx base direction a → ¬CallWrites s.regs.rsp c a)
    (indexApart : ∀ a, InRange (.ofNat 64 (s.regs.rsp.toNat+16)) 8 a →
      ¬InRange (.ofNat 64 (base+48)) 8 a) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.regs.rsp=s.regs.rsp ∧ CallsReady c t.data ∧
      EqualOutside (fun a => SetupWrites s.regs.rsp c a ∨ PublishWrites s.regs.rbx base direction a)
        s.dmem t.data.dmem ∧
      Corresponds (names.allocated base) nodeOffsets t.data.dmem
        (childInstalled d parentId direction key cidr entry.data.regs.rbp.toNat pid parentNode owner) ∧
      heap (names.allocated base)
        (target (childInstalled d parentId direction key cidr entry.data.regs.rbp.toNat pid parentNode owner))
        t.data.dmem=.ok ()) ⟨s,Add.entry+0x6e0⟩ := by
  apply eventually_trans (instructionStep fetch) _ _ _
    (save_call fetch decoder tracePc c ready pending allocation extent bit index byte checked
      contextApart savedApart projectionApart tableApart)
  rintro a ⟨pcA,stack,bx,readyA,frameA,pendingA,baseRead,directionRead,indexRead,mapped⟩
  have parentMappedA := mapped _ _ parentMapped (fun a h => destinationsApart a (.inl h))
  have childMappedA := mapped _ _ childMapped (fun a h => destinationsApart a (.inr h))
  rw [←stack] at baseRead directionRead indexRead indexApart
  rw [←bx] at childMappedA parentNamed
  obtain ⟨published,registers,exec,stackB,baseB,indexB⟩ :=
    ChildPublish.effect_total baseRead directionRead indexRead parentMappedA childMappedA indexApart
  have bytes := publish_writes (before:=a.data.regs) baseB indexB
  rw [bx] at bytes
  have run := ChildPublish.publication_restores fetch decoder fields related heapOk pendingA
    parentNamed hasParent hasPeer bit empty sameWidth measure prefixEq side
    (readNat_of_word baseRead) (readNat_of_word directionRead) indexRead indexApart exec
  rw [Placement.at_pc a _ pcA]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨pc,mem,regs,frame,relatedT,heapT⟩
  have stackT : t.data.regs.rsp=a.data.regs.rsp := by rw [regs]; exact stackB
  have mappedT : MappedLe a.data.dmem t.data.dmem := mem ▸ ChildPublish.effect_mapped exec
  rw [regs,bytes] at frame
  have readyT := readyA.frame stackT frame mappedT publishContextApart
  refine ⟨pc,stackT.trans stack,readyT,?_,relatedT,heapT⟩
  intro address outside
  exact (frameA address (fun h => outside (.inl h))).trans
    (frame address (fun h => outside (.inr h)))

#print axioms finish
end Binary.Pair.Allowedips.ChildFinish
