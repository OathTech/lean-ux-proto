import AllowedipsChildEntryFinish

namespace Binary.Pair.Allowedips.ChildFinish
open Leanux Leanux.WG Root CommonBitsCoverage AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

/-- A continuous child-attachment execution from the tested initialization
boundary. The only branch case is the mirror's empty child; initialization,
selection, both PC callbacks and publication are all proved below that boundary.
Caller-resource establishment and the remaining insertion cases are separate. -/
theorem initialization_child (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TrustBase.TracePcContract fetch)
    {names : Names} {world : World} {entry : MachineState}
    {key cidr pid base parentId : Nat} {d : Device} {parentNode : AipNode} {owner : Peer} (c : Context)
    (checked : NodeInit.boundary names nodeOffsets world entry key cidr pid=.ok base)
    (device : world.wg.dev=some d)
    (parentNamed : (parentId,entry.data.regs.rbx.toNat) ∈ names.trie.nodes)
    (hasParent : d.nodes.get? parentId=some parentNode) (hasPeer : d.peers.get? pid=some owner)
    (sameWidth : entry.data.regs.rbp.toNat=parentNode.bitlen) (measure : parentNode.cidr<cidr)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (empty : parentNode.bit[key/2^(parentNode.bitlen-1-parentNode.cidr)%2]?=some none)
    (extent : entry.data.regs.rsp.toNat+32≤2^64)
    (stackMapped : ∀ offset size, offset+size≤32 →
      (entry.data.dmem.loadInt (.ofNat 64 (entry.data.regs.rsp.toNat+offset)) size).isSome=true)
    (ready : CallsReady c entry.data)
    (initialContextApart : ∀ a, c.bytes a → ¬NodeInit.EntryWrites names entry.data base a)
    (contextApart : ∀ a, c.bytes a → ¬ChildSetup.Writes entry.data.regs.rsp a)
    (publishContextApart : ∀ a, c.bytes a →
      ¬PublishWrites entry.data.regs.rbx base (key/2^(parentNode.bitlen-1-parentNode.cidr)%2) a)
    (savedApart : ∀ a, ChildSetup.Writes entry.data.regs.rsp a → ¬CallWrites entry.data.regs.rsp c a)
    (projectionApart : ∀ span ∈ readSpans (names.allocated base) nodeOffsets,
      ∀ a, span.contains a → ¬SetupWrites entry.data.regs.rsp c a)
    (tableApart : ∀ a, InRange (.ofNat 64 names.table) 24 a → ¬SetupWrites entry.data.regs.rsp c a)
    (queryApart : ∀ a, InRange entry.data.regs.r13.toBitVec (parentNode.bitlen/8) a →
      ¬SetupWrites entry.data.regs.rsp c a)
    (destinationsApart : ∀ a, PublishWrites entry.data.regs.rbx base
      (key/2^(parentNode.bitlen-1-parentNode.cidr)%2) a → ¬CallWrites entry.data.regs.rsp c a)
    (indexApart : ∀ a, InRange (.ofNat 64 (entry.data.regs.rsp.toNat+16)) 8 a →
      ¬InRange (.ofNat 64 (base+48)) 8 a) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x549 ∧ t.data.regs.rbx=0 ∧ t.data.regs.rsp=entry.data.regs.rsp ∧ CallsReady c t.data ∧
      EqualOutside (fun a => NodeInit.EntryWrites names entry.data base a ∨
        SetupWrites entry.data.regs.rsp c a ∨
        PublishWrites entry.data.regs.rbx base (key/2^(parentNode.bitlen-1-parentNode.cidr)%2) a)
        entry.data.dmem t.data.dmem ∧
      Corresponds (names.allocated base) nodeOffsets t.data.dmem
        (childInstalled d parentId (key/2^(parentNode.bitlen-1-parentNode.cidr)%2)
          key cidr entry.data.regs.rbp.toNat pid parentNode owner) ∧
      heap (names.allocated base)
        (target (childInstalled d parentId (key/2^(parentNode.bitlen-1-parentNode.cidr)%2)
          key cidr entry.data.regs.rbp.toNat pid parentNode owner)) t.data.dmem=.ok ()) entry := by
  have fields := NodeInit.boundary_fields checked
  obtain ⟨actual,deviceAt,related,heapOk⟩ := assertAt_ok fields.asserted
  have equal : actual=d := Option.some.inj (deviceAt.symm.trans device)
  subst actual
  obtain ⟨memory,summary,execution⟩ := NodeInit.initialization_executes fetch decoder checked
  have pending := NodeInit.pending_of_effect fields related heapOk summary
  have frame := (NodeInit.core_of_effect fields summary).2
  apply eventually_trans (instructionStep fetch) _ _ _ execution
  rintro a ⟨pcA,memA,registers,mappedA⟩
  have registerFacts : a.data.regs.rsp=entry.data.regs.rsp ∧
      a.data.regs.rbx=entry.data.regs.rbx ∧ a.data.regs.r12=entry.data.regs.r12 ∧
      a.data.regs.r13=entry.data.regs.r13 ∧ a.data.regs.r15=entry.data.regs.r15 ∧
      a.data.regs.rbp=UInt64.ofNat (entry.data.regs.rbp.toNat/8) ∧
      a.data.regs.r8=UInt64.ofNat base ∧ a.data.regs.r14=UInt64.ofNat (base+32) := by
    simpa only [NodeInit.registers,Bool.and_eq_true,beq_iff_eq,and_assoc] using registers
  obtain ⟨stack,bx,_,queryReg,_,_,allocation,_⟩ := registerFacts
  have fresh := (allocated_facts fields.allocated).2.2.1
  change base+72<2^64 at fresh
  have allocationNat : a.data.regs.r8.toNat=base := by
    rw [allocation]
    exact UInt64.toNat_ofNat_of_lt' (by change base<2^64; omega)
  have frameA : EqualOutside (NodeInit.EntryWrites names entry.data base) entry.data.dmem a.data.dmem := memA ▸ frame
  have pendingA : NodeInit.Pending names entry.data d key cidr pid base a.data.dmem := memA ▸ pending
  have readyA := ready.frame stack frameA mappedA initialContextApart
  have queryA : AllowedipsChild.QueryWords a.data.dmem a.data.regs.r13.toBitVec parentNode.bitlen key := by
    rw [queryReg,←sameWidth]
    exact AllowedipsLoop.query_frame fields.family (Placement.queryLocals_fields fields.query)
      frameA fields.query_separated
  have mappedFresh := mappedA.of_word (fields.zero_word "node.parent" 48 8 (by decide))
  have run := initialized_finish fetch decoder tracePc c fields related heapOk pendingA
    (by rw [bx]; exact parentNamed) hasParent hasPeer sameWidth measure prefixEq empty queryA allocationNat
    (by rw [stack]; exact extent)
    (by intro offset size within; rw [stack]; exact mappedA _ _ (stackMapped offset size within))
    mappedFresh readyA (by rw [stack]; exact contextApart) (by rw [bx]; exact publishContextApart)
    (by rw [stack]; exact savedApart) (by rw [stack]; exact projectionApart)
    (by rw [stack]; exact tableApart) (by rw [stack,queryReg]; exact queryApart)
    (by rw [stack,bx]; exact destinationsApart) (by rw [stack]; exact indexApart)
  rw [Placement.at_pc a _ pcA]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨pc,zeroT,stackT,readyT,frameT,relatedT,heapT⟩
  rw [stack,bx] at frameT
  refine ⟨pc,zeroT,stackT.trans stack,readyT,?_,relatedT,heapT⟩
  intro address outside
  exact (frameA address (fun h => outside (.inl h))).trans
    (frameT address (fun h => outside (.inr h)))

#print axioms initialization_child
end Binary.Pair.Allowedips.ChildFinish
