import C1BelowSplitBits

/-! Result C1, work package 3, the split path, parent and root sub-cases:
from `Add.entry+0x338` to the common exit with the relation and `heap` for
`C1Step.step`'s own device. T5's capstones with every ordering, side and
device hypothesis discharged from what `StepFacts` carries (`model`'s case,
`walked`); what remains is the machine state at `+0x338` (T5's hypotheses,
unchanged), the pending leaf and the initialized internal node, and
`downFacts`: that the internal node's prefix length and the bit selected for
the node below, both computed before `+0x338`, are the mirror's. -/
namespace Binary.Pair.Allowedips.C1Split
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.SplitStage3 Binary.SplitStage3.Path
open Binary.CommonBitsCoverage Leanux Leanux.WG Root Binary.Statements.C1.Proof
local instance : Labels := Image.linkedLabels

theorem split_parent_from_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (b1 byteIndex shift byte parentIndex parentShift parentByte : Nat)
    {names : Names} {machine : MachineState} {memory : DataMem} {d : Device}
    {key cidr common pid base base2 downId downBase parentId parentBase : Nat}
    {d0 : Device} {family : Nat} {exact : Bool} {outcomes : List Bool}
    (owner : Peer)
    -- machine side, as `Path.connections_nonnull`
    (entry : SplitStage3.Entry s b1 byteIndex shift byte)
    (parent : s.regs.rbx ≠ 0)
    (ready : CallsReady c s)
    (contextApart : ∀ a, c.bytes a →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec b1 (selected byte shift) a)
    (contextApart3 : ∀ a, c.bytes a → ¬(InRange (s.regs.r12.toBitVec + 48) 8 a ∨
      InRange (slot s.regs.rbx.toBitVec (selected parentByte parentShift)) 8 a))
    (indexRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 25) 1 = some (parentIndex : Int))
    (shiftRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 26) 1 = some (parentShift : Int))
    (byteRead : s.dmem.loadInt (s.regs.r12.toBitVec + 32 + .ofNat 64 parentIndex) 1 = some (parentByte : Int))
    (indexBound : parentIndex < 16) (shiftBound : parentShift < 8) (byteBound : parentByte < 256)
    (nodeParentMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 48) 8).isSome = true)
    (parentLeft : (s.dmem.loadInt (s.regs.rbx.toBitVec + 8) 8).isSome = true)
    (parentRight : (s.dmem.loadInt (s.regs.rbx.toBitVec + 16) 8).isSome = true)
    (readsApart : ∀ a, (InRange (s.regs.rbx.toBitVec + 25) 1 a ∨ InRange (s.regs.rbx.toBitVec + 26) 1 a ∨
        InRange (s.regs.r12.toBitVec + 32 + .ofNat 64 parentIndex) 1 a) →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec b1 (selected byte shift) a ∧
      ¬CallWrites s c a)
    (wordsApart : ∀ a, (InRange (s.regs.r12.toBitVec + 48) 8 a ∨ InRange (s.regs.rbx.toBitVec + 8) 8 a ∨
        InRange (s.regs.rbx.toBitVec + 16) 8 a) → ¬CallWrites s c a)
    (node : s.regs.r12.toBitVec = .ofNat 64 base2) (down : s.regs.rdi.toBitVec = .ofNat 64 downBase)
    (leaf : s.regs.r8.toBitVec = .ofNat 64 base) (par : s.regs.rbx.toBitVec = .ofNat 64 parentBase)
    (readApart : ∀ span ∈ readSpans ((names.allocated base).allocated base2) nodeOffsets,
      ∀ a, span.contains a → ¬CallWrites s c a)
    (metadataApart : ∀ span ∈ metadataSpans ((names.allocated base).allocated base2) nodeOffsets,
      ∀ a, span.contains a → ¬CallWrites s c a)
    -- data side, as stages 1 and 2; `s.dmem` is the memory after the internal node's initialization
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (checked : heap names (target d) machine.data.dmem=.ok ())
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (valid2 : validate ((names.allocated base).allocated base2) nodeOffsets=.ok ())
    (init : InternalInit (names.allocated base) memory s.dmem base2 key common machine.data.regs.rbp.toNat)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (hasPeer : d.peers.get? pid=some owner)
    -- the source side: what `StepFacts` carries for this run, over the device before the sequence increment
    (cut : d=bump d0) (width : machine.data.regs.rbp.toNat=widthOf family)
    (case : (step d0 family key cidr pid (some parentId) exact outcomes).case = .split)
    (walked : walk (bump d0) (rootOf d0 family) key cidr (widthOf family) (some parentId) exact = true)
    -- the node the machine holds in `rdi` is the node below the placement, and what the code before
    -- `+0x338` computed for it: the internal node's prefix length and the bit selected for the node below
    (found : below (bump d0) (rootOf d0 family) key (some parentId) = some downId)
    (downFacts : ∀ down, (bump d0).nodes.get? downId = some down →
      common = min cidr (AllowedipsRelation.common (widthOf family) down.bits key) ∧
      b1 = down.bits/2^(widthOf family-1-common)%2) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t =>
      t.pc = Add.entry + 0x549 ∧ t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧
      t.data.regs.rbp = s.regs.rbp ∧ t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧
      t.data.regs.r14 = s.regs.r14 ∧ t.data.regs.r15 = s.regs.r15 ∧
      Corresponds ((names.allocated base).allocated base2) nodeOffsets t.data.dmem
        (step d0 family key cidr pid (some parentId) exact outcomes).device ∧
      heap ((names.allocated base).allocated base2)
        (target (step d0 family key cidr pid (some parentId) exact outcomes).device) t.data.dmem=.ok () ∧
      CallsReady c t.data ∧
      EqualOutside (PathWrites s c b1 (selected byte shift) (selected parentByte parentShift))
        s.dmem t.data.dmem ∧
      (step d0 family key cidr pid (some parentId) exact outcomes).answer = 0 ∧
      (step d0 family key cidr pid (some parentId) exact outcomes).consumed = 2)
      ⟨s, Add.entry + 0x338⟩ := by
  subst cut
  have belowNext := target_nodes_below related
  obtain ⟨downId',downNode,pnode,rest,found',hasDown,facts,device,answer,consumed,_,_,_⟩ :=
    split_step_parent case walked (show d0.peers.get? pid=some owner from hasPeer)
      belowNext
  have same : downId'=downId := Option.some.inj (found'.symm.trans found)
  subst same
  obtain ⟨least,downBit⟩ := downFacts downNode hasDown
  subst least
  have proper : min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)<machine.data.regs.rbp.toNat := by
    rw [width]; exact facts.proper
  have leafBit := split_leaf_bit pending init entry node leaf proper
  have short : pnode.cidr<pnode.bitlen := by
    have := facts.measure
    have := facts.proper
    have := facts.sameWidth
    omega
  have parentBit := split_parent_bit related pending init parentNamed facts.hasParent
    (width.trans facts.sameWidth) short node par indexRead shiftRead byteRead
  rw [width] at leafBit
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (split_parent_exit fetch agree tracePc c s b1 byteIndex shift byte parentIndex parentShift parentByte owner
      entry parent ready contextApart contextApart3 indexRead shiftRead byteRead indexBound shiftBound byteBound nodeParentMapped parentLeft parentRight readsApart wordsApart node down leaf par readApart metadataApart related checked pending valid2 init downNamed parentNamed
      hasDown hasPeer width facts device downBit leafBit parentBit)
  rintro t ⟨pc,rbx,rsp,rbp,r12,r13,r14,r15,related',shape,ready',frame⟩
  exact ⟨pc,rbx,rsp,rbp,r12,r13,r14,r15,related',shape,ready',frame,answer,consumed⟩

#print axioms split_parent_from_step
theorem split_root_from_step (fetch : Int64 → Option Decoded)
    (agree : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (b1 byteIndex shift byte : Nat) (v4 : Bool)
    {names : Names} {machine : MachineState} {memory : DataMem} {d : Device}
    {key cidr common pid base base2 downId downBase : Nat}
    {d0 : Device} {family : Nat} {exact : Bool} {outcomes : List Bool} (owner : Peer)
    (entry : SplitStage3.Entry s b1 byteIndex shift byte)
    (noParent : s.regs.rbx = 0)
    (ready : CallsReady c s)
    (contextApart : ∀ a, c.bytes a →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec b1 (selected byte shift) a)
    (contextApartRoot : ∀ a, c.bytes a → ¬(InRange (s.regs.r12.toBitVec + 48) 8 a ∨
      InRange (BitVec.ofNat 64 (names.table+rootOffset v4)) 8 a))
    (slotRead : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 =
      some (BitVec.ofNat 64 (names.table+rootOffset v4)).toInt)
    (nodeParentMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 48) 8).isSome = true)
    (rootMapped : (s.dmem.loadInt (BitVec.ofNat 64 (names.table+rootOffset v4)) 8).isSome = true)
    (savedSlotApart : ∀ a, InRange (s.regs.rsp.toBitVec + 8) 8 a →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec b1 (selected byte shift) a ∧
      ¬CallWrites s c a)
    (wordsApart : ∀ a, (InRange (s.regs.r12.toBitVec + 48) 8 a ∨
      InRange (BitVec.ofNat 64 (names.table+rootOffset v4)) 8 a) → ¬CallWrites s c a)
    (node : s.regs.r12.toBitVec = .ofNat 64 base2) (down : s.regs.rdi.toBitVec = .ofNat 64 downBase)
    (leaf : s.regs.r8.toBitVec = .ofNat 64 base)
    (readApart : ∀ span ∈ readSpans ((names.allocated base).allocated base2) nodeOffsets,
      ∀ a, span.contains a → ¬CallWrites s c a)
    (metadataApart : ∀ span ∈ metadataSpans ((names.allocated base).allocated base2) nodeOffsets,
      ∀ a, span.contains a → ¬CallWrites s c a)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (heapBefore : heap names (target d) machine.data.dmem=.ok ())
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (valid2 : validate ((names.allocated base).allocated base2) nodeOffsets=.ok ())
    (init : InternalInit (names.allocated base) memory s.dmem base2 key common machine.data.regs.rbp.toNat)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (hasPeer : d.peers.get? pid=some owner)
    -- the source side: what `StepFacts` carries for this run, over the device before the sequence increment
    (cut : d=bump d0) (width : machine.data.regs.rbp.toNat=widthOf family) (fam : v4=(family == 4))
    (ord : ordered d0 = true)
    (case : (step d0 family key cidr pid none exact outcomes).case = .split)
    (walked : walk (bump d0) (rootOf d0 family) key cidr (widthOf family) none exact = true)
    -- the node the machine holds in `rdi` is the family's root, and what the code before `+0x338`
    -- computed for it
    (found : rootOf d0 family = some downId)
    (downFacts : ∀ down, (bump d0).nodes.get? downId = some down →
      common = min cidr (AllowedipsRelation.common (widthOf family) down.bits key) ∧
      b1 = down.bits/2^(widthOf family-1-common)%2) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t =>
      t.pc = Add.entry + 0x549 ∧ t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧
      t.data.regs.rbp = s.regs.rbp ∧ t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧
      t.data.regs.r14 = s.regs.r14 ∧ t.data.regs.r15 = s.regs.r15 ∧ CallsReady c t.data ∧
      EqualOutside (RootPathWrites s c b1 (selected byte shift) (BitVec.ofNat 64 (names.table+rootOffset v4)))
        s.dmem t.data.dmem ∧
      Corresponds ((names.allocated base).allocated base2) nodeOffsets t.data.dmem
        (step d0 family key cidr pid none exact outcomes).device ∧
      heap ((names.allocated base).allocated base2)
        (target (step d0 family key cidr pid none exact outcomes).device) t.data.dmem=.ok () ∧
      (step d0 family key cidr pid none exact outcomes).answer = 0 ∧
      (step d0 family key cidr pid none exact outcomes).consumed = 2)
      ⟨s, Add.entry + 0x338⟩ := by
  subst cut fam
  have belowNext := target_nodes_below related
  obtain ⟨downId',downNode,rest,hasDown,rootHere,otherRoot,facts,device,answer,consumed,_,_,_⟩ :=
    split_step_root ord case walked (show d0.peers.get? pid=some owner from hasPeer) belowNext
  have same : downId'=downId := by
    apply Option.some.inj
    rw [←rootHere,←found]
    unfold rootOf
    split <;> rfl
  subst same
  obtain ⟨least,downBit⟩ := downFacts downNode hasDown
  subst least
  have proper : min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)<machine.data.regs.rbp.toNat := by
    rw [width]; exact facts.proper
  have leafBit := split_leaf_bit pending init entry node leaf proper
  rw [width] at leafBit
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (split_root_exit fetch agree tracePc c s b1 byteIndex shift byte (family == 4) owner
      entry noParent ready contextApart contextApartRoot slotRead nodeParentMapped rootMapped savedSlotApart wordsApart node down leaf readApart metadataApart related heapBefore pending valid2 init downNamed
      hasDown hasPeer width rfl rootHere otherRoot facts device downBit leafBit)
  rintro t ⟨pc,rbx,rsp,rbp,r12,r13,r14,r15,ready',frame,related',shape⟩
  exact ⟨pc,rbx,rsp,rbp,r12,r13,r14,r15,ready',frame,related',shape,answer,consumed⟩

#print axioms split_root_from_step
end Binary.Pair.Allowedips.C1Split
