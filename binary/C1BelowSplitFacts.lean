import C1BelowSplitExit
import C1BelowSplitSelect

/-! Result C1, work package 3, the split path: T5's capstones restated over
the plan's source side. The ordering hypotheses are `SplitParentFacts` /
`SplitRootFacts` (from `split_step_parent` / `split_step_root`), the device
is `step`'s, and the three machine-selected bits are equated with the
mirror's sides (`selected_link` gives two of them from decodes; the bit for
the node below is computed before `Add.entry+0x338`). The machine-state
hypotheses are T5's, unchanged. -/
namespace Binary.Pair.Allowedips.C1Split
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.SplitStage3 Binary.SplitStage3.Path
open Binary.CommonBitsCoverage Leanux Leanux.WG Root
local instance : Labels := Image.linkedLabels

theorem split_parent_exit (fetch : Int64 → Option Decoded)
    (agree : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (b1 byteIndex shift byte parentIndex parentShift parentByte : Nat)
    {names : Names} {machine : MachineState} {memory : DataMem} {d : Device}
    {key cidr common pid base base2 downId downBase parentId parentBase bits : Nat} {installed : Device}
    {parentNode downNode : AipNode} (owner : Peer)
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
    (hasDown : d.nodes.get? downId=some downNode) (hasPeer : d.peers.get? pid=some owner)
    -- the source side (`split_step_parent`): the ordering facts and `step`'s device
    (width : machine.data.regs.rbp.toNat=bits)
    (facts : Binary.Statements.C1.Proof.SplitParentFacts d key cidr bits common parentId downId downNode parentNode)
    (device : installed=intermediateInstalled d downId (downNode.bits/2^(bits-1-common)%2)
      (key/2^(bits-1-common)%2) parentId (key/2^(parentNode.bitlen-1-parentNode.cidr)%2) key cidr common bits pid
      downNode parentNode owner)
    -- the machine's three selected bits are the mirror's (`selected_link`, and the `choose` before `+0x338`)
    (downBit : b1=downNode.bits/2^(bits-1-common)%2)
    (leafBit : selected byte shift=key/2^(bits-1-common)%2)
    (parentBit : selected parentByte parentShift=key/2^(parentNode.bitlen-1-parentNode.cidr)%2) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t =>
      t.pc = Add.entry + 0x549 ∧ t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧
      t.data.regs.rbp = s.regs.rbp ∧ t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧
      t.data.regs.r14 = s.regs.r14 ∧ t.data.regs.r15 = s.regs.r15 ∧
      Corresponds ((names.allocated base).allocated base2) nodeOffsets t.data.dmem installed ∧
      heap ((names.allocated base).allocated base2) (target installed) t.data.dmem=.ok () ∧
      CallsReady c t.data ∧
      EqualOutside (PathWrites s c b1 (selected byte shift) (selected parentByte parentShift))
        s.dmem t.data.dmem)
      ⟨s, Add.entry + 0x338⟩ := by
  subst width
  have same : installed=intermediateInstalled d downId b1 (selected byte shift) parentId
      (selected parentByte parentShift) key cidr common machine.data.regs.rbp.toNat pid downNode parentNode owner := by
    rw [device,downBit,leafBit,parentBit]
  rw [same]
  exact machine_intermediate_nonnull fetch agree tracePc c s b1 byteIndex shift byte parentIndex parentShift
    parentByte owner entry parent ready contextApart contextApart3 indexRead shiftRead byteRead indexBound shiftBound byteBound nodeParentMapped parentLeft parentRight readsApart wordsApart node down leaf par readApart metadataApart related checked pending valid2 init downNamed parentNamed
    hasDown facts.hasParent hasPeer facts.different (by rw [parentBit]; exact facts.occupied) facts.sameWidth
    facts.measure facts.prefixEq parentBit.symm facts.downMeasure facts.leafMeasure facts.downPrefix downBit.symm
    leafBit.symm (by rw [downBit,leafBit]; exact facts.sides)

#print axioms split_parent_exit
theorem split_root_exit (fetch : Int64 → Option Decoded)
    (agree : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (b1 byteIndex shift byte : Nat) (v4 : Bool)
    {names : Names} {machine : MachineState} {memory : DataMem} {d : Device}
    {key cidr common pid base base2 downId downBase bits : Nat} {installed : Device} {downNode : AipNode} (owner : Peer)
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
    (hasDown : d.nodes.get? downId=some downNode) (hasPeer : d.peers.get? pid=some owner)
    -- the source side (`split_step_root`): the root slots, the ordering facts and `step`'s device
    (width : machine.data.regs.rbp.toNat=bits) (family : bits=if v4 then 32 else 128)
    (rootHere : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6)=some downId)
    (otherRoot : (if v4 then d.peerAllowedips.root6 else d.peerAllowedips.root4)≠some downId)
    (facts : Binary.Statements.C1.Proof.SplitRootFacts key cidr bits common downNode)
    (device : installed=intermediateRootInstalled d v4 downId (downNode.bits/2^(bits-1-common)%2)
      (key/2^(bits-1-common)%2) key cidr common bits pid downNode owner)
    -- the machine's two selected bits are the mirror's
    (downBit : b1=downNode.bits/2^(bits-1-common)%2)
    (leafBit : selected byte shift=key/2^(bits-1-common)%2) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t =>
      t.pc = Add.entry + 0x549 ∧ t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧
      t.data.regs.rbp = s.regs.rbp ∧ t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧
      t.data.regs.r14 = s.regs.r14 ∧ t.data.regs.r15 = s.regs.r15 ∧ CallsReady c t.data ∧
      EqualOutside (RootPathWrites s c b1 (selected byte shift) (BitVec.ofNat 64 (names.table+rootOffset v4)))
        s.dmem t.data.dmem ∧
      Corresponds ((names.allocated base).allocated base2) nodeOffsets t.data.dmem installed ∧
      heap ((names.allocated base).allocated base2) (target installed) t.data.dmem=.ok ())
      ⟨s, Add.entry + 0x338⟩ := by
  subst width
  have same : installed=intermediateRootInstalled d v4 downId b1 (selected byte shift) key cidr common
      machine.data.regs.rbp.toNat pid downNode owner := by
    rw [device,downBit,leafBit]
  rw [same]
  exact machine_intermediate_root_exit fetch agree tracePc c s b1 byteIndex shift byte v4 owner
    entry noParent ready contextApart contextApartRoot slotRead nodeParentMapped rootMapped savedSlotApart wordsApart node down leaf readApart metadataApart related heapBefore pending valid2 init downNamed
    hasDown hasPeer rootHere otherRoot family facts.downWidth facts.downMeasure facts.leafMeasure
    facts.downPrefix downBit.symm leafBit.symm (by rw [downBit,leafBit]; exact facts.sides)

#print axioms split_root_exit
end Binary.Pair.Allowedips.C1Split
