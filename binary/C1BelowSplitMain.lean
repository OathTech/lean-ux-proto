import C1BelowSplitTransfer

/- Origin: trial source binary-trials/t5/T5Main.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, capstone (non-NULL parent): from `Add.entry+0x338`, with the internal node
initialized, the image reaches the common exit `+0x549` with return value 0 in `rbx`, in a
memory that corresponds, under the twice-extended names, to the mirror device after its
three `chooseAndConnectNode` calls, and satisfies `heap`. -/
namespace Binary.Pair.Allowedips.C1Split
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.SplitStage3 Binary.SplitStage3.Path
open Binary.CommonBitsCoverage Leanux Leanux.WG Root
local instance : Labels := Image.linkedLabels

theorem machine_intermediate_nonnull (fetch : Int64 → Option Decoded)
    (agree : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (b1 byteIndex shift byte parentIndex parentShift parentByte : Nat)
    {names : Names} {machine : MachineState} {memory : DataMem} {d : Device}
    {key cidr common pid base base2 downId downBase parentId parentBase : Nat}
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
    (hasDown : d.nodes.get? downId=some downNode) (hasParent : d.nodes.get? parentId=some parentNode)
    (hasPeer : d.peers.get? pid=some owner) (different : downId≠parentId)
    (occupied : parentNode.bit[selected parentByte parentShift]?=some (some downId))
    (sameWidth : machine.data.regs.rbp.toNat=parentNode.bitlen) (measure : parentNode.cidr<common)
    (prefixEq : key/2^(parentNode.bitlen-parentNode.cidr)=parentNode.bits/2^(parentNode.bitlen-parentNode.cidr))
    (side : key/2^(parentNode.bitlen-1-parentNode.cidr)%2=selected parentByte parentShift)
    (downMeasure : common<downNode.cidr) (leafMeasure : common<cidr)
    (downPrefix : downNode.bits/2^(machine.data.regs.rbp.toNat-common)=
      key/2^(machine.data.regs.rbp.toNat-common))
    (downSide : downNode.bits/2^(machine.data.regs.rbp.toNat-1-common)%2=b1)
    (leafSide : key/2^(machine.data.regs.rbp.toNat-1-common)%2=selected byte shift)
    (sides : b1≠selected byte shift) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t =>
      t.pc = Add.entry + 0x549 ∧ t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧
      t.data.regs.rbp = s.regs.rbp ∧ t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧
      t.data.regs.r14 = s.regs.r14 ∧ t.data.regs.r15 = s.regs.r15 ∧
      Corresponds ((names.allocated base).allocated base2) nodeOffsets t.data.dmem
        (intermediateInstalled d downId b1 (selected byte shift) parentId (selected parentByte parentShift)
          key cidr common machine.data.regs.rbp.toNat pid downNode parentNode owner) ∧
      heap ((names.allocated base).allocated base2)
        (target (intermediateInstalled d downId b1 (selected byte shift) parentId
          (selected parentByte parentShift) key cidr common machine.data.regs.rbp.toNat pid
          downNode parentNode owner)) t.data.dmem=.ok () ∧ CallsReady c t.data ∧
      EqualOutside (PathWrites s c b1 (selected byte shift) (selected parentByte parentShift))
        s.dmem t.data.dmem)
      ⟨s, Add.entry + 0x338⟩ := by
  have bit1 := entry.directionBound
  have bit2 := Direct.selected_bound byte shift
  have bit := Direct.selected_bound parentByte parentShift
  have targetEq := target_intermediateInstalled d downId b1 (selected byte shift) parentId
    (selected parentByte parentShift) key cidr common machine.data.regs.rbp.toNat pid downNode parentNode owner
    hasDown hasParent hasPeer different (target_nodes_below related)
  unfold Corresponds
  rw [targetEq]
  exact machine_connections_transfer fetch agree tracePc c s b1 byteIndex shift byte parentIndex parentShift
    parentByte entry parent ready contextApart contextApart3 indexRead shiftRead byteRead indexBound shiftBound byteBound
    nodeParentMapped parentLeft parentRight readsApart wordsApart node down leaf par readApart metadataApart
    (reconstruct_intermediate_connect related pending valid2 init downNamed parentNamed bit1 bit2 bit)
    (intermediate_connect_heap owner related checked pending valid2 init downNamed parentNamed hasPeer
      (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasParent)
      (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown) bit bit1 bit2 occupied sameWidth measure
      prefixEq side downMeasure leafMeasure downPrefix downSide leafSide sides)

#print axioms machine_intermediate_nonnull
end Binary.Pair.Allowedips.C1Split
