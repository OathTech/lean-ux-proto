import C1BelowSplitSegment

/-! Result C1, work package 3, the split path, root sub-case: the root
publication with the saved root-slot pointer read as an unsigned word.

The trial's lemma for `add+0x6c5` (`RootExit.regionF`, and the four theorems
built on it) states the read of the saved slot pointer at `rsp+8` as
`loadInt … = some trieSlot.toInt`. A load never returns a negative value, so
that hypothesis cannot be met when the table lies in the upper half of the
address space (as kernel addresses do). The five theorems are repeated here
with the read stated as `some (trieSlot.toNat : Int)`; nothing else changes.
Origin: `C1BelowSplitMachineRoot` (regionF, root_exit), `C1BelowSplitPathRoot`
(connections_root), `C1BelowSplitExit` (machine_intermediate_root_exit),
`C1BelowSplitFacts` (split_root_exit), `C1BelowSplitSegment`
(split_root_from_step). -/
namespace Binary.SplitStage3.RootExit
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.SplitStage3
local instance : Labels := Image.linkedLabels

theorem nat_emod_toNat (x : BitVec 64) : ((x.toNat : Int) % 18446744073709551616).toNat = x.toNat := by
  have bound := x.isLt
  omega

theorem ofInt_nat_bmod64 (x : BitVec 64) :
    BitVec.ofInt 64 ((x.toNat : Int).bmod 18446744073709551616) = x := by
  rw [AllowedipsChild.ofInt_bmod64,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem or_two_bmod64 (x : BitVec 64) :
    ((x.toNat ||| 2 : Nat) : Int).bmod 18446744073709551616 = (x ||| 2).toInt := by
  have value : (x ||| 2).toNat = x.toNat ||| 2 := by rw [BitVec.toNat_or]; rfl
  have signed : (BitVec.ofNat 64 (x ||| 2).toNat).toInt = (((x ||| 2).toNat : Nat) : Int).bmod (2^64) :=
    BitVec.toInt_ofNat' ..
  rw [BitVec.ofNat_toNat,BitVec.setWidth_eq] at signed
  rw [signed,value]

theorem regionF_nat (s : MachineData) (trieSlot : BitVec 64)
    (slotRead : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some (trieSlot.toNat : Int))
    (nodeMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 48) 8).isSome = true)
    (rootMapped : ((s.dmem.storeInt (s.regs.r12.toBitVec + 48) 8 (trieSlot ||| 2).toInt).loadInt
        trieSlot 8).isSome = true) :
    (Directives.interp Add.r6c5 s (Add.entry + 0x6c5) (fun p d => .done ⟨d, p⟩)).All (fun t =>
      t.pc = Add.entry + 0x549 ∧
      t.data.dmem = memRoot s trieSlot ∧
      t.data.regs = {s.regs with rax := UInt64.ofBitVec (trieSlot ||| 2), rbx := 0, rdx := UInt64.ofBitVec trieSlot}) := by
  obtain ⟨old, oldRead⟩ := Option.isSome_iff_exists.mp nodeMapped
  obtain ⟨old2, oldRead2⟩ := Option.isSome_iff_exists.mp rootMapped
  simp [Add.r6c5,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    memRoot] at slotRead oldRead oldRead2 ⊢
  rw [slotRead]
  simp only [Effects.All,nat_emod_toNat,ofInt_nat_bmod64]
  rw [or_two_bmod64]
  rw [oldRead]
  simp only [Effects.All]
  intro v
  rw [or_two_bmod64] at oldRead2
  rw [oldRead2]
  simp [RelRegOrMem.interp,ConstExpr.interp,Effects.All,BitVec.ofInt_natCast]
  rfl

#print axioms regionF_nat

/-- From `Add.entry+0x6c5` (after the KCOV call) to the common exit: the root slot
pointer saved at `8(%rsp)` receives the internal node, whose parent word is the
tagged slot address. -/
theorem root_exit_nat (fetch : Int64 → Option Decoded) (agree : AllowedipsMutationDecoderAgreement fetch)
    (s : MachineData) (trieSlot : BitVec 64)
    (slotRead : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some (trieSlot.toNat : Int))
    (nodeMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 48) 8).isSome = true)
    (rootMapped : (s.dmem.loadInt trieSlot 8).isSome = true) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t =>
      t.pc = Add.entry + 0x549 ∧ t.data.dmem = memRoot s trieSlot ∧
      t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧ t.data.regs.rbp = s.regs.rbp ∧
      t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧ t.data.regs.r14 = s.regs.r14 ∧
      t.data.regs.r15 = s.regs.r15) ⟨s, Add.entry + 0x6c5⟩ := by
  have run := regionF_nat s trieSlot slotRead nodeMapped (storeInt_defined _ _ _ _ _ _ rootMapped)
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (r6c5_layout agree) s _ run)
  rintro t ⟨pcT, memT, regsT⟩
  simp only [pcT, memT, regsT]
  simp only [and_self]

#print axioms root_exit_nat

end Binary.SplitStage3.RootExit

namespace Binary.Pair.Allowedips.C1Split
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.SplitStage3 Binary.SplitStage3.Path
open Binary.CommonBitsCoverage Leanux Leanux.WG Root Binary.Statements.C1.Proof
local instance : Labels := Image.linkedLabels

theorem connections_root_nat (fetch : Int64 → Option Decoded)
    (agree : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (direction byteIndex shift byte : Nat) (trieSlot : BitVec 64)
    (entry : SplitStage3.Entry s direction byteIndex shift byte)
    (noParent : s.regs.rbx = 0)
    (ready : CallsReady c s)
    (contextApart : ∀ a, c.bytes a →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec direction (selected byte shift) a)
    (contextApartRoot : ∀ a, c.bytes a →
      ¬(InRange (s.regs.r12.toBitVec + 48) 8 a ∨ InRange trieSlot 8 a))
    -- the root slot pointer saved at 8(%rsp), and the two words the publication writes
    (slotRead : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some (trieSlot.toNat : Int))
    (nodeParentMapped : (s.dmem.loadInt (s.regs.r12.toBitVec + 48) 8).isSome = true)
    (rootMapped : (s.dmem.loadInt trieSlot 8).isSome = true)
    (savedApart : ∀ a, InRange (s.regs.rsp.toBitVec + 8) 8 a →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec direction (selected byte shift) a ∧
      ¬CallWrites s c a)
    (wordsApart : ∀ a, (InRange (s.regs.r12.toBitVec + 48) 8 a ∨ InRange trieSlot 8 a) →
      ¬CallWrites s c a) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t => ∃ mid : DataMem,
      EqualOutside (CallWrites s c)
        (connected s.dmem s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec direction
          (selected byte shift)) mid ∧
      t.pc = Add.entry + 0x549 ∧
      t.data.dmem = (mid.storeInt (s.regs.r12.toBitVec + 48) 8 (trieSlot ||| 2).toInt).storeInt
          trieSlot 8 s.regs.r12.toBitVec.toInt ∧
      t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧ t.data.regs.rbp = s.regs.rbp ∧
      t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧ t.data.regs.r14 = s.regs.r14 ∧
      t.data.regs.r15 = s.regs.r15 ∧ CallsReady c t.data ∧
      EqualOutside (RootPathWrites s c direction (selected byte shift) trieSlot) s.dmem t.data.dmem)
      ⟨s, Add.entry + 0x338⟩ := by
  have first := Direct.target fetch agree s direction byteIndex shift byte entry
  apply eventually_trans (instructionStep fetch) _ _ _ first
  intro u exit
  obtain ⟨pcU, memU, _, _, _, rbxU, rspU, rbpU, _, _, r12U, r13U, r14U, r15U⟩ := exit
  simp only [noParent, ↓reduceIte] at pcU
  have frameU := connected_frame s.dmem s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec
    direction (selected byte shift)
  rw [←memU] at frameU
  have readyU : CallsReady c u.data := ready.frame rspU frameU
    (memU ▸ connected_mapped s.dmem _ _ _ _ _) contextApart
  have here := agree.add _ _ (show Add.fetch (Add.entry+0x6c0)=some _ from rfl)
  rw [Placement.at_pc u _ pcU]
  apply eventually_trans (instructionStep fetch) _ _ _
    (Binary.Pair.Services.call fetch (Add.entry+0x6c0) "L_ffffffff810f31f0" .pc tracePc here c u.data readyU)
  rintro v ⟨pcV, rspV, rbxV, rbpV, r12V, r13V, r14V, r15V, readyV, frameV⟩
  rw [rspU] at frameV
  have slotV : v.data.dmem.loadInt (v.data.regs.rsp.toBitVec + 8) 8 = some (trieSlot.toNat : Int) := by
    rw [rspV, rspU, ←frameV.loadInt _ 8 (fun i hi => (savedApart _ ⟨i, hi, rfl⟩).2),
      ←frameU.loadInt _ 8 (fun i hi => (savedApart _ ⟨i, hi, rfl⟩).1)]
    exact slotRead
  have nodeV : (v.data.dmem.loadInt (v.data.regs.r12.toBitVec + 48) 8).isSome = true := by
    rw [r12V, r12U, ←frameV.loadInt _ 8 (fun i hi => wordsApart _ (.inl ⟨i, hi, rfl⟩)), memU]
    exact connected_mapped s.dmem _ _ _ _ _ _ _ nodeParentMapped
  have rootV : (v.data.dmem.loadInt trieSlot 8).isSome = true := by
    rw [←frameV.loadInt _ 8 (fun i hi => wordsApart _ (.inr ⟨i, hi, rfl⟩)), memU]
    exact connected_mapped s.dmem _ _ _ _ _ _ _ rootMapped
  have pcV' : v.pc = Add.entry + 0x6c5 := pcV.trans (by rfl)
  rw [Placement.at_pc v _ pcV']
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (RootExit.root_exit_nat fetch agree v.data trieSlot slotV nodeV rootV)
  rintro t ⟨pcT, memT, rbxT, rspT, rbpT, r12T, r13T, r14T, r15T⟩
  have memT' : t.data.dmem = (v.data.dmem.storeInt (s.regs.r12.toBitVec + 48) 8 (trieSlot ||| 2).toInt).storeInt
      trieSlot 8 s.regs.r12.toBitVec.toInt := by
    simpa only [RootExit.memRoot, r12V, r12U] using memT
  have frame3 : EqualOutside (fun a => InRange (s.regs.r12.toBitVec + 48) 8 a ∨ InRange trieSlot 8 a)
      v.data.dmem t.data.dmem := by
    intro a outside
    rw [memT']
    exact (storeInt_frame _ _ _ _ a (fun h => outside (.inl h))).trans
      (storeInt_frame _ _ _ _ a (fun h => outside (.inr h)))
  have readyT : CallsReady c t.data := readyV.frame rspT frame3
    (fun _ _ h => by rw [memT']; exact storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ h))
    contextApartRoot
  have total : EqualOutside (RootPathWrites s c direction (selected byte shift) trieSlot)
      s.dmem t.data.dmem := by
    intro a outside
    exact ((frameU a (fun h => outside (.inl h))).trans
      (frameV a (fun h => outside (.inr (.inl h))))).trans (frame3 a (fun h => outside (.inr (.inr h))))
  rw [memU] at frameV
  exact ⟨v.data.dmem, frameV, pcT, memT', rbxT, rspT.trans (rspV.trans rspU), rbpT.trans (rbpV.trans rbpU),
    r12T.trans (r12V.trans r12U), r13T.trans (r13V.trans r13U), r14T.trans (r14V.trans r14U),
    r15T.trans (r15V.trans r15U), readyT, total⟩


theorem machine_intermediate_root_exit_nat (fetch : Int64 → Option Decoded)
    (agree : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (b1 byteIndex shift byte : Nat) (v4 : Bool)
    {names : Names} {machine : MachineState} {memory : DataMem} {d : Device}
    {key cidr common pid base base2 downId downBase : Nat} {downNode : AipNode} (owner : Peer)
    (entry : SplitStage3.Entry s b1 byteIndex shift byte)
    (noParent : s.regs.rbx = 0)
    (ready : CallsReady c s)
    (contextApart : ∀ a, c.bytes a →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec b1 (selected byte shift) a)
    (contextApartRoot : ∀ a, c.bytes a → ¬(InRange (s.regs.r12.toBitVec + 48) 8 a ∨
      InRange (BitVec.ofNat 64 (names.table+rootOffset v4)) 8 a))
    (slotRead : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 =
      some ((BitVec.ofNat 64 (names.table+rootOffset v4)).toNat : Int))
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
    (rootHere : (if v4 then (target d).table.root4 else (target d).table.root6)=some downId)
    (otherRoot : (if v4 then (target d).table.root6 else (target d).table.root4)≠some downId)
    (family : machine.data.regs.rbp.toNat=if v4 then 32 else 128)
    (downWidth : downNode.bitlen=machine.data.regs.rbp.toNat)
    (downMeasure : common<downNode.cidr) (leafMeasure : common<cidr)
    (downPrefix : downNode.bits/2^(machine.data.regs.rbp.toNat-common)=
      key/2^(machine.data.regs.rbp.toNat-common))
    (downSide : downNode.bits/2^(machine.data.regs.rbp.toNat-1-common)%2=b1)
    (leafSide : key/2^(machine.data.regs.rbp.toNat-1-common)%2=selected byte shift)
    (sides : b1≠selected byte shift) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t =>
      t.pc = Add.entry + 0x549 ∧ t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧
      t.data.regs.rbp = s.regs.rbp ∧ t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧
      t.data.regs.r14 = s.regs.r14 ∧ t.data.regs.r15 = s.regs.r15 ∧ CallsReady c t.data ∧
      EqualOutside (RootPathWrites s c b1 (selected byte shift) (BitVec.ofNat 64 (names.table+rootOffset v4)))
        s.dmem t.data.dmem ∧
      Corresponds ((names.allocated base).allocated base2) nodeOffsets t.data.dmem
        (intermediateRootInstalled d v4 downId b1 (selected byte shift) key cidr common
          machine.data.regs.rbp.toNat pid downNode owner) ∧
      heap ((names.allocated base).allocated base2)
        (target (intermediateRootInstalled d v4 downId b1 (selected byte shift) key cidr common
          machine.data.regs.rbp.toNat pid downNode owner)) t.data.dmem=.ok ())
      ⟨s, Add.entry + 0x338⟩ := by
  have bit1 := entry.directionBound
  have bit2 := Direct.selected_bound byte shift
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (connections_root_nat fetch agree tracePc c s b1 byteIndex shift byte _ entry noParent ready contextApart
      contextApartRoot slotRead nodeParentMapped rootMapped savedSlotApart wordsApart)
  rintro t ⟨mid, frame, pcT, memT, rbxT, rspT, rbpT, r12T, r13T, r14T, r15T, readyT, total⟩
  have framed := (frame.storeInt (s.regs.r12.toBitVec + 48) 8
    (BitVec.ofNat 64 (names.table+rootOffset v4) ||| 2).toInt).storeInt
    (BitVec.ofNat 64 (names.table+rootOffset v4)) 8 s.regs.r12.toBitVec.toInt
  rw [←memT, node, down, leaf, memRoot_connectMemory, connected_connectMemory] at framed
  have targetEq := target_intermediateRootInstalled d v4 downId b1 (selected byte shift) key cidr common
    machine.data.regs.rbp.toNat pid downNode owner hasDown hasPeer (target_nodes_below related)
  have relatedT : Corresponds ((names.allocated base).allocated base2) nodeOffsets t.data.dmem
      (intermediateRootInstalled d v4 downId b1 (selected byte shift) key cidr common
        machine.data.regs.rbp.toNat pid downNode owner) := by
    have data := intermediate_root_corresponds (downNode:=downNode) (owner:=owner) v4 related pending valid2
      init downNamed bit1 bit2 hasDown hasPeer
    unfold Corresponds at data ⊢
    rw [←reconstruct_frame _ nodeOffsets framed readApart]
    exact data
  have shapeT : heap ((names.allocated base).allocated base2)
      (target (intermediateRootInstalled d v4 downId b1 (selected byte shift) key cidr common
        machine.data.regs.rbp.toNat pid downNode owner)) t.data.dmem=.ok () := by
    rw [targetEq,←heap_frame _ nodeOffsets _ framed metadataApart]
    exact intermediate_root_heap owner v4 related heapBefore pending valid2 init downNamed hasPeer
      (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown) bit1 bit2 rootHere otherRoot family
      downWidth downMeasure leafMeasure downPrefix downSide leafSide sides
  exact ⟨pcT,rbxT,rspT,rbpT,r12T,r13T,r14T,r15T,readyT,total,relatedT,shapeT⟩


theorem split_root_exit_nat (fetch : Int64 → Option Decoded)
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
      some ((BitVec.ofNat 64 (names.table+rootOffset v4)).toNat : Int))
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
  exact machine_intermediate_root_exit_nat fetch agree tracePc c s b1 byteIndex shift byte v4 owner
    entry noParent ready contextApart contextApartRoot slotRead nodeParentMapped rootMapped savedSlotApart wordsApart node down leaf readApart metadataApart related heapBefore pending valid2 init downNamed
    hasDown hasPeer rootHere otherRoot family facts.downWidth facts.downMeasure facts.leafMeasure
    facts.downPrefix downBit.symm leafBit.symm (by rw [downBit,leafBit]; exact facts.sides)


theorem split_root_from_step_nat (fetch : Int64 → Option Decoded)
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
      some ((BitVec.ofNat 64 (names.table+rootOffset v4)).toNat : Int))
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
    (split_root_exit_nat fetch agree tracePc c s b1 byteIndex shift byte (family == 4) owner
      entry noParent ready contextApart contextApartRoot slotRead nodeParentMapped rootMapped savedSlotApart wordsApart node down leaf readApart metadataApart related heapBefore pending valid2 init downNamed
      hasDown hasPeer width rfl rootHere otherRoot facts device downBit leafBit)
  rintro t ⟨pc,rbx,rsp,rbp,r12,r13,r14,r15,ready',frame,related',shape⟩
  exact ⟨pc,rbx,rsp,rbp,r12,r13,r14,r15,ready',frame,related',shape,answer,consumed⟩


#print axioms split_root_from_step_nat
end Binary.Pair.Allowedips.C1Split
