import C1BelowSplitTransfer
import C1BelowSplitMachineRoot
import C1BelowSplitRootSource

/- Origin: trial source binary-trials/t5/T5PathRoot.lean on branch task/binary-trials (unreviewed), ported for C1 work
package 3 with module and namespace renames only unless a comment marked "C1 port" says otherwise. -/
/-! Trial T5, stage 3, NULL-parent path: `Add.entry+0x338` to the common exit `+0x549`
through t1's 22 instructions (exit at `+0x6c0`), the KCOV callback there, and the root
publication (`RootExit.root_exit`); and its data result (`Corresponds` only: `heap` for
the NULL-parent subcase was not proved in this trial). -/
namespace Binary.Pair.Allowedips.C1Split
open AllowedipsMutationImage TrustBase AllowedipsChild Binary.SplitStage3 Binary.SplitStage3.Path
open Binary.CommonBitsCoverage Leanux Leanux.WG Root
local instance : Labels := Image.linkedLabels

/-- Everything the NULL-parent segment may write. -/
def RootPathWrites (s : MachineData) (c : Context) (direction bit : Nat) (trieSlot : BitVec 64)
    (a : BitVec 64) : Prop :=
  Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec direction bit a ∨ CallWrites s c a ∨
    InRange (s.regs.r12.toBitVec + 48) 8 a ∨ InRange trieSlot 8 a

theorem connections_root (fetch : Int64 → Option Decoded)
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
    (slotRead : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some trieSlot.toInt)
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
  have slotV : v.data.dmem.loadInt (v.data.regs.rsp.toBitVec + 8) 8 = some trieSlot.toInt := by
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
    (RootExit.root_exit fetch agree v.data trieSlot slotV nodeV rootV)
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

#print axioms connections_root

/-- NULL-parent capstone (data only): the exit memory corresponds to the mirror device
after `chooseAndConnectNode node down; chooseAndConnectNode node newnode;
connectNode root node`. -/
theorem machine_intermediate_root (fetch : Int64 → Option Decoded)
    (agree : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch) (c : Context)
    (s : MachineData) (b1 byteIndex shift byte : Nat) (v4 : Bool)
    {names : Names} {machine : MachineState} {memory : DataMem} {d : Device}
    {key cidr common pid base base2 downId downBase : Nat} {downNode : AipNode} {owner : Peer}
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
    (savedApart : ∀ a, InRange (s.regs.rsp.toBitVec + 8) 8 a →
      ¬Writes s.regs.r12.toBitVec s.regs.rdi.toBitVec s.regs.r8.toBitVec b1 (selected byte shift) a ∧
      ¬CallWrites s c a)
    (wordsApart : ∀ a, (InRange (s.regs.r12.toBitVec + 48) 8 a ∨
      InRange (BitVec.ofNat 64 (names.table+rootOffset v4)) 8 a) → ¬CallWrites s c a)
    (node : s.regs.r12.toBitVec = .ofNat 64 base2) (down : s.regs.rdi.toBitVec = .ofNat 64 downBase)
    (leaf : s.regs.r8.toBitVec = .ofNat 64 base)
    (readApart : ∀ span ∈ readSpans ((names.allocated base).allocated base2) nodeOffsets,
      ∀ a, span.contains a → ¬CallWrites s c a)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (pending : NodeInit.Pending names machine.data d key cidr pid base memory)
    (valid2 : validate ((names.allocated base).allocated base2) nodeOffsets=.ok ())
    (init : InternalInit (names.allocated base) memory s.dmem base2 key common machine.data.regs.rbp.toNat)
    (downNamed : (downId,downBase) ∈ names.trie.nodes)
    (hasDown : d.nodes.get? downId=some downNode) (hasPeer : d.peers.get? pid=some owner) :
    Eventually (@instructionStep Image.linkedLabels fetch) (fun t =>
      t.pc = Add.entry + 0x549 ∧ t.data.regs.rbx = 0 ∧ t.data.regs.rsp = s.regs.rsp ∧
      Corresponds ((names.allocated base).allocated base2) nodeOffsets t.data.dmem
        (intermediateRootInstalled d v4 downId b1 (selected byte shift) key cidr common
          machine.data.regs.rbp.toNat pid downNode owner)) ⟨s, Add.entry + 0x338⟩ := by
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (connections_root fetch agree tracePc c s b1 byteIndex shift byte _ entry noParent ready contextApart
      contextApartRoot slotRead nodeParentMapped rootMapped savedApart wordsApart)
  rintro t ⟨mid, frame, pcT, memT, rbxT, rspT, _, _, _, _, _⟩
  have framed := (frame.storeInt (s.regs.r12.toBitVec + 48) 8
    (BitVec.ofNat 64 (names.table+rootOffset v4) ||| 2).toInt).storeInt
    (BitVec.ofNat 64 (names.table+rootOffset v4)) 8 s.regs.r12.toBitVec.toInt
  rw [←memT, node, down, leaf, memRoot_connectMemory, connected_connectMemory] at framed
  refine ⟨pcT, rbxT, rspT, ?_⟩
  have data := intermediate_root_corresponds (downNode:=downNode) (owner:=owner) v4 related pending valid2
    init downNamed entry.directionBound (Direct.selected_bound byte shift) hasDown hasPeer
  unfold Corresponds at data ⊢
  rw [←reconstruct_frame _ nodeOffsets framed readApart]
  exact data

#print axioms machine_intermediate_root
end Binary.Pair.Allowedips.C1Split
