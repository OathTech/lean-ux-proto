import C1BelowPrefixCut
import C1BelowPrefixSelect
import C1BelowFlight

/-! Result C1, work package 3, prefix: from the cut (`add+0x156`) to the
selected node below the placement (`add+0x241`), when a node was placed
(`rbx ≠ 0`): the landed first initialization, the save of the fresh node, the
coverage call and the selector with an occupied slot. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root Binary.Pair.Allowedips.ChildFinish
local instance : Labels := Image.linkedLabels

/-- The bytes the prefix writes after the first initialization: the six
words below the stack pointer and the word at it (callbacks, `common_bits`,
the saved node below), the saved fresh node at `rsp+24`, the coverage buffer. -/
def Late (stack : UInt64) (c : Context) (a : BitVec 64) : Prop :=
  InRange (stack.toBitVec-48) 56 a ∨ InRange (stack.toBitVec+24) 8 a ∨ c.writes a

theorem late_after {stack : UInt64} {c : Context} {a : BitVec 64} (late : Late stack c a) :
    Zone stack a ∨ c.writes a := by
  rcases late with low|slot|buffer
  · exact .inl (zone_scratch (by decide) low)
  · exact .inl (zone_local (offset:=24) (by decide) slot)
  · exact .inr buffer

theorem late_word {stack : UInt64} {c : Context} {a : BitVec 64}
    (inside : InRange (stack.toBitVec-8) 8 a) : Late stack c a := by
  obtain ⟨i,bound,equal⟩ := inside
  refine .inl ⟨40+i,by omega,?_⟩
  rw [equal]
  bv_omega

theorem late_top {stack : UInt64} {c : Context} {a : BitVec 64}
    (inside : InRange stack.toBitVec 8 a) : Late stack c a := by
  obtain ⟨i,bound,equal⟩ := inside
  refine .inl ⟨48+i,by omega,?_⟩
  rw [equal]
  bv_omega

theorem slot_address (stack : UInt64) (offset : Nat) :
    BitVec.ofNat 64 (stack.toNat+offset)=stack.toBitVec+.ofNat 64 offset := by
  rw [BitVec.ofNat_add,ofNat_uint64]

/-- The state at `add+0x241`: the fresh node initialized and pending, its
address in `r8`, the address of the node below the placement in the stack
word at `rsp`. `m` is the memory the first initialization left. -/
structure Selected (names : Allowedips.Names) (c : Context) (e : MachineData) (d : Device)
    (key cidr pid base downId : Nat) (m : DataMem) (t : MachineState) : Prop where
  pc : t.pc=Add.entry+0x241
  stack : t.data.regs.rsp=e.regs.rsp
  bx : t.data.regs.rbx=e.regs.rbx
  r12 : t.data.regs.r12=e.regs.r12
  r13 : t.data.regs.r13=e.regs.r13
  r15 : t.data.regs.r15=e.regs.r15
  bp : t.data.regs.rbp=UInt64.ofNat (e.regs.rbp.toNat/8)
  r14 : t.data.regs.r14=UInt64.ofNat (base+32)
  r8 : t.data.regs.r8=UInt64.ofNat base
  ready : CallsReady c t.data
  late : EqualOutside (Late e.regs.rsp c) m t.data.dmem
  mapped : MappedLe e.dmem t.data.dmem
  pending : NodeInit.Pending names e d key cidr pid base t.data.dmem
  query : AllowedipsChild.QueryWords t.data.dmem e.regs.r13.toBitVec e.regs.rbp.toNat key
  down : ∃ child, child≠0 ∧ (downId,child) ∈ names.trie.nodes ∧
    t.data.dmem.loadInt e.regs.rsp.toBitVec 8=some (child : Int)

theorem selected_parent (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    {names : Allowedips.Names} {world : World} {e : MachineState}
    {key cidr pid base parentId downId : Nat} {d : Device} {parentNode : AipNode} (c : Context)
    (checked : NodeInit.boundary names nodeOffsets world e key cidr pid=.ok base)
    (device : world.wg.dev=some d)
    (res : Res names c e.data base)
    (ready : CallsReady c e.data)
    (parentNamed : (parentId,e.data.regs.rbx.toNat) ∈ names.trie.nodes)
    (hasParent : d.nodes.get? parentId=some parentNode)
    (sameWidth : e.data.regs.rbp.toNat=parentNode.bitlen)
    (short : parentNode.cidr<parentNode.bitlen)
    (occupied : parentNode.bit[key/2^(parentNode.bitlen-1-parentNode.cidr)%2]?=some (some downId))
    (downOld : downId≠names.nextNode) :
    ∃ m, NodeInit.effect e.data=.ok (m,base) ∧
      Eventually (instructionStep fetch) (Selected names c e.data d key cidr pid base downId m) e := by
  have fields := NodeInit.boundary_fields checked
  obtain ⟨actual,deviceAt,related,heapOk⟩ := assertAt_ok fields.asserted
  have equal : actual=d := Option.some.inj (deviceAt.symm.trans device)
  subst actual
  obtain ⟨memory,summary,execution⟩ := NodeInit.initialization_executes fetch decoder checked
  refine ⟨memory,summary,?_⟩
  have pending := NodeInit.pending_of_effect fields related heapOk summary
  have frame := (NodeInit.core_of_effect fields summary).2
  apply eventually_trans (instructionStep fetch) _ _ _ execution
  rintro a ⟨pcA,memA,registers,mappedA⟩
  have registerFacts : a.data.regs.rsp=e.data.regs.rsp ∧
      a.data.regs.rbx=e.data.regs.rbx ∧ a.data.regs.r12=e.data.regs.r12 ∧
      a.data.regs.r13=e.data.regs.r13 ∧ a.data.regs.r15=e.data.regs.r15 ∧
      a.data.regs.rbp=UInt64.ofNat (e.data.regs.rbp.toNat/8) ∧
      a.data.regs.r8=UInt64.ofNat base ∧ a.data.regs.r14=UInt64.ofNat (base+32) := by
    simpa only [NodeInit.registers,Bool.and_eq_true,beq_iff_eq,and_assoc] using registers
  obtain ⟨stack,bx,r12A,queryReg,r15A,bpA,allocation,r14A⟩ := registerFacts
  have fresh := (allocated_facts fields.allocated).2.2.1
  change base+72<2^64 at fresh
  have allocationNat : a.data.regs.r8.toNat=base := by
    rw [allocation]
    exact UInt64.toNat_ofNat_of_lt' (by change base<2^64; omega)
  have frameA : EqualOutside (NodeInit.EntryWrites names e.data base) e.data.dmem a.data.dmem := memA ▸ frame
  have pendingA : NodeInit.Pending names e.data d key cidr pid base a.data.dmem := memA ▸ pending
  have readyA := ready.frame stack frameA mappedA res.contextInit
  have queryA : AllowedipsChild.QueryWords a.data.dmem e.data.regs.r13.toBitVec e.data.regs.rbp.toNat key :=
    AllowedipsLoop.query_frame fields.family (Placement.queryLocals_fields fields.query)
      frameA fields.query_separated
  have parentNonzero : a.data.regs.rbx≠0 := by
    have positive := ((Trie.reconstruct_fields related.trie).nodeRange _ _ parentNamed).1
    intro zero
    rw [←bx,zero] at positive
    exact Nat.lt_irrefl 0 positive
  -- the save of the fresh node and the coverage call
  have slotMapped : (a.data.dmem.loadInt (.ofNat 64 (a.data.regs.rsp.toNat+24)) 8).isSome=true := by
    rw [stack]
    exact mappedA _ _ (res.local_mapped_nat 24 8 (by decide))
  have stored := store_total (value:=a.data.regs.r8.toNat) slotMapped
  have entryChecked : ChildSetup.entryEffect a.data=
      .ok (a.data.dmem.storeInt (.ofNat 64 (a.data.regs.rsp.toNat+24)) 8 a.data.regs.r8.toNat,0x20d) := by
    simp only [ChildSetup.entryEffect,stored,beq_iff_eq,parentNonzero,ite_false]
    rfl
  rw [Placement.at_pc a _ pcA]
  apply eventually_trans (instructionStep fetch) _ _ _
    (eventually_flight (ChildSetup.entry_checked fetch decoder entryChecked))
  rintro b ⟨⟨pcB,regsB,memB,frameB,_⟩,mappedB,_⟩
  have readyB : CallsReady c b.data := readyA.frame (by rw [regsB]) frameB mappedB (by
    intro x read written
    rw [stack] at written
    exact res.context x read (zone_locals (by decide) written))
  have here := decoder.add _ _ (show Add.fetch (Add.entry+0x20d)=some _ from rfl)
  rw [Placement.at_pc b _ pcB]
  apply eventually_trans (instructionStep fetch) _ _ _
    (eventually_flight (Services.call fetch (Add.entry+0x20d) "L_ffffffff810f31f0" .pc tracePc here c b.data readyB))
  rintro s2 ⟨⟨pcS,stackS,bxS,bpS,r12S,r13S,r14S,r15S,readyS,frameS⟩,mappedS,_⟩
  rw [regsB] at stackS bxS bpS r12S r13S r14S r15S frameS
  have slotFrame : EqualOutside (Late e.data.regs.rsp c) a.data.dmem b.data.dmem := by
    rw [memB]
    intro x outside
    apply storeInt_frame _ _ _ _ x
    intro inside
    apply outside
    rw [stack,slot_address] at inside
    exact .inr (.inl inside)
  have frameAS : EqualOutside (Late e.data.regs.rsp c) a.data.dmem s2.data.dmem := by
    intro x outside
    refine (slotFrame x outside).trans (frameS x ?_)
    rintro (word|buffer)
    · rw [stack] at word
      exact outside (late_word word)
    · exact outside (.inr (.inr buffer))
  have pendingS := pendingA.frame frameAS
    (fun span member x inside late => res.projection span member x inside (late_after late))
    (fun x inside late => res.table x inside (late_after late))
  have named : (parentId,s2.data.regs.rbx.toNat) ∈ names.trie.nodes := by
    rw [bxS,bx]; exact parentNamed
  have decoded := pendingS.old_node related named hasParent
  have queryS : AllowedipsChild.QueryWords s2.data.dmem e.data.regs.r13.toBitVec e.data.regs.rbp.toNat key :=
    AllowedipsLoop.query_frame fields.family queryA frameAS
      (fun x inside late => res.query x inside (late_after late))
  have savedB : word b.data.dmem "saved.base" (a.data.regs.rsp.toNat+24) 8=.ok base := by
    rw [memB,←allocationNat]
    exact word_store_same _ _ _ _ _ (by rw [stack]; have := res.extent; omega) a.data.regs.r8.toBitVec.isLt
  have savedS : readNat ⟨s2.data,0⟩ (s2.data.regs.rsp.toNat+24) 8=.ok base := by
    rw [stackS]
    apply readNat_of_word
    rw [←Trie.word_frame frameS "saved.base" _ _ _]
    · exact savedB
    · rintro x ⟨i,bound,location⟩ (word|buffer)
      · obtain ⟨j,boundJ,locationJ⟩ := word
        rw [slot_address] at location
        rw [location] at locationJ
        bv_omega
      · apply res.context x (.inr (.inr ⟨buffer.1,.inr buffer.2⟩))
        rw [stack,slot_address] at location
        exact zone_local (offset:=24) (by decide) ⟨i,bound,location⟩
  have topMapped : (s2.data.dmem.loadInt s2.data.regs.rsp.toBitVec 8).isSome=true := by
    rw [stackS,stack]
    have top : (e.data.dmem.loadInt e.data.regs.rsp.toBitVec 8).isSome=true := by
      simpa using res.local_mapped 0 8 (by decide)
    exact mappedS _ _ (mappedB _ _ (mappedA _ _ top))
  have width : e.data.regs.rbp.toNat=(Trie.targetNode parentNode).width := sameWidth
  obtain ⟨child,nonzero,childNamed,selected⟩ := Select.occupied_total (key:=key) decoded
    (by rw [r13S,queryReg,←width]; exact queryS) short occupied savedS topMapped
  have childOld : (downId,child) ∈ names.trie.nodes := by
    have member : (downId,child) ∈ names.trie.nodes++[(names.nextNode,base)] := childNamed
    rcases List.mem_append.mp member with old|new
    · exact old
    · exact absurd (Prod.mk.inj (List.mem_singleton.mp new)).1 downOld
  have pcS' : s2.pc=Add.entry+0x212 := pcS
  rw [Placement.at_pc s2 _ pcS']
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (eventually_flight (Select.effect_segment fetch decoder selected))
  rintro t ⟨⟨pcT,memT,regsT,frameT,_⟩,mappedT,_⟩
  have stackT : t.data.regs.rsp=e.data.regs.rsp := by rw [regsT]; exact stackS.trans stack
  have lateT : EqualOutside (Late e.data.regs.rsp c) a.data.dmem t.data.dmem := by
    intro x outside
    refine (frameAS x outside).trans (frameT x ?_)
    intro top
    rw [stackS,stack] at top
    exact outside (late_top top)
  have allMapped : MappedLe e.data.dmem t.data.dmem :=
    fun address size h => mappedT _ _ (mappedS _ _ (mappedB _ _ (mappedA _ _ h)))
  refine {
    pc := pcT
    stack := stackT
    bx := by rw [regsT]; exact bxS.trans bx
    r12 := by rw [regsT]; exact r12S.trans r12A
    r13 := by rw [regsT]; exact r13S.trans queryReg
    r15 := by rw [regsT]; exact r15S.trans r15A
    bp := by rw [regsT]; exact bpS.trans bpA
    r14 := by rw [regsT]; exact r14S.trans r14A
    r8 := by rw [regsT]
    ready := readyS.frame (by rw [regsT]) frameT mappedT (by
      intro x read top
      rw [stackS,stack] at top
      exact res.context x read (zone_locals (by decide) top))
    late := memA ▸ lateT
    mapped := allMapped
    pending := pendingA.frame lateT
      (fun span member x inside late => res.projection span member x inside (late_after late))
      (fun x inside late => res.table x inside (late_after late))
    query := AllowedipsLoop.query_frame fields.family queryA lateT
      (fun x inside late => res.query x inside (late_after late))
    down := ⟨child,nonzero,childOld,?_⟩ }
  rw [memT,←stack,←stackS]
  have read := MemoryBytes.loadInt_store_subword s2.data.dmem s2.data.regs.rsp.toBitVec 8 (child : Int)
    (by decide) 0 8 (by decide)
  have bound : child<2^64 := by
    have range := ((Trie.reconstruct_fields related.trie).nodeRange _ _ childOld).2
    omega
  have reduce : (child : Int)%18446744073709551616=(child : Int) :=
    Int.emod_eq_of_lt (by omega) (by have h : child<18446744073709551616 := bound; omega)
  simpa [reduce] using read

#print axioms selected_parent
end Binary.Statements.C1.Proof
