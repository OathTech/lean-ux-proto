import AllowedipsPlacementExact

namespace Binary.Pair.Allowedips.Placement
open TrustBase CommonBitsCoverage AllowedipsMutationImage AllowedipsRelation AllowedipsChild
local instance : Labels := Image.linkedLabels

structure ChildInput (base : MachineData) (c : Context) (address : UInt64)
    (bits query cidr : Nat) (next : BitVec 64) : Prop where
  family : bits=32 ∨ bits=128
  short : cidr<bits
  byteIndex : base.dmem.loadInt (address.toBitVec+25) 1=some (byteSelector bits cidr)
  shift : base.dmem.loadInt (address.toBitVec+26) 1=some (7-cidr%8)
  child : base.dmem.loadInt (address.toBitVec+8+.ofNat 64 (8*(query/2^(bits-1-cidr)%2))) 8=some next.toNat
  separate : ∀ a,
    InRange (address.toBitVec+25) 1 a ∨ InRange (address.toBitVec+26) 1 a ∨
      InRange (address.toBitVec+8+.ofNat 64 (8*(query/2^(bits-1-cidr)%2))) 8 a →
      ¬Writes base.regs.rsp c a
  queryWords : QueryWords base.dmem base.regs.r13.toBitVec bits query
  queryApart : ∀ a, InRange base.regs.r13.toBitVec (bits/8) a → ¬Writes base.regs.rsp c a

/-- The child-selector loads follow from the source key arithmetic. The parent
store is interpreted before the query/child reads and framed explicitly. -/
theorem ChildInput.follow {base c address bits query cidr next}
    (input : ChildInput base c address bits query cidr next)
    (fetch : Int64 → Option Decoded) (mutation : AllowedipsMutationDecoderAgreement fetch)
    {s} (frame : Frame base c s) (cursor : s.regs.rbx=address)
    (mapped : (s.dmem.loadInt s.regs.rsp.toBitVec 8).isSome=true) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if next=0 then Add.entry+0x55f else Add.entry+0xf7) ∧
      Frame base c t.data ∧
      t.data.regs.rbx=(if next=0 then address else .ofBitVec next) ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=some (address.toNat : Int))
      ⟨s,Add.entry+0xcf⟩ := by
  have within := (selector_position bits cidr input.family input.short).2
  have ixRead : s.dmem.loadInt (s.regs.rbx.toBitVec+25) 1=some (byteSelector bits cidr) := by
    rw [cursor,←frame.memory.loadInt _ 1 (fun n bound => input.separate _ (.inl ⟨n,bound,rfl⟩))]
    exact input.byteIndex
  have shiftRead : s.dmem.loadInt (s.regs.rbx.toBitVec+26) 1=some (7-cidr%8) := by
    rw [cursor,←frame.memory.loadInt _ 1 (fun n bound => input.separate _ (.inr (.inl ⟨n,bound,rfl⟩)))]
    exact input.shift
  have storedFrame : Frame base c {s with dmem := parentMemory s} := frame.after_parent s.regs.rbx.toBitVec rfl rfl rfl rfl rfl
  have words := AllowedipsLoop.query_frame input.family input.queryWords storedFrame.memory input.queryApart
  have byteRead := queryByte_read (parentMemory s) base.regs.r13.toBitVec bits query (byteSelector bits cidr)
    input.family within words
  have childRead : (parentMemory s).loadInt
      (s.regs.rbx.toBitVec+8+.ofNat 64 (8*selected (queryByte bits query (byteSelector bits cidr)) (7-cidr%8))) 8=some next.toNat := by
    rw [cursor,queryByte_select bits query cidr input.family input.short,
      ←storedFrame.memory.loadInt _ 8 (fun n bound => input.separate _ (.inr (.inr ⟨n,bound,rfl⟩)))]
    exact input.child
  obtain ⟨old,mapped⟩ := Option.isSome_iff_exists.mp mapped
  have executed := child_step s (byteSelector bits cidr) (7-cidr%8)
    (queryByte bits query (byteSelector bits cidr)) next
    (by rcases input.family with h|h <;> omega) (by omega) (queryByte_bound _ _ _) old mapped
    ixRead shiftRead (by change _=some (queryByte bits query (byteSelector bits cidr) : Int); simpa only [frame.key] using byteRead) childRead
  have first := region_eventually (Add_rcf_layout.agreement mutation.add) s _ executed
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro t1 ⟨pc1,memory1,regs1,zf1⟩
  have frame1 := frame.after_parent s.regs.rbx.toBitVec (by simp [regs1]) (by simp [regs1])
    (by simp [regs1]) (by simp [regs1]) memory1
  have parent1 : t1.data.dmem.loadInt base.regs.rsp.toBitVec 8=some (address.toNat : Int) := by
    rw [memory1,←frame.stack]
    simpa only [parentMemory,cursor,UInt64.toNat_toBitVec] using load64_store s.dmem s.regs.rsp.toBitVec address.toBitVec
  have second := region_eventually (Add_ree_layout.agreement mutation.add) t1.data _ (child_guard t1.data)
  rw [at_pc t1 _ pc1]
  apply eventually_trans (instructionStep fetch) _ _ _ second
  rintro t2 ⟨data2,pc2⟩
  by_cases empty : next=0
  · apply Eventually.done
    refine ⟨?_,by simpa only [data2] using frame1,?_,by simpa only [data2] using parent1⟩
    · simpa only [zf1,empty,beq_self_eq_true,ite_true,ite_eq_left empty] using pc2
    · simp only [data2,regs1,ite_eq_left empty,cursor]
  · have pc2' : t2.pc=Add.entry+0xf4 := by simpa only [zf1,beq_iff_eq,ite_eq_right empty] using pc2
    have third := region_eventually (Add_rf4_layout.agreement mutation.add) t2.data _ (child_move t2.data)
    rw [at_pc t2 _ pc2']
    apply eventually_weaken (instructionStep fetch) _ _ _ _ third
    rintro t3 ⟨pc3,regs3,memory3⟩
    refine ⟨by simpa only [ite_eq_right empty] using pc3,?_,?_,?_⟩
    · apply frame1.congr (memory3.trans (congrArg MachineData.dmem data2))
      all_goals simp [regs3,data2]
    · simp only [regs3,data2,regs1,ite_eq_right empty]
    · simpa only [memory3,data2] using parent1

#print axioms ChildInput.follow
end Binary.Pair.Allowedips.Placement
