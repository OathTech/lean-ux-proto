import SourceAdapter
import PairCallEntry
import PairTrieLoop
import AllowedipsRoot
import SequentialExecution

namespace Binary.Pair.Trie
open Leanux Leanux.WG AllowedipsRelation TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 4096

theorem range_shift_inside (base : BitVec 64) (offset size total : Nat)
    (bound : offset+size ≤ total) {a : BitVec 64}
    (inside : InRange (base+.ofNat 64 offset) size a) : InRange base total a := by
  obtain ⟨i,hi,equal⟩ := inside
  exact ⟨offset+i,by omega,by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal⟩

theorem loopScratch_inside {initial : MachineState} {base : MachineData}
    (stack : base.regs.rsp=initial.data.regs.rsp-80) {a : BitVec 64}
    (inside : InRange (base.regs.rsp.toBitVec-48) 48 a) : AllowedipsStackWrites initial a := by
  have coordinate : base.regs.rsp.toBitVec-48=initial.data.regs.rsp.toBitVec-144+16 := by
    rw [stack,UInt64.toBitVec_sub,BitVec.sub_sub]
    change initial.data.regs.rsp.toBitVec-128=initial.data.regs.rsp.toBitVec-(128+16)+16
    rw [←BitVec.sub_sub,BitVec.sub_add_cancel]
  rw [coordinate] at inside
  exact range_shift_inside _ 16 48 144 (by decide) inside

theorem loopWrites_total {initial : MachineState} {coverage : KcovLayout} {old : BitVec 32} {base : MachineData} {a : BitVec 64}
    (stack : base.regs.rsp=initial.data.regs.rsp-80)
    (write : AllowedipsLoop.writes base.regs.rsp ⟨coverage,old+512⟩ a) :
    AllowedipsEntry.TotalWrites initial coverage old a := by
  rcases write with scratch | buffer
  · exact .inl (loopScratch_inside stack scratch)
  · exact .inr (.inl ⟨.inr buffer.1,buffer.2⟩)

theorem entryPost_loopFrame {cfg coverage old ra initial w v entry}
    (pre : AllowedipsEntry cfg coverage old ra initial w v)
    (post : AllowedipsEntry.Post cfg initial coverage old ra entry) :
    AllowedipsLoop.Frame entry.data ⟨coverage,old+512⟩ entry.data := by
  apply AllowedipsLoop.Frame.initial _ _ post.ready
  · intro n hn
    have coordinate : entry.data.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)=AllowedipsEntry.slot initial (n+11) := by
      rw [post.stack,UInt64.toBitVec_sub,BitVec.sub_sub]
      change initial.data.regs.rsp.toBitVec-(80+.ofNat 64 ((n+1)*8))=initial.data.regs.rsp.toBitVec-.ofNat 64 ((n+11)*8)
      have number : (n+11)*8=80+(n+1)*8 := by omega
      rw [number,BitVec.ofNat_add]
      rfl
    rw [coordinate]
    exact post.mapped (n+10) (by omega)
  · intro a read inside
    exact pre.stackServices a (AllowedipsCoverage.bytes_during coverage old a read) (loopScratch_inside post.stack inside)

theorem query_loop_apart {cfg coverage old ra initial w v entry}
    (pre : AllowedipsEntry cfg coverage old ra initial w v)
    (post : AllowedipsEntry.Post cfg initial coverage old ra entry)
    (family : cfg.bits=32 ∨ cfg.bits=128) :
    ∀ a, InRange (entry.data.regs.rsp.toBitVec+16) (cfg.bits/8) a →
      ¬AllowedipsLoop.writes entry.data.regs.rsp ⟨coverage,old+512⟩ a := by
  intro a read written
  rcases written with scratch | buffer
  · have coordinate : entry.data.regs.rsp.toBitVec+16=(entry.data.regs.rsp.toBitVec-48)+64 := by
      rw [show (64 : BitVec 64)=48+16 from rfl,←BitVec.add_assoc,BitVec.sub_add_cancel]
    rw [coordinate] at read
    have apart := InRange.offset_disjoint (entry.data.regs.rsp.toBitVec-48) 64 (cfg.bits/8) 0 48
      (by rcases family with h | h <;> rw [h] <;> decide) (by decide) (by omega) a read
    exact apart (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using scratch)
  · apply pre.bufferStack a ⟨.inr buffer.1,buffer.2⟩
    apply AllowedipsEntry.query_live initial cfg.bits family
    have coordinate : entry.data.regs.rsp.toBitVec+16=AllowedipsEntry.slot initial 8 := by
      rw [post.stack]
      change initial.data.regs.rsp.toBitVec-80+16=initial.data.regs.rsp.toBitVec-64
      rw [show (80 : BitVec 64)=64+16 from rfl,←BitVec.sub_sub,BitVec.sub_add_cancel]
    exact coordinate ▸ read

theorem root_loop_apart {cfg coverage old ra initial w v entry}
    (pre : AllowedipsEntry cfg coverage old ra initial w v)
    (post : AllowedipsEntry.Post cfg initial coverage old ra entry) :
    ∀ a, InRange (entry.data.regs.rsp.toBitVec+8) 8 a →
      ¬AllowedipsLoop.writes entry.data.regs.rsp ⟨coverage,old+512⟩ a := by
  intro a read written
  rcases written with scratch | buffer
  · have coordinate : entry.data.regs.rsp.toBitVec+8=(entry.data.regs.rsp.toBitVec-48)+56 := by
      rw [show (56 : BitVec 64)=48+8 from rfl,←BitVec.add_assoc,BitVec.sub_add_cancel]
    rw [coordinate] at read
    have apart := InRange.offset_disjoint (entry.data.regs.rsp.toBitVec-48) 56 8 0 48
      (by decide) (by decide) (by decide) a read
    exact apart (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using scratch)
  · apply pre.bufferStack a ⟨.inr buffer.1,buffer.2⟩
    apply AllowedipsEntry.slot_live initial 9 (by decide)
    have coordinate : entry.data.regs.rsp.toBitVec+8=AllowedipsEntry.slot initial 9 := by
      rw [post.stack]
      change initial.data.regs.rsp.toBitVec-80+8=initial.data.regs.rsp.toBitVec-72
      rw [show (80 : BitVec 64)=72+8 from rfl,←BitVec.sub_sub,BitVec.sub_add_cancel]
    exact coordinate ▸ read

/-- The outer root segment exposes endpoint control and its physical frame;
its diagnostic decision history remains internal to the reused lemma. -/
theorem root_segment (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch) (pcContract : AllowedipsTracePcContract fetch)
    {cfg coverage old ra initial w v entry}
    (pre : AllowedipsEntry cfg coverage old ra initial w v)
    (post : AllowedipsEntry.Post cfg initial coverage old ra entry) :
    Eventually (instructionStep fetch) (fun t =>
      t.data.regs.rbx.toBitVec = AllowedipsRelation.pointer cfg.nodes cfg.root ∧
      (if AllowedipsRelation.pointer cfg.nodes cfg.root == 0 then t.pc=AllowedipsImage.Lookup.entry+0x184
        else t.pc=AllowedipsImage.Lookup.entry+0xd5 ∧ t.data.regs.rbp=0) ∧
      AllowedipsLoop.Frame entry.data ⟨coverage,old+512⟩ t.data) entry := by
  have run := AllowedipsOuter.root_start fetch decoder pcContract entry.data entry.data ⟨coverage,old+512⟩
    (AllowedipsRelation.pointer cfg.nodes cfg.root) (post.root pre) (root_loop_apart pre post)
    (entryPost_loopFrame pre post) w.netRxSection [entry] [] rfl (by rw [←post.pc]; rfl)
  have start : (⟨entry.data,AllowedipsImage.Lookup.entry+0x74⟩ : MachineState)=entry := by rw [←post.pc]
  rw [←start]
  apply Sequential.forget run
  rintro t ⟨value,pc,_,trace⟩
  exact ⟨congrArg UInt64.toBitVec value,pc,trace.frame⟩

#print axioms root_segment

/-- The entry supplies the loop's physical setup. No future heap, saved
register value or callback readiness is accepted as a new input. -/
theorem entryPost_loopSetup (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch) (callbacks : CommonBits.Callbacks fetch)
    (cmp1 : AllowedipsTraceCmp1Contract fetch)
    {names} {input : AllowedipsProbe.Input} {coverage initial w d root bits key ra entry}
    (pre : AllowedipsEntry (callConfig names w d root bits key) coverage.coverage coverage.preempt ra initial w
      (callView (callConfig names w d root bits key) d))
    (facts : CallFacts names input.offsets coverage initial ra bits key)
    (post : AllowedipsEntry.Post (callConfig names w d root bits key) initial coverage.coverage coverage.preempt ra entry)
    (related : Corresponds names input.offsets entry.data.dmem d) :
    AllowedipsLoop.Setup fetch entry.data ⟨coverage.coverage,coverage.preempt+512⟩
      (callConfig names w d root bits key) (fun id => d.nodes.get? id) ∧
    (∀ a, ReadBytes names input.offsets a →
      ¬AllowedipsLoop.writes entry.data.regs.rsp ⟨coverage.coverage,coverage.preempt+512⟩ a) := by
  obtain ⟨_,projected,physical⟩ := pre.related.2.1
  have viewEq : project (callConfig names w d root bits key) w =
      some (callView (callConfig names w d root bits key) d) := pre.projection
  have equal := Option.some.inj (projected.symm.trans viewEq)
  subst_vars
  have apartTotal := spansApart_disjoint facts.decoderApart
    (show Covers (decoderSpans names input.offsets) (ReadBytes names input.offsets) from fun _ read => decoderSpans_cover read)
    (callTotalWrites_cover initial coverage)
  have apart : ∀ a, ReadBytes names input.offsets a →
      ¬AllowedipsLoop.writes entry.data.regs.rsp ⟨coverage.coverage,coverage.preempt+512⟩ a := by
    intro a read write
    exact apartTotal a read (loopWrites_total post.stack write)
  have heap := physical.1.frame post.frame (fun a read => by
    rcases read with read
    intro written
    rcases written with stack | buffer | preempt
    · exact pre.stackData a (.inl read) stack
    · exact pre.bufferData a (.inl read) buffer
    · exact pre.preemptData a (.inl read) preempt)
  refine ⟨⟨decoder,callbacks,cmp1,heap,
    fun a read => apart a (trieReads_decoded related read),?_,?_,post.query_current,
    query_loop_apart pre post heap.1⟩,apart⟩
  · simp only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,Width.bits,Nat.sub_zero,BitVec.extractLsb'_eq_self]
    change (entry.data.regs.r12.toBitVec.extractLsb' 0 8).toNat = bits
    rw [post.r12]
    simp only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,Width.bits,Nat.sub_zero,BitVec.extractLsb'_eq_self]
    have low := pre.bits
    simp only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,Width.bits,Nat.sub_zero,BitVec.extractLsb'_eq_self] at low
    change initial.data.regs.rsi.toBitVec.extractLsb' 0 8 = .ofNat 8 bits at low
    change (((initial.data.regs.rsi.toBitVec.extractLsb' 0 32).setWidth 64).extractLsb' 0 8).toNat=bits
    rw [BitVec.extractLsb'_setWidth_of_le (by decide),BitVec.extractLsb'_extractLsb'_of_le (by decide),low]
    rcases heap.1 with h | h <;> change bits = _ at h <;> rw [h] <;> rfl
  · simp only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,Width.bits,Nat.sub_zero,BitVec.extractLsb'_eq_self]
    change entry.data.regs.r13.toBitVec.extractLsb' 0 8 = .ofNat 8 bits
    rw [post.r13]
    change ((BitVec.ofNat 64 bits).extractLsb' 0 8) = .ofNat 8 bits
    rcases heap.1 with h | h <;> change bits = _ at h <;> rw [h] <;> rfl

/-- Search from the post-prologue cut through every accepted source loop.
Empty roots take the compiler's merged miss edge; other calls retain the
same executable reconstruction at the selected-node boundary. -/
theorem search_segment (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch) (callbacks : CommonBits.Callbacks fetch)
    (cmp1 : AllowedipsTraceCmp1Contract fetch)
    {names} {input : AllowedipsProbe.Input} {coverage initial w d root bits key ra entry}
    (pre : AllowedipsEntry (callConfig names w d root bits key) coverage.coverage coverage.preempt ra initial w
      (callView (callConfig names w d root bits key) d))
    (facts : CallFacts names input.offsets coverage initial ra bits key)
    (post : AllowedipsEntry.Post (callConfig names w d root bits key) initial coverage.coverage coverage.preempt ra entry)
    (related : Corresponds names input.offsets entry.data.dmem d)
    (source final : World) (answer : Option NodeId) (device : source.wg.dev = some d)
    (accepted : (Source.findNode root bits key).run source = .ok (answer,final)) :
    Eventually (instructionStep fetch) (fun t =>
      (if root.isNone then answer=none ∧ t.pc=AllowedipsImage.Lookup.entry+0x184 else
        t.pc=AllowedipsImage.Lookup.entry+0x101 ∧
        t.data.regs.rbp.toBitVec = AllowedipsRelation.pointer (interpretation names.nodes) answer) ∧
      Corresponds names input.offsets t.data.dmem d ∧
      AllowedipsLoop.Frame entry.data ⟨coverage.coverage,coverage.preempt+512⟩ t.data) entry := by
  obtain ⟨setup,apart⟩ := entryPost_loopSetup fetch decoder callbacks cmp1 pre facts post related
  have start := root_segment fetch decoder callbacks.pc pre post
  apply eventually_trans (instructionStep fetch) _ _ _ start
  rintro state ⟨cursor,position,frame⟩
  have reconstructed : Corresponds names input.offsets state.data.dmem d :=
    (reconstruct_frame names input.offsets frame.memory apart).symm.trans related
  cases root with
  | none =>
    have selected := (AllowedipsSource.findNode_accepted_select none bits key source final answer accepted).1
    have answerEq : answer = none := by
      have equal : some none = some answer := selected
      exact (Option.some.inj equal).symm
    exact .done _ ⟨⟨answerEq,position⟩,reconstructed,frame⟩
  | some id =>
    obtain ⟨node,_,fields⟩ := setup.heap.2.2 id (.root id rfl)
    have nonnull : interpretation names.nodes id ≠ 0 := fields.1
    have notZero : (interpretation names.nodes id == 0) = false := by
      cases equal : (interpretation names.nodes id == 0) with
      | false => rfl
      | true => exact False.elim (nonnull (eq_of_beq equal))
    have header : state.pc=AllowedipsImage.Lookup.entry+0xd5 ∧ state.data.regs.rbp=0 := by
      change (if interpretation names.nodes id == 0 then state.pc=AllowedipsImage.Lookup.entry+0x184
        else state.pc=AllowedipsImage.Lookup.entry+0xd5 ∧ state.data.regs.rbp=0) at position
      simpa only [notZero,Bool.false_eq_true,↓reduceIte] using position
    have invariant : Invariant names input.offsets d entry.data ⟨coverage.coverage,coverage.preempt+512⟩
        (callConfig names w d (some id) bits key) (none,some id,none) ⟨state,[state]⟩ := by
      refine ⟨⟨?_,header.1,cursor,.root id rfl⟩,frame,reconstructed,⟨[],rfl⟩,rfl⟩
      change state.data.regs.rbp.toBitVec=0
      rw [header.2]
      rfl
    have loop := findNode_effect fetch names input.offsets d entry.data
      ⟨coverage.coverage,coverage.preempt+512⟩ (callConfig names w d (some id) bits key)
      setup related apart source final answer device accepted ⟨state,[state]⟩ invariant
    apply Sequential.forget loop
    rintro t ⟨pc,value,decoded,_,frame⟩
    exact ⟨⟨pc,value⟩,decoded,frame⟩

#print axioms entryPost_loopSetup
#print axioms search_segment
end Binary.Pair.Trie
