import BucketEntry
import LookupLoads
import TrustBase
import StackFrame

namespace Binary.LookupHistory
local instance : Labels := Image.linkedLabels

def bhDisabled (s : MachineData) (count : BitVec 32) : MachineData :=
  let a : BitVec 32 := 512
  let v := a+count
  {s with
    dmem := s.dmem.storeInt TrustBase.preemptCountAddress 4 v.toInt
    status := StatusFlags.from_result v {
      cf := v.unsigned != a.unsigned+count.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned+(count.take 4).unsigned
      of := v.signed != a.signed+count.signed }}

/-- Nested BH-disable counts are admitted. The machine addition is modular;
    admissibility of the later enable path is a separate physical obligation. -/
theorem bh_disable_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData) (count : BitVec 32)
    (field : s.dmem.loadInt TrustBase.preemptCountAddress 4 = some (count.toNat : Int))
    (history : List MachineState) :
    historySteps fetch 1 (fun t => t.machine = ⟨bhDisabled s count, Image.Lookup.entry+0x23⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨s, Image.Lookup.entry+0x19⟩, history⟩ := by
  refine instruction_history fetch _ history
    (fun t => t = ⟨bhDisabled s count, Image.Lookup.entry+0x23⟩) ?_
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+0x19) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.store, MachineData.set, AddrExpr.interp, ConstExpr.interp,
      BitVec.signed,
    BitVec.take, Effects.All, bhDisabled, TrustBase.preemptCountAddress,
    Image.Lookup.entry] at field ⊢
  rw [field]
  simp [Effects.All, BitVec.toInt_eq_toNat_bmod]

def queryCopied (s : MachineData) : MachineData :=
  s.setReg (.low .rax .W32) (s.regs.get (.low .r12 .W32))

def bucketMasked (s : MachineData) (af : Bool) : MachineData :=
  let bits := s.regs.get (.low .rax .W32) &&& (8191#32)
  {s with status := StatusFlags.from_result bits {cf := false, af, of := false}}
    |>.setReg (.low .rax .W32) bits

def headLoaded (s : MachineData) (head : BitVec 64) : MachineData :=
  s.setReg (.low .rbx .W64) head

def headAddress (s : MachineData) : BitVec 64 :=
  s.regs.rbx.toBitVec + s.regs.rax.toBitVec*8

theorem bucket_mask_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (history : List MachineState) :
    historySteps fetch 1 (fun t => ∃ af,
      t.machine = ⟨bucketMasked s af, Image.Lookup.entry+0x2b⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨s, Image.Lookup.entry+0x26⟩, history⟩ := by
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+0x26) = some _ from rfl)
  simp only [historySteps, historyStep, instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.set, ConstExpr.interp, Effects.All, bucketMasked, Image.Lookup.entry]

theorem bucket_head_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData) (head : BitVec 64)
    (field : s.dmem.loadInt (headAddress s) 8 = some (head.toNat : Int))
    (history : List MachineState) :
    historySteps fetch 1 (fun t => t.machine = ⟨headLoaded s head, Image.Lookup.entry+0x2f⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨s, Image.Lookup.entry+0x2b⟩, history⟩ := by
  refine instruction_history fetch _ history
    (fun t => t = ⟨headLoaded s head, Image.Lookup.entry+0x2f⟩) ?_
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+0x2b) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, AddrExpr.interp, ConstExpr.interp,
    Reg64s.get64, BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_add, BitVec.ofInt_mul,
    BitVec.ofInt_toInt, BitVec.take, Effects.All, headAddress, headLoaded] at field ⊢
  rw [field]
  simp [Effects.All]
  rfl

theorem masked_head_address (s : MachineData) (count : BitVec 32) (af : Bool) :
    headAddress (bucketMasked (queryCopied (bhDisabled s count)) af) = Lookup.bucketAddress s := by
  simp [headAddress, bucketMasked, queryCopied, bhDisabled, Lookup.bucketAddress,
    Lookup.bucketWord, MachineData.setReg, Reg64s.get, Reg64s.get64, Reg64s.set,
    Reg64s.set64, Reg.base, Reg.offset, BitVec.drop, BitVec.take]
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

def bucketStates (s : MachineData) (count : BitVec 32) (head : BitVec 64) (af : Bool) :
    List MachineState :=
  [⟨bhDisabled s count, Image.Lookup.entry+0x23⟩,
   ⟨queryCopied (bhDisabled s count), Image.Lookup.entry+0x26⟩,
   ⟨bucketMasked (queryCopied (bhDisabled s count)) af, Image.Lookup.entry+0x2b⟩,
   ⟨headLoaded (bucketMasked (queryCopied (bhDisabled s count)) af) head, Image.Lookup.entry+0x2f⟩]

/-- Header to the first bucket guard, with every actual successor retained.
    The head is read after the BH write; separation later derives that read
    from the incoming all-bucket representation. -/
theorem bucket_header_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (count : BitVec 32) (head : BitVec 64)
    (preempt : s.dmem.loadInt TrustBase.preemptCountAddress 4 = some (count.toNat : Int))
    (field : (bhDisabled s count).dmem.loadInt (Lookup.bucketAddress s) 8 = some (head.toNat : Int))
    (history : List MachineState) :
    historySteps fetch 4 (fun t => ∃ af,
      t.machine = ⟨headLoaded (bucketMasked (queryCopied (bhDisabled s count)) af) head,
        Image.Lookup.entry+0x2f⟩ ∧ t.history = history ++ bucketStates s count head af)
      ⟨⟨s, Image.Lookup.entry+0x19⟩, history⟩ := by
  rw [show 4 = 1+3 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (bh_disable_history fetch agree s count preempt history)
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨bhDisabled s count, Image.Lookup.entry+0x23⟩,
      history ++ [⟨bhDisabled s count, Image.Lookup.entry+0x23⟩]⟩ := by
    cases t; simp_all
  rw [cursor, show 3 = 1+2 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (mov32_history fetch (Image.Lookup.entry+0x23)
    (.low .rax .W32) (.low .r12 .W32) 3 (by decide) (agree _ _ (by rfl)) (bhDisabled s count) _)
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨queryCopied (bhDisabled s count), Image.Lookup.entry+0x26⟩,
      history ++ [⟨bhDisabled s count, Image.Lookup.entry+0x23⟩,
        ⟨queryCopied (bhDisabled s count), Image.Lookup.entry+0x26⟩]⟩ := by
    cases t; simp_all [queryCopied, List.append_assoc, Image.Lookup.entry]
  rw [cursor, show 2 = 1+1 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (bucket_mask_history fetch agree _ _)
  rintro t ⟨af, machine, recorded⟩
  have cursor : t = ⟨⟨bucketMasked (queryCopied (bhDisabled s count)) af, Image.Lookup.entry+0x2b⟩,
      history ++ [⟨bhDisabled s count, Image.Lookup.entry+0x23⟩,
        ⟨queryCopied (bhDisabled s count), Image.Lookup.entry+0x26⟩,
        ⟨bucketMasked (queryCopied (bhDisabled s count)) af, Image.Lookup.entry+0x2b⟩]⟩ := by
    cases t; simp_all [List.append_assoc]
  rw [cursor]
  have read : (bucketMasked (queryCopied (bhDisabled s count)) af).dmem.loadInt
      (headAddress (bucketMasked (queryCopied (bhDisabled s count)) af)) 8 = some (head.toNat : Int) := by
    rw [masked_head_address]
    exact field
  apply historySteps_mono fetch 1 _ _ _ _ (bucket_head_history fetch agree _ head read _)
  rintro t ⟨machine, recorded⟩
  exact ⟨af, machine, by simpa only [machine, bucketStates, List.append_assoc,
    List.cons_append, List.nil_append] using recorded⟩

theorem bucket_header_observed (rxSection : Nat) (s : MachineData)
    (count : BitVec 32) (head : BitVec 64) (af : Bool) :
    observeHistory (LookupObservation.edge rxSection)
      (⟨s, Image.Lookup.entry+0x19⟩ :: bucketStates s count head af) = .ok [] := by
  simp [observeHistory, bucketStates, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]

theorem bucketStates_memory (s : MachineData) (count : BitVec 32) (head : BitVec 64)
    (af : Bool) (q : MachineState) (member : q ∈ bucketStates s count head af) :
    q.data.dmem = (bhDisabled s count).dmem := by
  simp only [bucketStates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

theorem bh_disabled_count (s : MachineData) (count : BitVec 32) :
    (bhDisabled s count).dmem.loadInt TrustBase.preemptCountAddress 4 =
      some (((512#32)+count).toNat : Int) := load32_store _ _ _

theorem bh_disabled_frame (s : MachineData) (count : BitVec 32) :
    EqualOutside (InRange TrustBase.preemptCountAddress 4) s.dmem (bhDisabled s count).dmem :=
  storeInt_frame _ _ _ _

#print axioms bucket_header_history
#print axioms bucket_header_observed
#print axioms bucketStates_memory
#print axioms masked_head_address
#print axioms bh_disabled_count
#print axioms bh_disabled_frame
end Binary.LookupHistory
