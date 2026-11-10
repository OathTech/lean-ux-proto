import C1TrunkEntry
import PairMappedMemory
import PairAllowedipsAssert
/-! Result C1, package 2 (origin: trial T4, `task/binary-trials:binary-trials/t4`, copied and trimmed): the common tail from +0x549 (last coverage callback, epilogue, RET),
shared by the success path and the failure paths. Wraps the landed
`Return.finish_checked`. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem readNat_of_load {s : MachineState} {a size n : Nat}
    (load : s.data.dmem.loadInt (.ofNat 64 a) size = some (n : Int)) : readNat s a size = .ok n := by
  obtain ⟨value,read⟩ := readNat_exists (s := s) (address := a) (size := size) (by rw [load]; rfl)
  have again := Trie.readNat_loadInt read
  rw [load] at again
  have equal := Int.ofNat.inj (Option.some.inj again)
  rw [equal]
  exact read

theorem metadata_read {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {span : Pair.Span}
    (member : span ∈ metadataSpans names o) : span ∈ readSpans names o := by
  simp only [metadataSpans,readSpans,List.mem_append] at member ⊢
  rcases member with table | node | peer
  · exact .inl table
  · exact .inr (.inl node)
  · apply Or.inr ∘ Or.inr
    obtain ⟨pair,named,field⟩ := List.mem_flatMap.mp peer
    obtain ⟨slot,present,equal⟩ := List.mem_map.mp field
    exact List.mem_flatMap.mpr ⟨pair,named,List.mem_map.mpr
      ⟨slot,List.mem_cons_of_mem _ present,equal⟩⟩

theorem saved_of_load (w : MachineData) (off : Nat) (x : UInt64)
    (load : w.dmem.loadInt (w.regs.rsp.toBitVec+.ofNat 64 off) 8 = some (x.toNat : Int)) :
    Return.saved w off = .ok x := by
  unfold Return.saved
  have conv : BitVec.ofNat 64 (w.regs.rsp.toBitVec+.ofNat 64 off).toNat =
      w.regs.rsp.toBitVec+.ofNat 64 off := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [readNat_of_load (s := ⟨w,0⟩) (a := (w.regs.rsp.toBitVec+.ofNat 64 off).toNat) (n := x.toNat)
    (by show w.dmem.loadInt (.ofNat 64 _) 8 = _; rw [conv]; exact load)]
  show Except.ok (UInt64.ofNat x.toNat) = Except.ok x
  rw [UInt64.ofNat_toNat]

/-- From +0x549 to the caller: the frame's saved words are the prologue's,
so the epilogue restores the entry registers and returns to `ra`. -/
theorem finish_tail (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    {names : Allowedips.Names} {c : Context} {s0 w : MachineData} {ra : UInt64} {d : Device}
    (r : Resources c s0) (returnWord : s0.dmem.loadInt s0.regs.rsp.toBitVec 8 = some (ra.toNat : Int))
    (readyW : CallsReady c w) (spW : w.regs.rsp = s0.regs.rsp-96)
    (loadW : ∀ off n : Nat, 8 ≤ off → off+n ≤ 112 →
      w.dmem.loadInt (s0.regs.rsp.toBitVec-104+.ofNat 64 off) n =
        (memory s0 8).loadInt (s0.regs.rsp.toBitVec-104+.ofNat 64 off) n)
    (related : Corresponds names Root.nodeOffsets w.dmem d)
    (shape : heap names (target d) w.dmem = .ok ())
    (projection : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ a, span.contains a →
      ¬Window s0 a ∧ ¬c.writes a) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc = .ofBitVec ra.toBitVec ∧
      t.data.regs.rax = .ofBitVec ((w.regs.get (.low .rbx .W32)).setWidth 64) ∧
      t.data.regs.rsp = s0.regs.rsp+8 ∧
      t.data.regs.rbx = s0.regs.rbx ∧ t.data.regs.rbp = s0.regs.rbp ∧
      t.data.regs.r12 = s0.regs.r12 ∧ t.data.regs.r13 = s0.regs.r13 ∧
      t.data.regs.r14 = s0.regs.r14 ∧ t.data.regs.r15 = s0.regs.r15 ∧
      c.At t.data.dmem ∧
      Corresponds names Root.nodeOffsets t.data.dmem d ∧
      heap names (target d) t.data.dmem = .ok () ∧
      EqualOutside (fun a => Window s0 a ∨ c.writes a) w.dmem t.data.dmem)
      ⟨w,Add.entry+0x549⟩ := by
  have wordW := call_word s0 w spW
  have address (off : Nat) : w.regs.rsp.toBitVec+.ofNat 64 off =
      s0.regs.rsp.toBitVec-104+.ofNat 64 (8+off) := by
    rw [spW, UInt64.toBitVec_sub, BitVec.ofNat_add, ← BitVec.add_assoc]
    congr 1
    show s0.regs.rsp.toBitVec-96#64 = s0.regs.rsp.toBitVec-104#64+8#64
    bv_omega
  have savedWord (i : Nat) (hi : i < 6) :
      Return.saved w (88-i*8) = .ok ((words s0)[i]?.getD 0) := by
    apply saved_of_load
    rw [address, loadW _ 8 (by omega) (by omega)]
    have read := memory_read s0 8 i (by decide) (by omega) (by omega)
    rw [slot_base s0 i (by omega)] at read
    have off : slotOffset i = 88-i*8 := by simp only [slotOffset,hi,↓reduceIte]
    rw [off] at read
    exact read
  have h0 : Return.saved w 48 = .ok s0.regs.rbx := savedWord 5 (by decide)
  have h1 : Return.saved w 56 = .ok s0.regs.rbp := savedWord 4 (by decide)
  have h2 : Return.saved w 64 = .ok s0.regs.r12 := savedWord 3 (by decide)
  have h3 : Return.saved w 72 = .ok s0.regs.r13 := savedWord 2 (by decide)
  have h4 : Return.saved w 80 = .ok s0.regs.r14 := savedWord 1 (by decide)
  have h5 : Return.saved w 88 = .ok s0.regs.r15 := savedWord 0 (by decide)
  have h6 : Return.saved w 96 = .ok ra := by
    apply saved_of_load
    rw [address, loadW _ 8 (by decide) (by decide)]
    have top : s0.regs.rsp.toBitVec-104+.ofNat 64 (8+96) = s0.regs.rsp.toBitVec := by
      show s0.regs.rsp.toBitVec-104#64+104#64 = s0.regs.rsp.toBitVec
      bv_omega
    have above : ∀ i < 8, ¬InRange (s0.regs.rsp.toBitVec-96) 96 (s0.regs.rsp.toBitVec+.ofNat 64 i) := by
      intro i ib
      rw [frame_base]
      apply InRange.offset_disjoint (s0.regs.rsp.toBitVec-104) 104 8 8 96 (by decide) (by decide)
        (.inr (by decide))
      exact ⟨i,ib,congrArg (· + BitVec.ofNat 64 i) top.symm⟩
    rw [top, ← (memory_frame s0 8 (by decide)).loadInt _ 8 above]
    exact returnWord
  have effect : Return.addEffect w = .ok ({w.regs with
      rax := .ofBitVec ((w.regs.get (.low .rbx .W32)).setWidth 64),
      rbx := s0.regs.rbx, rbp := s0.regs.rbp, r12 := s0.regs.r12, r13 := s0.regs.r13,
      r14 := s0.regs.r14, r15 := s0.regs.r15, rsp := w.regs.rsp+104},.ofBitVec ra.toBitVec) := by
    unfold Return.addEffect
    rw [h0,h1,h2,h3,h4,h5,h6]
    rfl
  have savedApart : ∀ offset ∈ [48,56,64,72,80,88,96], ∀ a,
      InRange (w.regs.rsp.toBitVec+.ofNat 64 offset) 8 a → ¬Return.Writes w c a := by
    intro offset member a inside written
    have le : offset ≤ 96 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      omega
    rw [address] at inside
    rcases (written : InRange _ 8 a ∨ c.writes a) with p | cw
    · rw [wordW] at p
      exact InRange.offset_disjoint (s0.regs.rsp.toBitVec-104) (8+offset) 8 0 8 (by omega) (by omega)
        (.inr (by omega)) a inside (by simpa using p)
    · exact r.coverageApart a (writes_bytes cw)
        (window_sub s0 (8+offset) 8 (by omega) a inside)
  have projection' : ∀ span ∈ readSpans names Root.nodeOffsets,
      ∀ a, span.contains a → ¬Return.Writes w c a := by
    intro span member a inside written
    obtain ⟨nw,ncw⟩ := projection span member a inside
    rcases (written : InRange _ 8 a ∨ c.writes a) with p | cw
    · rw [wordW] at p
      exact nw (window_sub s0 0 8 (by decide) a (by simpa using p))
    · exact ncw cw
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (Return.finish_checked fetch decoder tracePc c readyW effect savedApart related shape projection')
  rintro t ⟨pcT,obs,cov,frameT,relatedT,shapeT⟩
  simp only [Return.observed,List.cons.injEq,and_true] at obs
  obtain ⟨rax,rsp,rbx,rbp,r12,r13,r14,r15⟩ := obs
  refine ⟨pcT,rax,?_,rbx,rbp,r12,r13,r14,r15,cov,relatedT,shapeT,?_⟩
  · rw [rsp,spW]
    apply UInt64.toBitVec_inj.mp
    show s0.regs.rsp.toBitVec-96#64+104#64 = s0.regs.rsp.toBitVec+8#64
    bv_omega
  · intro a outside
    apply frameT a
    intro h
    rcases (h : InRange _ 8 a ∨ c.writes a) with p | cw
    · rw [wordW] at p
      exact outside (.inl (window_sub s0 0 8 (by decide) a (by simpa using p)))
    · exact outside (.inr cw)

#print axioms finish_tail
end C1Trunk
