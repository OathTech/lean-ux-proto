import C1TrunkRegions
/-! Result C1, package 2 (origin: trial T4, `task/binary-trials:binary-trials/t4`, copied): the running invariant between the prologue and the allocation call. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
local instance : Labels := Image.linkedLabels

/-- The frame's window: the callee return word below the frame, 48 bytes of
locals, six saved registers and the caller's return word (112 bytes). -/
def Window (s0 : MachineData) : BitVec 64 → Prop := InRange (s0.regs.rsp.toBitVec-104) 112

theorem window_sub (s0 : MachineData) (off n : Nat) (h : off+n ≤ 112) (a : BitVec 64)
    (inside : InRange (s0.regs.rsp.toBitVec-104+.ofNat 64 off) n a) : Window s0 a := by
  obtain ⟨i,hi,eq⟩ := inside
  exact ⟨off+i, by omega, by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using eq⟩

theorem frame_base (b : BitVec 64) : b-96 = b-104+.ofNat 64 8 := by
  show b-96#64 = b-104#64+8#64
  bv_omega

theorem slot_base (s0 : MachineData) (i : Nat) (hi : i<8) :
    slot s0 i = s0.regs.rsp.toBitVec-104+.ofNat 64 (8+slotOffset i) := by
  rw [slot_window s0 i hi, frame_base, BitVec.ofNat_add, BitVec.add_assoc]

theorem call_word (s0 s : MachineData) (stack : s.regs.rsp = s0.regs.rsp-96) :
    s.regs.rsp.toBitVec-8 = s0.regs.rsp.toBitVec-104 := by
  rw [stack, UInt64.toBitVec_sub]
  show s0.regs.rsp.toBitVec-96#64-8#64 = s0.regs.rsp.toBitVec-104#64
  bv_omega

theorem writes_bytes {c : Context} {a : BitVec 64} (w : c.writes a) : c.bytes a :=
  .inr (.inr ⟨w.1, .inr w.2⟩)

/-- Entry resources of the stack and the coverage state (no WireGuard content). -/
structure Resources (c : Context) (s0 : MachineData) : Prop where
  coverage : c.At s0.dmem
  aligned : s0.regs.rsp.toNat % 8 = 0
  slots : ∀ i < 8, (s0.dmem.loadInt (slot s0 i) (slotSize i)).isSome = true
  callWord : (s0.dmem.loadInt (s0.regs.rsp.toBitVec-104) 8).isSome = true
  coverageApart : ∀ a, c.bytes a → ¬Window s0 a
  metadataSeparate : ∀ a, c.writes a → ¬c.metadataBytes a
  preemptSeparate : ∀ a, c.writes a → ¬InRange preemptCountAddress 4 a

/-- Invariant from +0x25 to the allocation call: callee-saved registers hold
the arguments, and memory is the prologue's memory up to callback writes. -/
structure Live (c : Context) (s0 s : MachineData) : Prop where
  ready : CallsReady c s
  stack : s.regs.rsp = s0.regs.rsp-96
  bits : s.regs.rbp = .ofBitVec ((s0.regs.get (.low .rsi .W32)).setWidth 64)
  cidr12 : s.regs.r12 = .ofBitVec ((s0.regs.get (.low .rcx .W32)).setWidth 64)
  key : s.regs.r13 = s0.regs.rdx
  peer : s.regs.r14 = s0.regs.r8
  cidr15 : s.regs.r15 = .ofBitVec ((s0.regs.get (.low .rcx .W32)).setWidth 64)
  frame : EqualOutside (fun a => InRange (s0.regs.rsp.toBitVec-104) 8 a ∨ c.writes a)
    (memory s0 8) s.dmem

theorem Live.initial {c : Context} {s0 : MachineData} (r : Resources c s0) (t : MachineData)
    (regs : t.regs = {s0.regs with
        r15 := .ofBitVec ((s0.regs.get (.low .rcx .W32)).setWidth 64),
        r14 := s0.regs.r8, r13 := s0.regs.rdx,
        r12 := .ofBitVec ((s0.regs.get (.low .rcx .W32)).setWidth 64),
        rbp := .ofBitVec ((s0.regs.get (.low .rsi .W32)).setWidth 64),
        rsp := s0.regs.rsp-96})
    (mem : t.dmem = memory s0 8) : Live c s0 t := by
  have stack : t.regs.rsp = s0.regs.rsp-96 := by rw [regs]
  have word := call_word s0 t stack
  refine ⟨⟨?_,?_,?_,?_,?_,r.metadataSeparate,r.preemptSeparate⟩,stack,by rw [regs],by rw [regs],
    by rw [regs],by rw [regs],by rw [regs],by rw [mem]; exact fun _ _ => rfl⟩
  · rw [mem]
    apply state_frame c s0.dmem (memory s0 8) r.coverage _ (memory_frame s0 8 (by decide))
    intro a read inside
    rw [frame_base] at inside
    exact r.coverageApart a read (window_sub s0 8 96 (by decide) a inside)
  · rw [stack]
    have aligned := r.aligned
    have lt := s0.regs.rsp.toNat_lt
    rw [UInt64.toNat_sub]
    have : (96 : UInt64).toNat = 96 := rfl
    omega
  · rw [word, mem]
    exact memory_mapped s0 8 8 _ r.callWord
  · intro a read inside
    rw [word] at inside
    exact r.coverageApart a read (window_sub s0 0 8 (by decide) a (by simpa using inside))
  · intro a written inside
    rw [word] at inside
    exact r.coverageApart a (writes_bytes written) (window_sub s0 0 8 (by decide) a (by simpa using inside))

/-- Rebuild the invariant after a callback or a memory-preserving region. -/
theorem Live.next {c : Context} {s0 s t : MachineData} (live : Live c s0 s)
    (ready : CallsReady c t)
    (sp : t.regs.rsp = s.regs.rsp) (bp : t.regs.rbp = s.regs.rbp)
    (r12 : t.regs.r12 = s.regs.r12) (r13 : t.regs.r13 = s.regs.r13)
    (r14 : t.regs.r14 = s.regs.r14) (r15 : t.regs.r15 = s.regs.r15)
    (frame : EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ c.writes a) s.dmem t.dmem) :
    Live c s0 t := by
  refine ⟨ready,sp.trans live.stack,bp.trans live.bits,r12.trans live.cidr12,r13.trans live.key,
    r14.trans live.peer,r15.trans live.cidr15,?_⟩
  intro a outside
  rw [call_word s0 s live.stack] at frame
  exact (live.frame a outside).trans (frame a outside)

theorem Live.quiet {c : Context} {s0 s t : MachineData} (live : Live c s0 s)
    (mem : t.dmem = s.dmem)
    (sp : t.regs.rsp = s.regs.rsp) (bp : t.regs.rbp = s.regs.rbp)
    (r12 : t.regs.r12 = s.regs.r12) (r13 : t.regs.r13 = s.regs.r13)
    (r14 : t.regs.r14 = s.regs.r14) (r15 : t.regs.r15 = s.regs.r15) : Live c s0 t :=
  live.next (live.ready.congr mem sp) sp bp r12 r13 r14 r15 (by rw [mem]; exact fun _ _ => rfl)

theorem Live.call (fetch : Int64 → Option Decoded) (tracePc : TracePcContract fetch)
    {c : Context} {s0 s : MachineData} (live : Live c s0 s) (pc : Int64)
    (here : fetch pc = some ⟨callInstruction "L_ffffffff810f31f0",5⟩) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc = pc+5 ∧ Live c s0 t.data ∧ t.data.regs.rbx = s.regs.rbx) ⟨s,pc⟩ := by
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (Services.call fetch pc "L_ffffffff810f31f0" .pc tracePc here c s live.ready)
  rintro t ⟨pcT,sp,bx,bp,r12,r13,r14,r15,ready,frame⟩
  exact ⟨pcT,live.next ready sp bp r12 r13 r14 r15 frame,bx⟩

/-- A read that the callbacks cannot have touched sees the prologue's memory. -/
theorem Live.load {c : Context} {s0 s : MachineData} (live : Live c s0 s) (base : BitVec 64) (n : Nat)
    (apart : ∀ a, InRange base n a → ¬InRange (s0.regs.rsp.toBitVec-104) 8 a ∧ ¬c.writes a) :
    s.dmem.loadInt base n = (memory s0 8).loadInt base n :=
  (live.frame.loadInt base n (fun i hi h =>
    h.elim (apart _ ⟨i,hi,rfl⟩).1 (apart _ ⟨i,hi,rfl⟩).2)).symm

theorem Live.window_load {c : Context} {s0 s : MachineData} (r : Resources c s0) (live : Live c s0 s)
    (off n : Nat) (lo : 8 ≤ off) (hi : off+n ≤ 112) :
    s.dmem.loadInt (s0.regs.rsp.toBitVec-104+.ofNat 64 off) n =
      (memory s0 8).loadInt (s0.regs.rsp.toBitVec-104+.ofNat 64 off) n := by
  apply live.load
  intro a inside
  refine ⟨?_,fun w => r.coverageApart a (writes_bytes w) (window_sub s0 off n hi a inside)⟩
  have apart := InRange.offset_disjoint (s0.regs.rsp.toBitVec-104) off n 0 8 (by omega) (by omega)
    (.inr (by omega)) a inside
  simpa using apart

/-- A read outside the whole window and the coverage buffer sees entry memory. -/
theorem Live.outside_load {c : Context} {s0 s : MachineData} (live : Live c s0 s)
    (base : BitVec 64) (n : Nat)
    (apart : ∀ a, InRange base n a → ¬Window s0 a ∧ ¬c.writes a) :
    s.dmem.loadInt base n = s0.dmem.loadInt base n := by
  rw [live.load base n (fun a inside => ⟨fun h =>
    (apart a inside).1 (window_sub s0 0 8 (by decide) a (by simpa using h)),(apart a inside).2⟩)]
  symm
  apply (memory_frame s0 8 (by decide)).loadInt
  intro i hi inside
  rw [frame_base] at inside
  exact (apart _ ⟨i,hi,rfl⟩).1 (window_sub s0 8 96 (by decide) _ inside)

#print axioms Live.initial
#print axioms Live.call
#print axioms Live.window_load
#print axioms Live.outside_load
end C1Trunk
