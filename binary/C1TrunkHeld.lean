import C1TrunkRootBody
import AllowedipsPlacementChecked
/-! Result C1, package 2: the running invariant of `add`'s frame on a
nonempty root. `Live` (from trial T4) fixes `add`'s locals to the prologue's
values; on a nonempty root the image also writes `(%rsp)`, `0x18(%rsp)` and
`0x24(%rsp)`, and the placement loop's helper uses the 40 bytes below the
callee's return word. `Held` is `Live` with those bytes released: the saved
registers, the slot and cidr locals and everything outside the frame are
still the prologue's. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
local instance : Labels := Image.linkedLabels

/-- The bytes of `add`'s frame that change after the prologue on a nonempty
root: the helper's scratch with the callee return word and `(%rsp)` (56
bytes from `rsp-48`), `0x18(%rsp)` and `0x24(%rsp)`. -/
def Locals (a : MachineData) (x : BitVec 64) : Prop :=
  InRange (a.regs.rsp.toBitVec-144) 56 x ∨
  InRange (a.regs.rsp.toBitVec-104+.ofNat 64 32) 8 x ∨
  InRange (a.regs.rsp.toBitVec-104+.ofNat 64 44) 4 x

/-- The whole of `add`'s frame with the helper's scratch below it. -/
def Wide (a : MachineData) : BitVec 64 → Prop := InRange (a.regs.rsp.toBitVec-144) 152

theorem low_base (b : BitVec 64) (off : Nat) :
    b-104+.ofNat 64 off = b-144+.ofNat 64 (40+off) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  congr 1
  show b-104#64 = b-144#64+40#64
  bv_omega

theorem wide_of_window (a : MachineData) (x : BitVec 64) (h : Window a x) : Wide a x := by
  obtain ⟨i,hi,eq⟩ := h
  refine ⟨40+i,by omega,?_⟩
  rw [eq, ← low_base]

theorem wide_sub (a : MachineData) (off n : Nat) (h : off+n ≤ 112) (x : BitVec 64)
    (inside : InRange (a.regs.rsp.toBitVec-104+.ofNat 64 off) n x) : Wide a x :=
  wide_of_window a x (window_sub a off n h x inside)

theorem wide_low (a : MachineData) (n : Nat) (h : n ≤ 152) (x : BitVec 64)
    (inside : InRange (a.regs.rsp.toBitVec-144) n x) : Wide a x := by
  obtain ⟨i,hi,eq⟩ := inside
  exact ⟨i,by omega,eq⟩

theorem wide_of_locals (a : MachineData) (x : BitVec 64) (h : Locals a x) : Wide a x := by
  rcases h with h | h | h
  · exact wide_low a 56 (by decide) x h
  · exact wide_sub a 32 8 (by decide) x h
  · exact wide_sub a 44 4 (by decide) x h

/-- A range of the window that avoids the released bytes. -/
theorem not_locals (a : MachineData) (off n : Nat) (lo : 16 ≤ off) (hi : off+n ≤ 112)
    (clear : off+n ≤ 32 ∨ (40 ≤ off ∧ off+n ≤ 44) ∨ 48 ≤ off) (x : BitVec 64)
    (inside : InRange (a.regs.rsp.toBitVec-104+.ofNat 64 off) n x) : ¬Locals a x := by
  intro h
  rcases h with h | h | h
  · rw [low_base] at inside
    have apart := InRange.offset_disjoint (a.regs.rsp.toBitVec-144) (40+off) n 0 56 (by omega) (by omega)
      (.inr (by omega)) x inside
    exact apart (by simpa using h)
  · exact InRange.offset_disjoint (a.regs.rsp.toBitVec-104) off n 32 8 (by omega) (by omega)
      (by omega) x inside h
  · exact InRange.offset_disjoint (a.regs.rsp.toBitVec-104) off n 44 4 (by omega) (by omega)
      (by omega) x inside h

/-- The callee return word below the frame is among the released bytes. -/
theorem locals_call (a : MachineData) (x : BitVec 64)
    (h : InRange (a.regs.rsp.toBitVec-104) 8 x) : Locals a x := by
  obtain ⟨i,hi,eq⟩ := h
  refine .inl ⟨40+i,by omega,?_⟩
  rw [eq, BitVec.ofNat_add, ← BitVec.add_assoc]
  congr 1
  show a.regs.rsp.toBitVec-104#64 = a.regs.rsp.toBitVec-144#64+40#64
  bv_omega

/-- The loop's write set at `add`'s frame is among the released bytes. -/
theorem locals_scratch (a : MachineData) (sp : UInt64) (stack : sp = a.regs.rsp-96) (x : BitVec 64)
    (h : InRange (sp.toBitVec-48) 56 x) : Locals a x := by
  have base : sp.toBitVec-48 = a.regs.rsp.toBitVec-144 := by
    rw [stack, UInt64.toBitVec_sub]
    show a.regs.rsp.toBitVec-96#64-48#64 = a.regs.rsp.toBitVec-144#64
    bv_omega
  rw [base] at h
  exact .inl h

/-- Invariant of `add`'s frame from the prologue on, on any path. -/
structure Held (c : Context) (a u : MachineData) : Prop where
  ready : CallsReady c u
  stack : u.regs.rsp = a.regs.rsp-96
  cidr12 : u.regs.r12 = .ofBitVec ((a.regs.get (.low .rcx .W32)).setWidth 64)
  key : u.regs.r13 = a.regs.rdx
  frame : EqualOutside (fun x => Locals a x ∨ c.writes x) (memory a 8) u.dmem

theorem Held.ofLive {c : Context} {a u : MachineData} (live : Live c a u) : Held c a u :=
  ⟨live.ready,live.stack,live.cidr12,live.key,fun x outside => live.frame x (fun h => outside
    (h.elim (fun p => .inl (locals_call a x p)) .inr))⟩

/-- Rebuild the invariant after a callback or a memory-preserving region. -/
theorem Held.next {c : Context} {a u t : MachineData} (held : Held c a u)
    (ready : CallsReady c t)
    (sp : t.regs.rsp = u.regs.rsp) (r12 : t.regs.r12 = u.regs.r12) (r13 : t.regs.r13 = u.regs.r13)
    (frame : EqualOutside (fun x => InRange (u.regs.rsp.toBitVec-8) 8 x ∨ c.writes x) u.dmem t.dmem) :
    Held c a t := by
  refine ⟨ready,sp.trans held.stack,r12.trans held.cidr12,r13.trans held.key,?_⟩
  intro x outside
  rw [call_word a u held.stack] at frame
  exact (held.frame x outside).trans (frame x (fun h => outside
    (h.elim (fun p => .inl (locals_call a x p)) .inr)))

theorem Held.quiet {c : Context} {a u t : MachineData} (held : Held c a u)
    (mem : t.dmem = u.dmem)
    (sp : t.regs.rsp = u.regs.rsp) (r12 : t.regs.r12 = u.regs.r12) (r13 : t.regs.r13 = u.regs.r13) :
    Held c a t :=
  held.next (held.ready.congr mem sp) sp r12 r13 (by rw [mem]; exact fun _ _ => rfl)

/-- A coverage call from a held state. -/
theorem Held.call (fetch : Int64 → Option Decoded) (tracePc : TracePcContract fetch)
    {c : Context} {a u : MachineData} (held : Held c a u) (pc : Int64)
    (here : fetch pc = some ⟨callInstruction "L_ffffffff810f31f0",5⟩) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc = pc+5 ∧ Held c a t.data ∧ t.data.regs.rbx = u.regs.rbx ∧ t.data.regs.rbp = u.regs.rbp ∧
      t.data.regs.r14 = u.regs.r14 ∧ t.data.regs.r15 = u.regs.r15) ⟨u,pc⟩ := by
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (Services.call fetch pc "L_ffffffff810f31f0" .pc tracePc here c u held.ready)
  rintro t ⟨pcT,sp,bx,bp,r12,r13,r14,r15,ready,frame⟩
  exact ⟨pcT,held.next ready sp r12 r13 frame,bx,bp,r14,r15⟩

/-- A store into the released bytes of the frame. -/
theorem Held.store {c : Context} {a u t : MachineData} (held : Held c a u)
    (base : BitVec 64) (n : Nat) (v : Int)
    (inside : ∀ x, InRange base n x → Locals a x)
    (mem : t.dmem = u.dmem.storeInt base n v)
    (sp : t.regs.rsp = u.regs.rsp) (r12 : t.regs.r12 = u.regs.r12) (r13 : t.regs.r13 = u.regs.r13)
    (scratch : ∀ x, c.bytes x → ¬Wide a x) :
    Held c a t := by
  have stored := storeInt_frame u.dmem base n v
  refine ⟨⟨?_,by rw [sp]; exact held.ready.aligned,?_,by rw [sp]; exact held.ready.pushSeparate,
    by rw [sp]; exact held.ready.returnSeparate,held.ready.metadataSeparate,held.ready.preemptSeparate⟩,
    sp.trans held.stack,r12.trans held.cidr12,r13.trans held.key,?_⟩
  · rw [mem]
    exact state_frame c u.dmem _ held.ready.state _ stored
      (fun x read h => scratch x read (wide_of_locals a x (inside x h)))
  · rw [mem, sp]
    exact storeInt_defined u.dmem _ _ 8 n v held.ready.mapped
  · rw [mem]
    intro x outside
    exact (held.frame x outside).trans (stored x (fun h => outside (.inl (inside x h))))

/-- A read of the frame that avoids the released bytes sees the prologue's memory. -/
theorem Held.window_load {c : Context} {a u : MachineData} (r : Resources c a) (held : Held c a u)
    (off n : Nat) (lo : 16 ≤ off) (hi : off+n ≤ 112)
    (clear : off+n ≤ 32 ∨ (40 ≤ off ∧ off+n ≤ 44) ∨ 48 ≤ off) :
    u.dmem.loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) n =
      (memory a 8).loadInt (a.regs.rsp.toBitVec-104+.ofNat 64 off) n := by
  refine (held.frame.loadInt _ n (fun i hi' h => ?_)).symm
  rcases h with h | h
  · exact not_locals a off n lo hi clear _ ⟨i,hi',rfl⟩ h
  · exact r.coverageApart _ (writes_bytes h) (window_sub a off n hi _ ⟨i,hi',rfl⟩)

/-- Everything `add` wrote between its entry and a held state. -/
theorem Held.fromEntry {c : Context} {a u : MachineData} (held : Held c a u) :
    EqualOutside (fun x => Wide a x ∨ c.writes x) a.dmem u.dmem := by
  intro x outside
  refine ((memory_frame a 8 (by decide)) x (fun h => outside (.inl ?_))).trans
    (held.frame x (fun h => outside ?_))
  · rw [frame_base] at h
    exact wide_sub a 8 96 (by decide) x h
  · exact h.elim (fun p => .inl (wide_of_locals a x p)) .inr

/-- A read outside the frame, the scratch and the coverage buffer sees entry memory. -/
theorem Held.outside_load {c : Context} {a u : MachineData} (held : Held c a u)
    (base : BitVec 64) (n : Nat)
    (apart : ∀ x, InRange base n x → ¬Wide a x ∧ ¬c.writes x) :
    u.dmem.loadInt base n = a.dmem.loadInt base n :=
  (held.fromEntry.loadInt base n (fun i hi h =>
    h.elim (apart _ ⟨i,hi,rfl⟩).1 (apart _ ⟨i,hi,rfl⟩).2)).symm

/-- The placement loop's frame keeps the invariant. -/
theorem Held.ofFrame {c : Context} {a h t : MachineData} (held : Held c a h)
    (frame : Placement.Frame h c t) : Held c a t := by
  refine ⟨frame.ready,frame.stack.trans held.stack,frame.cidr.trans held.cidr12,
    frame.key.trans held.key,?_⟩
  intro x outside
  refine (held.frame x outside).trans (frame.memory x (fun w => outside ?_))
  exact w.elim (fun p => .inl (locals_scratch a h.regs.rsp held.stack x p)) .inr

#print axioms Held.ofLive
#print axioms Held.call
#print axioms Held.store
#print axioms Held.window_load
#print axioms Held.outside_load
#print axioms Held.ofFrame
end C1Trunk
