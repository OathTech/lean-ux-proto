import AllowedipsPlacementChild
import CommonBitsCheckProof
import AllowedipsLoopCalls

namespace Binary.Pair.Allowedips.Placement
open TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels

/-- The six helper scratch words and the placement loop's saved-parent word. -/
def Writes (stack : UInt64) (c : Context) (a : BitVec 64) : Prop :=
  InRange (stack.toBitVec-48) 56 a ∨ c.writes a

structure Frame (base : MachineData) (c : Context) (s : MachineData) : Prop where
  ready : CallsReady c s
  stack : s.regs.rsp=base.regs.rsp
  key : s.regs.r13=base.regs.r13
  cidr : s.regs.r12=base.regs.r12
  bits : s.regs.r15=base.regs.r15
  mapped : ∀ n<6, (s.dmem.loadInt (base.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome=true
  separate : ∀ a, c.bytes a → ¬InRange (base.regs.rsp.toBitVec-48) 56 a
  memory : EqualOutside (Writes base.regs.rsp c) base.dmem s.dmem

theorem scratch_subset {stack : UInt64} {a : BitVec 64}
    (inside : InRange (stack.toBitVec-48) 48 a) : InRange (stack.toBitVec-48) 56 a := by
  obtain ⟨n,bound,atByte⟩ := inside
  exact ⟨n,by omega,atByte⟩

theorem parent_subset {stack : UInt64} {a : BitVec 64}
    (inside : InRange stack.toBitVec 8 a) : InRange (stack.toBitVec-48) 56 a := by
  obtain ⟨n,bound,atByte⟩ := inside
  refine ⟨48+n,by omega,?_⟩
  simpa only [BitVec.ofNat_add,←BitVec.add_assoc,
    show BitVec.ofNat 64 48=(48 : BitVec 64) from rfl,BitVec.sub_add_cancel] using atByte

theorem Frame.initial {base c} (checked : Trie.frameCheck c base=true)
    (separate : spansApart (Trie.readSpans c) [((base.regs.rsp.toBitVec-48).toNat,56)]=true) :
    Frame base c base := by
  have old := Trie.frameCheck_sound checked
  refine ⟨old.ready,rfl,rfl,rfl,rfl,old.mapped,?_,fun _ _ => rfl⟩
  intro a read inside
  obtain ⟨span,member,atSpan⟩ := Trie.readSpans_cover read
  exact spansApart_sound separate member (r := ((base.regs.rsp.toBitVec-48).toNat,56)) (by simp) atSpan
    (by simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using inside)

theorem Frame.congr {base c s t} (frame : Frame base c s)
    (memory : t.dmem=s.dmem) (stack : t.regs.rsp=s.regs.rsp)
    (key : t.regs.r13=s.regs.r13) (cidr : t.regs.r12=s.regs.r12)
    (bits : t.regs.r15=s.regs.r15) : Frame base c t := by
  exact ⟨frame.ready.congr memory stack,stack.trans frame.stack,key.trans frame.key,
    cidr.trans frame.cidr,bits.trans frame.bits,by rw [memory]; exact frame.mapped,
    frame.separate,by rw [memory]; exact frame.memory⟩

/-- Rebuild readiness once from a segment's actual state, mapped scratch and
write frame. Callers need not repeat metadata or save-word bookkeeping. -/
theorem Frame.after {base c s t} (frame : Frame base c s)
    (stack : t.regs.rsp=s.regs.rsp) (key : t.regs.r13=s.regs.r13)
    (cidr : t.regs.r12=s.regs.r12) (bits : t.regs.r15=s.regs.r15)
    (state : c.At t.dmem)
    (mapped : ∀ n<6, (t.dmem.loadInt (base.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome=true)
    (memory : EqualOutside (Writes base.regs.rsp c) s.dmem t.dmem) : Frame base c t := by
  refine ⟨?_,stack.trans frame.stack,key.trans frame.key,cidr.trans frame.cidr,
    bits.trans frame.bits,mapped,frame.separate,fun a outside => (frame.memory a outside).trans (memory a outside)⟩
  refine ⟨state,by rw [stack]; exact frame.ready.aligned,?_,?_,?_,
    frame.ready.metadataSeparate,frame.ready.preemptSeparate⟩
  · rw [stack,frame.stack]
    simpa using mapped 0 (by decide)
  · rw [stack]; exact frame.ready.pushSeparate
  · rw [stack]; exact frame.ready.returnSeparate

/-- A callback only overwrites its own return word; the other five mapped
helper words survive its frame. This is shared by all loop callbacks. -/
theorem Frame.callback_mapped {base c s t} (frame : Frame base c s)
    (stack : t.regs.rsp=s.regs.rsp) (ready : CallsReady c t)
    (memory : EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ c.writes a) s.dmem t.dmem) :
    ∀ n<6, (t.dmem.loadInt (base.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome=true := by
  intro n bound
  by_cases first : n=0
  · subst n
    simpa [stack,frame.stack] using ready.mapped
  · have unchanged := memory.loadInt (base.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8 (by
      intro byte byteBound written
      rcases written with pushed | covered
      · rw [frame.stack] at pushed
        have a := AllowedipsLoop.stack_slot_window base.regs.rsp n bound
        have b := AllowedipsLoop.stack_slot_window base.regs.rsp 0 (by decide)
        change base.regs.rsp.toBitVec-8 = _ at b
        rw [a,b] at pushed
        exact stack_slots_disjoint (base.regs.rsp.toBitVec-48) (5-n) 5
          (by omega) (by omega) (by omega) _ ⟨byte,byteBound,rfl⟩ pushed
      · exact frame.separate _ (.inr (.inr ⟨covered.1,.inr covered.2⟩))
          (scratch_subset (AllowedipsLoop.stack_slot_inside base.regs.rsp n bound _ ⟨byte,byteBound,rfl⟩)))
    rw [←unchanged]
    exact frame.mapped n bound

theorem Frame.after_parent {base c s t} (frame : Frame base c s) (value : BitVec 64)
    (stack : t.regs.rsp=s.regs.rsp) (key : t.regs.r13=s.regs.r13)
    (cidr : t.regs.r12=s.regs.r12) (bits : t.regs.r15=s.regs.r15)
    (memory : t.dmem=s.dmem.storeInt s.regs.rsp.toBitVec 8 value.toInt) : Frame base c t := by
  have stored := storeInt_frame s.dmem s.regs.rsp.toBitVec 8 value.toInt
  apply frame.after stack key cidr bits
  · rw [memory]
    apply state_frame c _ _ frame.ready.state _ stored
    intro a read inside
    rw [frame.stack] at inside
    exact frame.separate a read (parent_subset inside)
  · intro n bound
    rw [memory]
    exact storeInt_defined s.dmem _ _ 8 8 value.toInt (frame.mapped n bound)
  · rw [memory]
    intro a outside
    exact stored a (fun h => outside (.inl (parent_subset (by simpa only [frame.stack] using h))))

/-- Shared physical continuation for the PC and comparison callbacks. -/
theorem Frame.region_callback (fetch : Int64 → Option Decoded) (address returnPC : Int64)
    (kind : KcovKind)
    (contract : AllowedipsServiceReturns fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    {base c s} (frame : Frame base c s) (initial : MachineState) (registers : Reg64s)
    (key : registers.r13=s.regs.r13) (cidr : registers.r12=s.regs.r12)
    (bits : registers.r15=s.regs.r15)
    (region : Eventually (instructionStep fetch) (fun t =>
      t.data.regs={registers with rsp := s.regs.rsp-8} ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt ∧ t.pc=address) initial) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=returnPC ∧ Frame base c t.data ∧ t.data.regs.rbx=registers.rbx ∧
      t.data.regs.rbp=registers.rbp ∧ t.data.regs.r14=registers.r14) initial := by
  have called := CommonBitsCoverage.region_callback fetch address returnPC kind contract c initial s registers frame.ready region
  apply eventually_weaken (instructionStep fetch) _ _ _ _ called
  rintro t ⟨pc,sp,bx,bp,r12,r13,r14,r15,ready,written⟩
  refine ⟨pc,?_,bx,bp,r14⟩
  apply frame.after sp (r13.trans key) (r12.trans cidr) (r15.trans bits) ready.state
    (frame.callback_mapped sp ready written)
  intro a outside
  apply written a
  intro h
  have within := AllowedipsLoop.callback_subset s.regs.rsp c a h
  rw [frame.stack] at within
  rcases within with scratch | buffer
  · exact outside (.inl (scratch_subset scratch))
  · exact outside (.inr buffer)

#print axioms Frame.after
#print axioms Frame.callback_mapped
#print axioms Frame.after_parent
#print axioms Frame.region_callback
end Binary.Pair.Allowedips.Placement
