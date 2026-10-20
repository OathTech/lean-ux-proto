import AllowedipsCallerState
import AllowedipsEntryExports
import AllowedipsLoopFrame

namespace Binary.AllowedipsCaller
open TrustBase
local instance : Labels := Image.linkedLabels

/-- The peer helper's 64-byte scratch starts at the entry's deepest slot. -/
theorem scratch_entry {c initial coverage old ra base s}
    (entry : AllowedipsEntry.Post c initial coverage old ra base)
    (frame : AllowedipsLoop.Frame base.data ⟨coverage,old+512⟩ s) :
    s.regs.rsp.toBitVec-64=initial.data.regs.rsp.toBitVec-144 := by
  rw [frame.stack,entry.stack,UInt64.toBitVec_sub,BitVec.sub_sub]
  rfl

theorem slot_window (stack : UInt64) (n : Nat) (bound : n<8) :
    stack.toBitVec-.ofNat 64 ((n+1)*8)=stack.toBitVec-64+.ofNat 64 (8*(7-n)) := by
  have number : 64=(n+1)*8+8*(7-n) := by omega
  rw [show (64 : BitVec 64)=.ofNat 64 ((n+1)*8+8*(7-n)) from congrArg (BitVec.ofNat 64) number,BitVec.ofNat_add,
    ←BitVec.sub_sub,BitVec.sub_add_cancel]

/-- Existing entry mapping and loop write frames supply all eight peer-call
slots. The two deeper words are framed, rather than imposed at each call. -/
theorem ready_from_loop {c initial coverage old ra world v base s}
    (pre : TrustBase.AllowedipsEntry c coverage old ra initial world v)
    (entry : AllowedipsEntry.Post c initial coverage old ra base)
    (frame : AllowedipsLoop.Frame base.data ⟨coverage,old+512⟩ s) :
    Ready ⟨coverage,old+512⟩ s := by
  refine ⟨frame.ready,?_,?_⟩
  · intro n hn
    rw [frame.stack]
    by_cases small : n<6
    · exact frame.mapped n small
    · have address : base.data.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)=
          AllowedipsEntry.slot initial (n+11) := by
        rw [entry.stack,UInt64.toBitVec_sub,BitVec.sub_sub]
        unfold AllowedipsEntry.slot
        have num : (n+11)*8=80+(n+1)*8 := by omega
        rw [num,BitVec.ofNat_add]
        rfl
      have mapped : (base.data.dmem.loadInt
          (base.data.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome=true := by
        rw [address]
        exact entry.mapped (n+10) (by omega)
      have read := frame.memory.loadInt
        (base.data.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8 (by
          intro byte byteBound written
          have inside : InRange (base.data.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8
              (base.data.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)+.ofNat 64 byte) := ⟨byte,byteBound,rfl⟩
          rcases written with scratch | buffer
          · have gap : base.data.regs.rsp.toBitVec-48=base.data.regs.rsp.toBitVec-64+.ofNat 64 16 := by
              change _ = base.data.regs.rsp.toBitVec-(48+16)+16
              rw [←BitVec.sub_sub,BitVec.sub_add_cancel]
            rw [slot_window base.data.regs.rsp n hn] at inside
            rw [gap,slot_window base.data.regs.rsp n hn] at scratch
            exact InRange.offset_disjoint _ (8*(7-n)) 8 16 48 (by omega) (by decide)
              (.inl (by omega)) _ inside scratch
          · have live : AllowedipsLiveStack initial
                (base.data.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)+.ofNat 64 byte) := by
              rw [address] at inside ⊢
              exact AllowedipsEntry.slot_live initial (n+11) (by omega) _ inside
            exact pre.bufferStack _ ⟨.inr buffer.1,buffer.2⟩ live)
      rw [←read]
      exact mapped
  · intro a bytes inside
    have service := AllowedipsCoverage.bytes_during coverage old a bytes
    apply pre.stackServices a service
    change InRange (s.regs.rsp.toBitVec-64) 64 a at inside
    rw [scratch_entry entry frame] at inside
    obtain ⟨n,hn,eq⟩ := inside
    exact ⟨n,by omega,eq⟩


theorem loop_writes_subset {c initial coverage old ra base}
    (entry : AllowedipsEntry.Post c initial coverage old ra base) (a : BitVec 64)
    (written : AllowedipsLoop.writes base.data.regs.rsp ⟨coverage,old+512⟩ a) :
    AllowedipsStackWrites initial a ∨ AllowedipsCoverageWrites coverage old a := by
  rcases written with stack | buffer
  · left
    obtain ⟨n,hn,eq⟩ := stack
    rw [entry.stack,UInt64.toBitVec_sub,BitVec.sub_sub] at eq
    have address : initial.data.regs.rsp.toBitVec-80-48=initial.data.regs.rsp.toBitVec-144+16 := by
      change _ = initial.data.regs.rsp.toBitVec-((80+48)+16)+16
      conv => rhs; rw [←BitVec.sub_sub,BitVec.sub_add_cancel]
      rw [BitVec.sub_sub]
    have numeral : (80 : UInt64).toBitVec=(80 : BitVec 64) := rfl
    rw [numeral,←BitVec.sub_sub,address] at eq
    refine ⟨16+n,by omega,?_⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using eq
  · exact .inr ⟨.inr buffer.1,buffer.2⟩

theorem loop_reads {c initial coverage old ra world v base s}
    (pre : TrustBase.AllowedipsEntry c coverage old ra initial world v)
    (entry : AllowedipsEntry.Post c initial coverage old ra base)
    (frame : AllowedipsLoop.Frame base.data ⟨coverage,old+512⟩ s) :
    EqualOutside (fun a => ¬AllowedipsRelation.Reads c v a) initial.data.dmem s.dmem := by
  intro a outside
  have read := Classical.not_not.mp outside
  apply (entry.reads pre a read).trans
  apply frame.memory a
  intro written
  rcases loop_writes_subset entry a written with stack | buffer
  · exact pre.stackData a read stack
  · exact pre.bufferData a read buffer

/-- The focused word is loaded from related entry bytes and retained by the
actual entry/loop frames. Positivity is not a precondition of this lemma. -/
theorem count_from_loop {c initial coverage old ra world v base s}
    (pre : TrustBase.AllowedipsEntry c coverage old ra initial world v)
    (entry : AllowedipsEntry.Post c initial coverage old ra base)
    (frame : AllowedipsLoop.Frame base.data ⟨coverage,old+512⟩ s)
    (pid count : Nat) (focus : c.focus.peer=some pid) (viewCount : v.count=some count) :
    c.peers pid ≠ 0 ∧
    s.dmem.loadInt (c.peers pid+.ofNat 64 Layouts.peer_refcount) 4=some (count : Int) := by
  obtain ⟨u,projected,physical⟩ := pre.related.2.1
  have same : u=v := Option.some.inj (projected.symm.trans pre.projection)
  subst u
  have field := physical.2
  rw [focus] at field
  obtain ⟨actual,actualCount,nonnull,read⟩ := field
  have counts : actual=count := Option.some.inj (actualCount.symm.trans viewCount)
  subst actual
  have phase : LookupRelation.countPhase [initial] [LookupObservation.call "lookup" initial]=none := by
    unfold LookupRelation.countPhase
    simp only [PeerCountPhase.scan]
    split <;> rfl
  rw [phase] at read
  have retained := (loop_reads pre entry frame).loadInt
    (c.peers pid+.ofNat 64 Layouts.peer_refcount) 4 (by
      intro i hi absent
      exact absent (.inr ⟨pid,focus,i,hi,rfl⟩))
  exact ⟨nonnull,retained.symm.trans read⟩

theorem count_separate {c initial coverage old ra world v base s}
    (pre : TrustBase.AllowedipsEntry c coverage old ra initial world v)
    (entry : AllowedipsEntry.Post c initial coverage old ra base)
    (frame : AllowedipsLoop.Frame base.data ⟨coverage,old+512⟩ s)
    (pid count : Nat) (focus : c.focus.peer=some pid) (viewCount : v.count=some count)
    (positive : count≠0) :
    (∀ a, InRange (c.peers pid+.ofNat 64 Layouts.peer_refcount) 4 a → ¬Scratch s a) ∧
    (∀ a, (CommonBitsCoverage.Context.mk coverage (old+512)).bytes a →
      ¬InRange (c.peers pid+.ofNat 64 Layouts.peer_refcount) 4 a) := by
  constructor
  · intro a inside scratch
    apply pre.countStack a ⟨pid,count,focus,viewCount,positive,inside⟩
    change InRange (s.regs.rsp.toBitVec-64) 64 a at scratch
    rw [scratch_entry entry frame] at scratch
    obtain ⟨n,hn,eq⟩ := scratch
    exact ⟨n,by omega,eq⟩
  · intro a bytes inside
    exact pre.countServices a ⟨pid,count,focus,viewCount,positive,inside⟩
      (AllowedipsCoverage.bytes_during coverage old a bytes)

#print axioms count_from_loop
#print axioms count_separate

#print axioms ready_from_loop
end Binary.AllowedipsCaller
