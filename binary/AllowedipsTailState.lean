import AllowedipsEntryExports
import AllowedipsBhHistory
import AllowedipsEpilogue

namespace Binary.AllowedipsTail
open TrustBase CommonBitsCoverage AllowedipsEntry
local instance : Labels := Image.linkedLabels

/-- Physical facts at the return tail. The entry precondition supplies only
its original separations; no future execution or source relation is assumed. -/
structure Ready (initial : MachineState) (coverage : KcovLayout) (old : BitVec 32)
    (ra : UInt64) (s : MachineData) : Prop where
  stack : s.regs.rsp=initial.data.regs.rsp-80
  saved : ∀ i<6, s.dmem.loadInt (Allowedips.entrySlot initial.data i) 8 =
    some (((Allowedips.entryWords initial.data)[i]?.getD 0).toNat : Int)
  returnWord : s.dmem.loadInt initial.data.regs.rsp.toBitVec 8=some ra.toNat
  mappedResult : (s.dmem.loadInt s.regs.rsp.toBitVec 8).isSome=true
  calls : CallsReady ⟨coverage,old+512⟩ s
  before : AllowedipsCoverageAt coverage old s.dmem
  pending : LookupPendingRead old → s.dmem.loadInt softirqPendingAddress 2=some 0

def Writes (initial : MachineState) (coverage : KcovLayout) (old : BitVec 32)
    (a : BitVec 64) : Prop :=
  InRange (slot initial 10) 8 a ∨ InRange (slot initial 11) 8 a ∨
    AllowedipsCoverageWrites coverage old a ∨ InRange preemptCountAddress 4 a

theorem Ready.result_slot {initial coverage old ra s} (r : Ready initial coverage old ra s) :
    s.regs.rsp.toBitVec=slot initial 10 := by rw [r.stack]; rfl

theorem Ready.call_slot {initial coverage old ra s} (r : Ready initial coverage old ra s) :
    s.regs.rsp.toBitVec-8=slot initial 11 := by
  rw [r.stack,UInt64.toBitVec_sub]
  change (initial.data.regs.rsp.toBitVec-80)-8=initial.data.regs.rsp.toBitVec-88
  rw [BitVec.sub_sub]; rfl

theorem saved_apart (initial : MachineState) (i : Nat) (hi : i<6) (n : Nat) (hn : n=10 ∨ n=11)
    (a : BitVec 64) (read : InRange (Allowedips.entrySlot initial.data i) 8 a) :
    ¬InRange (slot initial n) 8 a := by
  rw [saved_slot initial i (by omega),ite_eq_left hi] at read
  exact slot_apart initial (i+1) n (by omega) (by rcases hn with rfl | rfl <;> decide)
    (by rcases hn with rfl | rfl <;> omega) a read

theorem return_apart (initial : MachineState) (n : Nat) (hn : n=10 ∨ n=11)
    (a : BitVec 64) (read : InRange initial.data.regs.rsp.toBitVec 8 a) :
    ¬InRange (slot initial n) 8 a := by
  have read' : InRange (slot initial 0) 8 a := by simpa only [slot,Nat.zero_mul,BitVec.ofNat_eq_ofNat,BitVec.sub_zero] using read
  exact slot_apart initial 0 n (by decide) (by rcases hn with rfl | rfl <;> decide)
    (by rcases hn with rfl | rfl <;> decide) a read'

theorem return_live (initial : MachineState) (a : BitVec 64)
    (read : InRange initial.data.regs.rsp.toBitVec 8 a) : AllowedipsLiveStack initial a := by
  apply slot_live initial 0 (by decide) a
  simpa only [slot,Nat.zero_mul,BitVec.ofNat_eq_ofNat,BitVec.sub_zero] using read

theorem saved_separate {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (i : Nat) (hi : i<6) (a : BitVec 64)
    (read : InRange (Allowedips.entrySlot initial.data i) 8 a) : ¬Writes initial coverage old a := by
  rintro (result | call | buffer | preempt)
  · exact saved_apart initial i hi 10 (.inl rfl) a read result
  · exact saved_apart initial i hi 11 (.inr rfl) a read call
  · exact pre.bufferStack a buffer (saved_live initial i (by omega) a read)
  · exact pre.preemptStack a (saved_live initial i (by omega) a read) preempt

theorem return_separate {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (a : BitVec 64) (read : InRange initial.data.regs.rsp.toBitVec 8 a) : ¬Writes initial coverage old a := by
  rintro (result | call | buffer | preempt)
  · exact return_apart initial 10 (.inl rfl) a read result
  · exact return_apart initial 11 (.inr rfl) a read call
  · exact pre.bufferStack a buffer (return_live initial a read)
  · exact pre.preemptStack a (return_live initial a read) preempt

theorem pending_separate {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v) (needed : LookupPendingRead old)
    (a : BitVec 64) (read : InRange softirqPendingAddress 2 a) : ¬Writes initial coverage old a := by
  have member : AllowedipsMetadata coverage old a := .inr (.inr (.inr (.inr ⟨needed,read⟩)))
  rintro (result | call | buffer | preempt)
  · exact pre.stackServices a (.inl (.inl member)) (slot_writes initial 10 (by decide) (by decide) a result)
  · exact pre.stackServices a (.inl (.inl member)) (slot_writes initial 11 (by decide) (by decide) a call)
  · exact pre.bufferMetadata a buffer member
  · exact pre.preemptServices a (.inl member) preempt

theorem writes_total {initial coverage old a} (written : Writes initial coverage old a) :
    AllowedipsEntry.TotalWrites initial coverage old a := by
  rcases written with result | call | buffer | preempt
  · exact .inl (slot_writes initial 10 (by decide) (by decide) a result)
  · exact .inl (slot_writes initial 11 (by decide) (by decide) a call)
  · exact .inr (.inl buffer)
  · exact .inr (.inr preempt)

#print axioms saved_separate
#print axioms pending_separate
end Binary.AllowedipsTail
