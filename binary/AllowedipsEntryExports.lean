import AllowedipsEntryExecution

namespace Binary.AllowedipsEntry
open TrustBase

/-- Rebase the concrete query from entry coordinates to the current stack. -/
theorem Post.query_current {c initial coverage old ra s}
    (post : Post c initial coverage old ra s) :
    AllowedipsChild.QueryWords s.data.dmem (s.data.regs.rsp.toBitVec+16) c.bits c.key := by
  have address : s.data.regs.rsp.toBitVec+16=slot initial 8 := by
    rw [post.stack,UInt64.toBitVec_sub]
    change initial.data.regs.rsp.toBitVec-80+16=initial.data.regs.rsp.toBitVec-64
    rw [show (80 : BitVec 64)=64+16 from rfl,←BitVec.sub_sub,BitVec.sub_add_cancel]
  simpa only [address] using post.query

theorem Post.root {c initial coverage old ra s world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (post : Post c initial coverage old ra s) :
    s.data.dmem.loadInt (s.data.regs.rsp.toBitVec+8) 8 =
      some (AllowedipsRelation.pointer c.nodes c.root).toNat := by
  have address : s.data.regs.rsp.toBitVec+8=Allowedips.entrySlot initial.data 6 := by
    rw [post.stack,UInt64.toBitVec_sub]
    change initial.data.regs.rsp.toBitVec-80+8=initial.data.regs.rsp.toBitVec-72
    rw [show (80 : BitVec 64)=72+8 from rfl,←BitVec.sub_sub,BitVec.sub_add_cancel]
  rw [address]
  have read := post.saved 6 (by decide)
  change s.data.dmem.loadInt (Allowedips.entrySlot initial.data 6) 8=some initial.data.regs.rdi.toNat at read
  simpa only [UInt64.toNat,pre.root] using read

/-- The pending word, read only on the BH-enable guard's reached path,
remains the exact entry value; no unconditional pending read is imposed. -/
theorem Post.pending {c initial coverage old ra s world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (post : Post c initial coverage old ra s) (needed : LookupPendingRead old) :
    s.data.dmem.loadInt softirqPendingAddress 2 = some 0 := by
  have retained := post.frame.loadInt softirqPendingAddress 2 (by
    intro i hi written
    have member : AllowedipsMetadata coverage old (softirqPendingAddress+.ofNat 64 i) :=
      .inr (.inr (.inr (.inr ⟨needed,i,hi,rfl⟩)))
    rcases written with stack | buffer | preempt
    · exact pre.stackServices _ (.inl (.inl member)) stack
    · exact pre.bufferMetadata _ buffer member
    · exact pre.preemptServices _ (.inl member) preempt)
  exact retained.symm.trans (pre.pending needed)

/-- Exact physical bytes of every anchored WireGuard read are retained. The
rest of World remains outside this frame relation. -/
theorem Post.reads {c initial coverage old ra s world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (post : Post c initial coverage old ra s) (a : BitVec 64)
    (read : AllowedipsRelation.Reads c v a) : initial.data.dmem.get? a=s.data.dmem.get? a := by
  apply post.frame a
  rintro (stack | buffer | preempt)
  · exact pre.stackData a read stack
  · exact pre.bufferData a read buffer
  · exact pre.preemptData a read preempt

#print axioms Post.root
#print axioms Post.pending
#print axioms Post.reads
end Binary.AllowedipsEntry
