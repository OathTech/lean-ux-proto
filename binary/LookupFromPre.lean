import LookupEntrySimulation
import CutFrames

namespace Binary.LookupRelation
open Leanux TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

/-- The complete existing prologue postcondition, retained for composition. -/
def Started (c : Config) (world : World) (s : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32) (t : Executed) : Prop :=

      t.machine.pc = Image.Lookup.entry+0x19 ∧
      t.machine.data.regs.rsp = s.regs.rsp-40 ∧ t.machine.data.regs.rbx = s.regs.rdi ∧
      t.machine.data.regs.r12 = UInt64.ofNat (s.regs.get (.low .rdx .W32)).toNat ∧
      t.machine.data.regs.r13 = s.regs.rcx ∧
      t.machine.data.regs.r14 = UInt64.ofNat (s.regs.get (.low .rsi .W32)).toNat ∧
      t.machine.data.regs.r15 = s.regs.r15 ∧
      LookupCoverage.CallsReady coverage preempt t.machine.data ∧
      EqualOutside (LookupCoverage.Context.writes coverage) (Lookup.saveMemory s 6) t.machine.data.dmem ∧
      observeHistory (LookupObservation.edge c.rxSection) t.history = .ok [] ∧
      LookupObservation.observe c.rxSection t.history = .ok [entryPoint s] ∧
      LookupObservation.MatchesPoints
        (ExecutedCorrespondence.AtPoint (R c) c.rxSection t.history)
        [entryPoint s] [sourceEntry world] ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection t.history [sourceEntry world] ∧
      R c t.history [entryPoint s] t.machine world ∧
      PeerCountPhase.StableExtension [⟨s, Image.Lookup.entry⟩] t.history ∧
      ∃ tail, t.history = [⟨s, Image.Lookup.entry⟩] ++ tail ∧
        ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
          EqualOutside (Lookup.entryWrites s coverage) s.dmem q.data.dmem

theorem backwards_range (sp : BitVec 64) (small large extra : Nat)
    (bound : small ≤ large) (a : BitVec 64)
    (inside : InRange (sp - .ofNat 64 small) (small+extra) a) :
    InRange (sp - .ofNat 64 large) (large+extra) a := by
  obtain ⟨i, hi, eq⟩ := inside
  have base : sp - .ofNat 64 small = (sp - .ofNat 64 large) + .ofNat 64 (large-small) := by
    have form : BitVec.ofNat 64 large =
        BitVec.ofNat 64 small + BitVec.ofNat 64 (large-small) := by
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    rw [form, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  refine ⟨large-small+i, by omega, ?_⟩
  simpa only [base, BitVec.ofNat_add, BitVec.add_assoc] using eq

/-- Every prologue execution premise is derived from the named physical
    entry declaration. Neither readiness at later calls nor R preservation
    is an additional assumption. -/
theorem start_from_entry (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v) :
    Eventually (historyStep fetch) (Started c world s ⟨coverage, preempt, v⟩ preempt)
      ⟨⟨s, Image.Lookup.entry⟩, [⟨s, Image.Lookup.entry⟩]⟩ := by
  let context : LookupCoverage.Context := ⟨coverage, preempt, v⟩
  have words : 6 ≤ LookupStackWords c := by
    unfold LookupStackWords
    split <;> decide
  have stackSubset (a : BitVec 64) (inside : InRange (s.regs.rsp.toBitVec-48) 48 a) :
      LookupStackWrites c ⟨s, Image.Lookup.entry⟩ a :=
    backwards_range s.regs.rsp.toBitVec 48 (8*LookupStackWords c) 0 (by omega) a inside
  have returnSubset (a : BitVec 64) (inside : InRange (s.regs.rsp.toBitVec-48) 8 a) :
      LookupLiveStack c ⟨s, Image.Lookup.entry⟩ a := by
    apply backwards_range s.regs.rsp.toBitVec 48 (8*LookupStackWords c) 8 (by omega) a
    obtain ⟨i, hi, eq⟩ := inside
    exact ⟨i, by omega, eq⟩
  have related := entry_R c world s v entry.projected entry.physical entry.steps entry.rxSection
  apply start_simulation fetch agree tracePc c world s context preempt related
    ⟨entry.coverageAt, entry.preemptAt⟩ (.inl rfl) entry.frame.1
    (fun i hi => entry.stackMapped i (by omega))
    (fun a read written => entry.serviceStack a read (stackSubset a written))
    (fun a written read => entry.coverageStack a written (returnSubset a read))
    entry.coverageMetadata entry.coveragePreempt
  intro other projected a read written
  have eq : other = v := Option.some.inj (projected.symm.trans entry.projected)
  subst other
  rcases written with stack | buffer
  · exact entry.readsScratch a read (.inl (stackSubset a stack))
  · exact entry.readsScratch a read (.inr (.inl buffer))

/-- Non-vacuous entry declaration to actual executed prologue, for its
    projected view. The witness in LookupWitness is one concrete instance. -/
theorem start_from_pre (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World)
    (entry : Pre_lookup c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world) :
    ∃ v, project c world = some v ∧
      Eventually (historyStep fetch) (Started c world s ⟨coverage, preempt, v⟩ preempt)
        ⟨⟨s, Image.Lookup.entry⟩, [⟨s, Image.Lookup.entry⟩]⟩ := by
  obtain ⟨v, entry⟩ := entry
  exact ⟨v, entry.projected, start_from_entry fetch agree tracePc c coverage preempt returnAddress s world v entry⟩

#print axioms start_from_entry
#print axioms start_from_pre

/-- Entry-derived loop-head state. The saved stack and the untouched source
    world are retained, alongside the correspondence for the actual prefix. -/
structure BeforeBucket (c : Config) (world : World) (s : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32) (t : Executed) : Prop where
  pc : t.machine.pc = Image.Lookup.entry+0x2f
  stack : t.machine.data.regs.rsp = s.regs.rsp-40
  query : (t.machine.data.regs.get (.low .r12 .W32)).toNat = c.query
  output : t.machine.data.regs.r13 = s.regs.rcx
  kinds : KindMask (t.machine.data.regs.get (.low .r14 .W32)) c.kinds
  saved : t.machine.data.regs.r15 = s.regs.r15
  ready : LookupCoverage.CallsReady coverage (512+preempt) t.machine.data
  cursor : t.machine.data.dmem.loadInt (c.table + .ofNat 64 (8*(c.query%8192))) 8 =
    some (t.machine.data.regs.rbx.toBitVec.toNat : Int)
  memory : EqualOutside
    (fun a => coverage.writes a ∨ InRange preemptCountAddress 4 a)
    (Lookup.saveMemory s 6) t.machine.data.dmem
  raw : observeHistory (LookupObservation.edge c.rxSection) t.history = .ok []
  observed : LookupObservation.observe c.rxSection t.history = .ok [entryPoint s]
  matched : LookupObservation.MatchesPoints
    (ExecutedCorrespondence.AtPoint (R c) c.rxSection t.history)
    [entryPoint s] [sourceEntry world]
  aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection t.history [sourceEntry world]
  related : R c t.history [entryPoint s] t.machine world
  stable : PeerCountPhase.StableExtension [⟨s, Image.Lookup.entry⟩] t.history
  frames : CutFrames (fun a => Lookup.entryWrites s coverage a ∨ InRange preemptCountAddress 4 a)
    s.dmem t.history

private theorem low32_ofNat (v : BitVec 32) :
    (UInt64.ofNat v.toNat).toBitVec.extractLsb' 0 32 = v := by
  apply BitVec.eq_of_toNat_eq
  simp
  exact v.isLt

/-- The header's metadata separation, count phase and ABI facts are all
    consequences of the entry declaration and the executed prologue. -/
theorem header_from_started (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (u : Executed) (started : Started c world s ⟨coverage, preempt, v⟩ preempt u) :
    Eventually (historyStep fetch) (BeforeBucket c world s ⟨coverage, preempt, v⟩ preempt) u := by
  obtain ⟨pc, sp, bx, query, out, mask, saved, ready, memory, raw, observed,
    matched, aligned, related, stable, tail⟩ := started
  have table : u.machine.data.regs.rbx.toBitVec = c.table := by rw [bx]; exact entry.table
  have queryReg : (u.machine.data.regs.get (.low .r12 .W32)).toNat = c.query := by
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, Width.bits, Nat.sub_zero, BitVec.extractLsb'_eq_self]
    change (u.machine.data.regs.r12.toBitVec.extractLsb' 0 32).toNat = _
    rw [query, low32_ofNat]
    exact entry.query
  have kindReg : KindMask (u.machine.data.regs.get (.low .r14 .W32)) c.kinds := by
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, Width.bits, Nat.sub_zero, BitVec.extractLsb'_eq_self]
    change KindMask (u.machine.data.regs.r14.toBitVec.extractLsb' 0 32) _
    rw [mask, low32_ofNat]
    exact entry.kinds
  have run := header_simulation fetch agree c world u.machine.data
    ⟨coverage, preempt, v⟩ preempt ready rfl table queryReg
    (fun a h => entry.bhMetadata a (.inl h))
    (fun needed a h => entry.bhMetadata a (.inr ⟨needed,h⟩))
    (by
      intro other projected a read written
      have eq : other = v := Option.some.inj (projected.symm.trans entry.projected)
      subst other
      exact entry.readsScratch a read (.inr (.inr written)))
    u.history [entryPoint s] [] [sourceEntry world]
    (by simpa only [← pc] using related) observed raw matched aligned rfl (by rfl) (by rfl)
  have cursor : (⟨⟨u.machine.data, Image.Lookup.entry+0x19⟩, u.history⟩ : Executed) = u := by
    cases u with | mk machine history => cases machine; simp_all
  rw [cursor] at run
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨pc', ⟨head, regs⟩, ready', loaded, memory', raw', observed',
    matched', aligned', related', stable', suffix, recorded, frames⟩
  refine ⟨pc', by simpa only [regs] using sp,
    by simpa only [regs, Reg64s.get, Reg64s.get64, Reg.base] using queryReg, by simpa only [regs] using out,
    by simpa only [regs, Reg64s.get, Reg64s.get64, Reg.base] using kindReg, by simpa only [regs] using saved,
    ready', loaded, memory.trans memory', raw', observed', matched', aligned', related', stable.trans stable', ?_⟩
  obtain ⟨prefixTail, prefixEq, prefixFrames⟩ := tail
  have old : CutFrames (fun a => Lookup.entryWrites s ⟨coverage, preempt, v⟩ a ∨ InRange preemptCountAddress 4 a) s.dmem u.history := by
    rw [prefixEq]
    exact (CutFrames.initial _ _).append_after (fun _ _ => rfl) prefixFrames (fun _ => Or.inl)
  have endpoint : EqualOutside (fun a => Lookup.entryWrites s ⟨coverage, preempt, v⟩ a ∨ InRange preemptCountAddress 4 a) s.dmem u.machine.data.dmem := by
    intro a outside
    exact (Lookup.saveMemory_frame s 6 (by decide) a (fun inside => outside (.inl (.inl inside)))).trans
      (memory a (fun inside => outside (.inl (.inr inside))))
  rw [recorded]
  exact old.append_after endpoint frames (fun _ => Or.inr)

theorem header_from_pre (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World)
    (entry : Pre_lookup c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world) :
    ∃ v, project c world = some v ∧
      Eventually (historyStep fetch) (BeforeBucket c world s ⟨coverage, preempt, v⟩ preempt)
        ⟨⟨s, Image.Lookup.entry⟩, [⟨s, Image.Lookup.entry⟩]⟩ := by
  obtain ⟨v, entry⟩ := entry
  refine ⟨v, entry.projected, ?_⟩
  apply eventually_trans (historyStep fetch) _ _ _
    (start_from_entry fetch agree tracePc c coverage preempt returnAddress s world v entry)
  exact header_from_started fetch agree c coverage preempt returnAddress s world v entry

#print axioms header_from_started
#print axioms header_from_pre

/-- The complete selected-bucket search, reached from the physical entry.
    The saved loop-head state is retained for the following owner/helper
    segment and its stack frame. -/
def AfterBucket (c : Config) (world : World) (s : MachineData)
    (coverage : KcovLayout) (preempt : BitVec 32) (v : View) (t : Executed) : Prop :=
  ∃ head : Executed, BeforeBucket c world s ⟨coverage, preempt, v⟩ preempt head ∧
    head.history.IsPrefix t.history ∧
    BucketStop c.query c.kinds (cells c v) t.machine ∧
    ScanFrame (bucketExitBase head.machine.data c.query (cells c v))
      ⟨coverage, preempt, v⟩ (512+preempt) t.machine.data ∧
    ∃ delta,
      LookupObservation.observe c.rxSection t.history = .ok ([entryPoint s] ++ delta) ∧
      observeHistory (LookupObservation.edge c.rxSection) t.history = .ok delta ∧
      LookupObservation.MatchesPoints
        (ExecutedCorrespondence.AtPoint (R c) c.rxSection t.history) ([entryPoint s] ++ delta)
        (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).1.2 ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection t.history
        (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).1.2 ∧
      R c t.history ([entryPoint s] ++ delta) t.machine
        (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).2 ∧
      PeerCountPhase.StableExtension head.history t.history ∧ DecisionPoints delta ∧
      ∃ tail, t.history = head.history ++ tail ∧
        CutFrames (scanWrites head.machine.data ⟨coverage, preempt, v⟩) head.machine.data.dmem tail

theorem bucket_from_head (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (traceCmp : TraceCmp4Contract fetch) (traceConstCmp : TraceConstCmp4Contract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (head : Executed) (atHead : BeforeBucket c world s ⟨coverage, preempt, v⟩ preempt head) :
    Eventually (historyStep fetch) (AfterBucket c world s coverage preempt v) head := by
  have apart : ∀ a, Reads c v a → ¬scanWrites head.machine.data ⟨coverage, preempt, v⟩ a := by
    intro a read written
    apply entry.readsScratch a read
    rcases written with stack | buffer
    · apply Or.inl
      have loc : head.machine.data.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-48 := by
        rw [atHead.stack, UInt64.toBitVec_sub, BitVec.sub_sub]
        rfl
      rw [loc] at stack
      have words : 6 ≤ LookupStackWords c := by unfold LookupStackWords; split <;> decide
      apply backwards_range s.regs.rsp.toBitVec 48 (8*LookupStackWords c) 0 (by omega) a
      obtain ⟨i, hi, eq⟩ := stack
      exact ⟨i, by omega, eq⟩
    · exact .inr (.inl buffer)
  have run := bucket_simulation fetch agree tracePc traceCmp traceConstCmp c world v entry.projected
    head.machine.data ⟨coverage, preempt, v⟩ (512+preempt) atHead.ready rfl rfl
    head.history [entryPoint s] [] (by simpa only [← atHead.pc] using atHead.related)
    atHead.observed atHead.raw (by rfl) (by rfl) atHead.query atHead.kinds atHead.cursor apart
    [sourceEntry world] atHead.matched atHead.aligned rfl
  have cursor : (⟨⟨head.machine.data, Image.Lookup.entry+0x2f⟩, head.history⟩ : Executed) = head := by
    rw [← atHead.pc]
  rw [cursor] at run
  have run := LookupObservation.history_prefix fetch _ head head.history ⟨[], by simp⟩ run
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨result, prefixed⟩
  exact ⟨head, atHead, prefixed, by simpa only [List.nil_append, CutFrames] using result⟩

/-- Prologue, BH-disable and the complete bucket loop, including an empty
    bucket, every collision prefix and either kind outcome. All execution
    premises are derived from the witnessed entry declaration. -/
theorem bucket_from_pre (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (traceCmp : TraceCmp4Contract fetch) (traceConstCmp : TraceConstCmp4Contract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World)
    (entry : Pre_lookup c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world) :
    ∃ v, project c world = some v ∧
      Eventually (historyStep fetch) (AfterBucket c world s coverage preempt v)
        ⟨⟨s, Image.Lookup.entry⟩, [⟨s, Image.Lookup.entry⟩]⟩ := by
  obtain ⟨v, entry⟩ := entry
  refine ⟨v, entry.projected, ?_⟩
  apply eventually_trans (historyStep fetch) _ _ _
    (start_from_entry fetch agree tracePc c coverage preempt returnAddress s world v entry)
  intro u started
  apply eventually_trans (historyStep fetch) _ _ _
    (header_from_started fetch agree c coverage preempt returnAddress s world v entry u started)
  exact bucket_from_head fetch agree tracePc traceCmp traceConstCmp c coverage preempt returnAddress
    s world v entry

#print axioms bucket_from_head
#print axioms bucket_from_pre
end Binary.LookupRelation
