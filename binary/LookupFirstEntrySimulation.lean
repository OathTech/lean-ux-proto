import LookupEntrySimulation
import LookupFirstStart
namespace Binary.LookupRelation.First
open Leanux TrustBase LookupHistory Callback
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

theorem start_simulation (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (c : Config) (world : World) (s : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (related : R c [⟨s, Image.Lookup.entry⟩] [entryPoint s] ⟨s, Image.Lookup.entry⟩ world)
    (state : LookupCoverage.Context.At coverage preempt s.dmem)
    (phase : preempt = coverage.entryPreempt ∨ preempt = 512+coverage.entryPreempt)
    (stackAligned : s.regs.rsp.toNat % 8 = 0)
    (mapped : ∀ n < 6,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, LookupCoverage.Context.bytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec-48) 48 address)
    (returnSeparate : LookupCoverage.Context.Separated coverage (InRange (s.regs.rsp.toBitVec-48) 8))
    (metadataSeparate : LookupCoverage.Context.Separated coverage (LookupCoverage.Context.metadataBytes coverage))
    (preemptSeparate : LookupCoverage.Context.Separated coverage (InRange preemptCountAddress 4))
    (apart : ∀ v, project c world = some v → ∀ address, Reads c v address →
      ¬Lookup.entryWrites s coverage address) :
    Eventually (guardedHistoryStep fetch (StackGuard s.regs.rsp)) (fun t =>
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
          EqualOutside (Lookup.entryWrites s coverage) s.dmem q.data.dmem)
      ⟨⟨s, Image.Lookup.entry⟩, [⟨s, Image.Lookup.entry⟩]⟩ := by
  have initialObserved := entry_observed c.rxSection s
  have initialRaw : observeHistory (LookupObservation.edge c.rxSection)
      [⟨s, Image.Lookup.entry⟩] = .ok [] := rfl
  obtain ⟨matched, aligned⟩ := entry_correspondence c world s related
  have run := Lookup.First.start_history fetch agree contract s coverage preempt state phase stackAligned
    mapped pushSeparate returnSeparate metadataSeparate preemptSeparate c.rxSection
    [⟨s, Image.Lookup.entry⟩] [] initialRaw rfl
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ _ run
  rintro t ⟨pc, sp, bx, query, out, mask, r15, ready, memory, raw, last, stable, tail, recorded, frames⟩
  have full := LookupObservation.observe_extend_raw c.rxSection
    [⟨s, Image.Lookup.entry⟩] tail [entryPoint s] [] [] initialObserved initialRaw
    (by simpa only [← recorded, List.append_nil] using raw)
  have finalFrame : EqualOutside (Lookup.entryWrites s coverage) s.dmem t.machine.data.dmem :=
    (Lookup.saveMemory_frame s 6 (by decide)).trans memory
  have extension := silent_extension c world ⟨s, Image.Lookup.entry⟩ t.machine
    [⟨s, Image.Lookup.entry⟩] tail [entryPoint s] [sourceEntry world] related initialObserved
    (by simpa using full) (by simpa only [← recorded] using last) matched aligned rfl
    (by rfl) (by rfl) (Lookup.entryWrites s coverage) finalFrame frames apart
  refine ⟨pc, sp, bx, query, out, mask, r15, ready, memory, raw, ?_, ?_⟩
  · simpa only [← recorded, List.append_nil] using full
  · exact ⟨by simpa only [← recorded] using extension.1,
      by simpa only [← recorded] using extension.2.1,
      by simpa only [← recorded] using extension.2.2,
      stable, tail, recorded, frames⟩
theorem header_simulation (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (c : Config) (world : World) (s : MachineData)
    (outside : s.regs.rsp≠outer+8)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (ready : LookupCoverage.CallsReady coverage preempt s)
    (entryCount : preempt = coverage.entryPreempt)
    (table : s.regs.rbx.toBitVec = c.table)
    (query : (s.regs.get (.low .r12 .W32)).toNat = c.query)
    (metadataApart : ∀ a, LookupCoverage.Context.metadataBytes coverage a → ¬InRange preemptCountAddress 4 a)
    (storageApart : LookupBufferNeeded coverage.coverage coverage.entryPreempt coverage.entryView →
      ∀ a, KcovStorageBytes coverage.coverage a → ¬InRange preemptCountAddress 4 a)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a →
      ¬InRange preemptCountAddress 4 a)
    (history : List MachineState) (seen prior : List LookupObservation.Point)
    (sourceHistory : List MirrorHistory.Point)
    (related : R c history seen ⟨s, Image.Lookup.entry+0x19⟩ world)
    (observed : LookupObservation.observe c.rxSection history = .ok seen)
    (raw : observeHistory (LookupObservation.edge c.rxSection) history = .ok prior)
    (matched : LookupObservation.MatchesPoints
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen sourceHistory)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history sourceHistory)
    (latest : sourceHistory.getLast?.map (·.world) = some world)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      t.machine.pc = Image.Lookup.entry+0x2f ∧
      (∃ head, t.machine.data.regs =
        {s.regs with rbx := .ofBitVec head, rax := .ofBitVec ((Lookup.bucketWord s).setWidth 64)}) ∧
      LookupCoverage.CallsReady coverage (512+preempt) t.machine.data ∧
      t.machine.data.dmem.loadInt (c.table + .ofNat 64 (8 * (c.query % 8192))) 8 =
        some (t.machine.data.regs.rbx.toBitVec.toNat : Int) ∧
      EqualOutside (InRange preemptCountAddress 4) s.dmem t.machine.data.dmem ∧
      observeHistory (LookupObservation.edge c.rxSection) t.history = .ok prior ∧
      LookupObservation.observe c.rxSection t.history = .ok seen ∧
      LookupObservation.MatchesPoints
        (ExecutedCorrespondence.AtPoint (R c) c.rxSection t.history) seen sourceHistory ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection t.history sourceHistory ∧
      R c t.history seen t.machine world ∧
      PeerCountPhase.StableExtension history t.history ∧
      ∃ tail, t.history = history ++ tail ∧
        ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
          EqualOutside (InRange preemptCountAddress 4) s.dmem q.data.dmem)
      ⟨⟨s, Image.Lookup.entry+0x19⟩, history⟩ := by
  obtain ⟨v, projected, physical⟩ := related.2.1
  obtain ⟨head, loaded, _⟩ := physical.2.1
  have frame := bh_disabled_frame s preempt
  have headRead : (bhDisabled s preempt).dmem.loadInt
      (c.table + .ofNat 64 (8 * (c.query % 8192))) 8 = some (head.toNat : Int) := by
    rw [← frame.loadInt _ 8 (fun i hi => apart v projected _ (.inl ⟨i, hi, rfl⟩))]
    exact loaded
  have field : (bhDisabled s preempt).dmem.loadInt (Lookup.bucketAddress s) 8 =
      some (head.toNat : Int) := by
    simpa only [bucket_address c s table query] using headRead
  have run := historySteps_eventually fetch 4 _ _
    (bucket_header_history fetch agree s preempt head
      (load32_raw _ _ _ ready.state.2) field history)
  have guarded := history_guard_suffix (guard := StackGuard outer) run related.1 (by
    rintro t ⟨af,machine,recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [bucketStates,List.dropLast_cons_cons,List.dropLast_singleton,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact outside)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
  rintro t ⟨af, machine, recorded⟩
  have last : t.history.getLast? = some t.machine := by
    simp only [recorded, bucketStates, List.getLast?_append, List.getLast?_cons]
    exact congrArg some machine.symm
  have rawFull : observeHistory (LookupObservation.edge c.rxSection) t.history = .ok prior := by
    have joined := observeHistory_splice (LookupObservation.edge c.rxSection)
      history.dropLast ⟨s, Image.Lookup.entry+0x19⟩ (bucketStates s preempt head af)
    rw [history_restore related.1, raw, bucket_header_observed] at joined
    change observeHistory (LookupObservation.edge c.rxSection)
      (history.dropLast ++ ⟨s, Image.Lookup.entry+0x19⟩ :: bucketStates s preempt head af) =
      .ok (prior ++ []) at joined
    rw [recorded, ← history_restore related.1, List.append_assoc]
    simpa only [List.singleton_append, List.append_nil] using joined
  have full := LookupObservation.observe_extend_raw c.rxSection history
    (bucketStates s preempt head af) seen prior [] observed raw
    (by simpa only [← recorded, List.append_nil] using rawFull)
  have finalFrame : EqualOutside (InRange preemptCountAddress 4) s.dmem t.machine.data.dmem := by
    rw [machine]
    exact frame
  have extension := silent_extension c world ⟨s, Image.Lookup.entry+0x19⟩ t.machine
    history (bucketStates s preempt head af) seen sourceHistory related observed
    (by simpa using full) (by simpa only [← recorded] using last)
    matched aligned latest inactive noReturn (InRange preemptCountAddress 4) finalFrame
    (by intro q member _; simpa only [bucketStates_memory s preempt head af q member] using frame)
    apart
  refine ⟨by rw [machine], ⟨head, ?_⟩, ?_, ?_, finalFrame, rawFull, ?_, ?_⟩
  · rw [machine]
    exact header_registers s preempt head af
  · rw [machine]
    exact header_ready s preempt coverage head af
      (bh_ready s preempt coverage ready entryCount metadataApart storageApart)
  · rw [machine, header_registers]
    exact headRead
  · simpa only [← recorded, List.append_nil] using full
  · exact ⟨by simpa only [← recorded] using extension.1,
      by simpa only [← recorded] using extension.2.1,
      by simpa only [← recorded] using extension.2.2,
      (by
        rw [recorded, ← history_restore related.1, List.append_assoc, List.singleton_append]
        apply PeerCountPhase.StableExtension.of_ordinary
        intro q member
        simp only [bucketStates, List.dropLast_cons_cons, List.dropLast_singleton,
          List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;>
          constructor <;> simp [Image.Lookup.entry, Image.PeerGet.entry]),
      bucketStates s preempt head af, recorded,
      by intro q member _; simpa only [bucketStates_memory s preempt head af q member] using frame⟩
#print axioms start_simulation
#print axioms header_simulation
end Binary.LookupRelation.First
