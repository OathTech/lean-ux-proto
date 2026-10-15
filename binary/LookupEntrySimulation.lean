import LookupBucketSimulation
import LookupStartHistory
import LookupBucketFrame

namespace Binary.LookupRelation
open Leanux TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

def entryPoint (s : MachineData) : LookupObservation.Point :=
  LookupObservation.call "wg_index_hashtable_lookup" ⟨s, Image.Lookup.entry⟩

def sourceEntry (world : World) : MirrorHistory.Point :=
  ⟨.call "wg_index_hashtable_lookup", world⟩

theorem entry_observed (rx : Nat) (s : MachineData) :
    LookupObservation.observe rx [⟨s, Image.Lookup.entry⟩] = .ok [entryPoint s] := by
  simp only [LookupObservation.observe, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    observeHistory]
  rfl

/-- Initialize correspondence from the concrete entry relation, not from
    an assumed simulation prefix. There is exactly the actual entry call. -/
theorem entry_correspondence (c : Config) (world : World) (s : MachineData)
    (related : R c [⟨s, Image.Lookup.entry⟩] [entryPoint s] ⟨s, Image.Lookup.entry⟩ world) :
    LookupObservation.MatchesPoints
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection [⟨s, Image.Lookup.entry⟩])
      [entryPoint s] [sourceEntry world] ∧
    ExecutedCorrespondence.CutsAligned (R c) c.rxSection [⟨s, Image.Lookup.entry⟩]
      [sourceEntry world] := by
  have atPoint : ExecutedCorrespondence.AtPoint (R c) c.rxSection
      [⟨s, Image.Lookup.entry⟩] [entryPoint s] ⟨s, Image.Lookup.entry⟩ world := by
    refine ⟨0, [entryPoint s], rfl, ?_, by simp, by simp, by simp, Or.inl rfl, related⟩
    exact entry_observed c.rxSection s
  have matched : LookupObservation.MatchesPoints
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection [⟨s, Image.Lookup.entry⟩])
      [entryPoint s] [sourceEntry world] :=
    .cons ⟨rfl, atPoint, trivial⟩ .nil
  refine ⟨matched, ?_⟩
  intro i current present _
  have bound := (List.getElem?_eq_some_iff.mp present).1
  have zero : i = 0 := by simp only [List.length_singleton] at bound; omega
  subst i
  have eq : current = ⟨s, Image.Lookup.entry⟩ := by simpa using present.symm
  subst current
  refine ⟨[entryPoint s], sourceEntry world, entry_observed c.rxSection s,
    ⟨by simp, ?_⟩, rfl, related⟩
  simpa using matched

theorem entry_R (c : Config) (world : World) (s : MachineData) (v : View)
    (projected : project c world = some v)
    (physical : Physical c [⟨s, Image.Lookup.entry⟩] [entryPoint s]
      ⟨s, Image.Lookup.entry⟩ v)
    (steps : world.steps.toList = c.incomingSteps) (rx : world.netRxSection = c.rxSection) :
    R c [⟨s, Image.Lookup.entry⟩] [entryPoint s] ⟨s, Image.Lookup.entry⟩ world := by
  refine ⟨rfl, ⟨v, projected, physical⟩, ?_, rx⟩
  simpa [entryPoint, LookupObservation.call] using steps

/-- A silent region carries the same source World. The relation at all new
    cuts follows from the executed write footprint, not from a simulation
    premise for the region. -/
theorem silent_extension (c : Config) (world : World) (s t : MachineState)
    (history tail : List MachineState) (seen : List LookupObservation.Point)
    (sourceHistory : List MirrorHistory.Point)
    (related : R c history seen s world)
    (observed : LookupObservation.observe c.rxSection history = .ok seen)
    (full : LookupObservation.observe c.rxSection (history ++ tail) = .ok seen)
    (last : (history ++ tail).getLast? = some t)
    (matched : LookupObservation.MatchesPoints
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen sourceHistory)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history sourceHistory)
    (latest : sourceHistory.getLast?.map (·.world) = some world)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none)
    (writes : Address → Prop)
    (finalFrame : EqualOutside writes s.data.dmem t.data.dmem)
    (frames : ∀ state ∈ tail, state.pc ∈ Image.cutPoints →
      EqualOutside writes s.data.dmem state.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ address, Reads c v address → ¬writes address) :
    LookupObservation.MatchesPoints
      (ExecutedCorrespondence.AtPoint (R c) c.rxSection (history ++ tail)) seen sourceHistory ∧
    ExecutedCorrespondence.CutsAligned (R c) c.rxSection (history ++ tail) sourceHistory ∧
    R c (history ++ tail) seen t world := by
  have emptyTags : DecisionPoints [] := by intro q member; cases member
  have cuts := bucket_cuts c world s history tail seen [] sourceHistory related observed
    (by simpa using full) matched aligned latest emptyTags (by simp) inactive noReturn
    writes frames apart
  have finalR := related.advance_inactive c history (history ++ tail) seen [] s t world
    last emptyTags inactive noReturn writes finalFrame apart
  exact ⟨ExecutedCorrespondence.matched_append_history matched tail,
    by simpa [LookupSearch.decisionWorlds] using cuts,
    by simpa [LookupSearch.advance] using finalR⟩

/-- Prologue and its real callback, initialized at the actual function entry.
    This supporting theorem still uses the callback-state interface; it is not
    a declaration of the function's entry precondition. -/
theorem start_simulation (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch)
    (c : Config) (world : World) (s : MachineData)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (related : R c [⟨s, Image.Lookup.entry⟩] [entryPoint s] ⟨s, Image.Lookup.entry⟩ world)
    (state : KcovState coverage preempt s.dmem)
    (stackAligned : s.regs.rsp.toNat % 8 = 0)
    (mapped : ∀ n < 6,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, KcovStateBytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec-48) 48 address)
    (returnSeparate : KcovSeparated coverage (InRange (s.regs.rsp.toBitVec-48) 8))
    (metadataSeparate : KcovSeparated coverage (KcovMetadataBytes coverage))
    (preemptSeparate : KcovSeparated coverage (InRange preemptCountAddress 4))
    (apart : ∀ v, project c world = some v → ∀ address, Reads c v address →
      ¬Lookup.entryWrites s coverage address) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = Image.Lookup.entry+0x19 ∧
      t.machine.data.regs.rsp = s.regs.rsp-40 ∧ t.machine.data.regs.rbx = s.regs.rdi ∧
      t.machine.data.regs.r12 = UInt64.ofNat (s.regs.get (.low .rdx .W32)).toNat ∧
      t.machine.data.regs.r13 = s.regs.rcx ∧
      t.machine.data.regs.r14 = UInt64.ofNat (s.regs.get (.low .rsi .W32)).toNat ∧
      t.machine.data.regs.r15 = s.regs.r15 ∧
      PeerGet.CallsReady coverage preempt t.machine.data ∧
      EqualOutside (KcovBufferBytes coverage) (Lookup.saveMemory s 6) t.machine.data.dmem ∧
      observeHistory (LookupObservation.edge c.rxSection) t.history = .ok [] ∧
      LookupObservation.observe c.rxSection t.history = .ok [entryPoint s] ∧
      LookupObservation.MatchesPoints
        (ExecutedCorrespondence.AtPoint (R c) c.rxSection t.history)
        [entryPoint s] [sourceEntry world] ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection t.history [sourceEntry world] ∧
      R c t.history [entryPoint s] t.machine world ∧
      ∃ tail, t.history = [⟨s, Image.Lookup.entry⟩] ++ tail ∧
        ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
          EqualOutside (Lookup.entryWrites s coverage) s.dmem q.data.dmem)
      ⟨⟨s, Image.Lookup.entry⟩, [⟨s, Image.Lookup.entry⟩]⟩ := by
  have initialObserved := entry_observed c.rxSection s
  have initialRaw : observeHistory (LookupObservation.edge c.rxSection)
      [⟨s, Image.Lookup.entry⟩] = .ok [] := rfl
  obtain ⟨matched, aligned⟩ := entry_correspondence c world s related
  have run := Lookup.start_history fetch agree contract s coverage preempt state stackAligned
    mapped pushSeparate returnSeparate metadataSeparate preemptSeparate c.rxSection
    [⟨s, Image.Lookup.entry⟩] [] initialRaw rfl
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨pc, sp, bx, query, out, mask, r15, ready, memory, raw, last, tail, recorded, frames⟩
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
      tail, recorded, frames⟩

theorem bucket_address (c : Config) (s : MachineData)
    (table : s.regs.rbx.toBitVec = c.table)
    (query : (s.regs.get (.low .r12 .W32)).toNat = c.query) :
    Lookup.bucketAddress s = c.table + .ofNat 64 (8 * (c.query % 8192)) := by
  have word : s.regs.get (.low .r12 .W32) = .ofNat 32 c.query := by
    simp [← query]
  have mask : (Lookup.bucketWord s).toNat = c.query % 8192 := by
    change (s.regs.get (.low .r12 .W32) &&& 8191#32).toNat = _
    rw [word]
    exact Lookup.mask13 c.query
  simp only [Lookup.bucketAddress, table]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [mask, Nat.mul_comm]

/-- The actual BH-disable store and bucket-head load, composed with the
    silent correspondence invariant. No selected owner/count is changed. -/
theorem header_simulation (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (c : Config) (world : World) (s : MachineData)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : PeerGet.CallsReady coverage preempt s)
    (count : s.dmem.loadInt preemptCountAddress 4 = some (preempt.toNat : Int))
    (table : s.regs.rbx.toBitVec = c.table)
    (query : (s.regs.get (.low .r12 .W32)).toNat = c.query)
    (metadataApart : ∀ a, KcovMetadataBytes coverage a → ¬InRange preemptCountAddress 4 a)
    (storageApart : coverage.mode = 2 ∨ coverage.mode = 3 →
      ∀ a, KcovStorageBytes coverage a → ¬InRange preemptCountAddress 4 a)
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
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = Image.Lookup.entry+0x2f ∧
      (∃ head, t.machine.data.regs =
        {s.regs with rbx := .ofBitVec head, rax := .ofBitVec ((Lookup.bucketWord s).setWidth 64)}) ∧
      PeerGet.CallsReady coverage (512+preempt) t.machine.data ∧
      t.machine.data.dmem.loadInt (c.table + .ofNat 64 (8 * (c.query % 8192))) 8 =
        some (t.machine.data.regs.rbx.toBitVec.toNat : Int) ∧
      EqualOutside (InRange preemptCountAddress 4) s.dmem t.machine.data.dmem ∧
      observeHistory (LookupObservation.edge c.rxSection) t.history = .ok prior ∧
      LookupObservation.observe c.rxSection t.history = .ok seen ∧
      LookupObservation.MatchesPoints
        (ExecutedCorrespondence.AtPoint (R c) c.rxSection t.history) seen sourceHistory ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection t.history sourceHistory ∧
      R c t.history seen t.machine world ∧
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
    (bucket_header_history fetch agree s preempt head count field history)
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
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
      (bh_ready s preempt coverage ready metadataApart storageApart)
  · rw [machine, header_registers]
    exact headRead
  · simpa only [← recorded, List.append_nil] using full
  · exact ⟨by simpa only [← recorded] using extension.1,
      by simpa only [← recorded] using extension.2.1,
      by simpa only [← recorded] using extension.2.2,
      bucketStates s preempt head af, recorded,
      by intro q member _; simpa only [bucketStates_memory s preempt head af q member] using frame⟩

#print axioms bucket_address
#print axioms header_simulation
#print axioms silent_extension
#print axioms start_simulation
#print axioms entry_observed
#print axioms entry_correspondence
#print axioms entry_R
end Binary.LookupRelation
