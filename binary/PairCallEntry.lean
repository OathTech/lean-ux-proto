import SourceAdapter
import PairCallRelation
import AllowedipsEntryExports

namespace Binary.Pair.Trie
open Leanux Leanux.WG AllowedipsRelation TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 4096

theorem callEntry_of_facts {names w d root bits key o s c ra}
    (device : w.wg.dev = some d) (related : Corresponds names o s.data.dmem d)
    (heapOk : heap (target d) [d.peerAllowedips.root4,d.peerAllowedips.root6] = .ok ())
    (input : callInput names o s.data.dmem root bits key = .ok ())
    (pc : s.pc = AllowedipsImage.Lookup.entry)
    (rootReg : s.data.regs.rdi.toBitVec = AllowedipsRelation.pointer (interpretation names.nodes) root)
    (bitsReg : s.data.regs.rsi.toNat = bits)
    (facts : CallFacts names o c s ra bits key) :
    AllowedipsEntry (callConfig names w d root bits key) c.coverage c.preempt ra s w
      (callView (callConfig names w d root bits key) d) := by
  let cfg := callConfig names w d root bits key
  let view := callView cfg d
  have dataCover : Covers (decoderSpans names o) (Reads cfg view) := by
    intro a read
    apply decoderSpans_cover
    rcases read with trie | ⟨pid,selected,count⟩
    · exact trieReads_decoded related trie
    · exact .inr (callCount_bytes related selected count)
  have stackCover : Covers (callStack s false) (AllowedipsStackWrites s) := Covers.range _ _
  have liveCover : Covers (callStack s true) (AllowedipsLiveStack s) := Covers.range _ _
  have preemptCover := Covers.range preemptCountAddress 4
  have bufferCover := callBuffers_cover c
  have metadataCover := callMetadata_cover c
  have servicesCover := callServices_cover c
  have inputCover : Covers [(s.data.regs.rdx.toNat,if bits == 32 then 4 else 16)]
      (Allowedips.NetworkReads s.data.regs.rdx.toBitVec bits) := by
    change Covers [(s.data.regs.rdx.toBitVec.toNat,if bits == 32 then 4 else 16)]
      (InRange s.data.regs.rdx.toBitVec (if bits=32 then 4 else 16))
    simpa only [beq_iff_eq] using Covers.range s.data.regs.rdx.toBitVec (if bits=32 then 4 else 16)
  have countCover : Covers (countSpans names o) (AllowedipsCountWrites cfg view) := by
    rintro a ⟨pid,count,selected,_,_,inside⟩
    exact countSpans_cover names o a (callCount_bytes related selected inside)
  have trieCover : Covers (trieSpans names o) (TrieReads cfg.nodes view.nodes cfg.root cfg.bits cfg.key) := by
    intro a read
    exact trieSpans_cover names o a (trieReads_nodeDecoded related read)
  refine {
    pc := pc
    entry := facts.entry
    root := rootReg
    bits := ?_
    projection := by simp [project,device,callView]
    related := callRelated device related heapOk input
    focusNode := rfl
    focusPeer := rfl
    input := facts.input
    stack := facts.stack
    preemptField := facts.coverage.2
    coverageBefore := facts.coverage.1
    coverageDuring := facts.during
    hardirq := facts.hardirq
    pending := facts.pending
    stackData := spansApart_disjoint facts.decoderApart dataCover stackCover.append_left.append_left
    stackInput := spansApart_disjoint facts.queryApart inputCover stackCover.append_left
    stackServices := spansApart_disjoint facts.serviceApart servicesCover stackCover
    bufferData := spansApart_disjoint facts.decoderApart dataCover bufferCover.append_right.append_left
    bufferInput := ?_
    bufferStack := spansApart_disjoint facts.bufferApart bufferCover liveCover.append_left.append_left
    bufferMetadata := spansApart_disjoint facts.bufferApart bufferCover metadataCover.append_right.append_left
    bufferPreempt := spansApart_disjoint facts.bufferApart bufferCover preemptCover.append_right
    countStack := spansApart_disjoint facts.countApart countCover liveCover.append_left.append_left
    countTrie := spansApart_disjoint facts.countApart countCover trieCover.append_right
    countServices := spansApart_disjoint facts.countApart countCover servicesCover.append_right.append_left
    preemptData := spansApart_disjoint facts.decoderApart dataCover preemptCover.append_right
    preemptStack := spansApart_disjoint facts.preemptApart liveCover.append_left.append_left preemptCover
    preemptServices := ?_ }
  · apply BitVec.eq_of_toNat_eq
    simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.drop,BitVec.take,bitsReg,callConfig]
  · exact spansApart_disjoint facts.queryApart inputCover
      (show Covers (writeSpans c) c.writes from fun _ read => writeSpans_cover read).append_right
  · intro a read write
    rcases read with metadata | ⟨needed,storage⟩
    · exact spansApart_disjoint facts.preemptApart metadataCover.append_right.append_left preemptCover a metadata write
    · rcases storage with header | buffer
      · have headerCover : Covers (callHeaders c) (InRange c.coverage.area 8) := by
          unfold callHeaders
          rw [ite_eq_left (show c.Needed ∨ (Context.mk c.coverage (c.preempt+512)).Needed from needed)]
          exact Covers.range _ _
        exact spansApart_disjoint facts.preemptApart headerCover.append_right preemptCover a header write
      · exact spansApart_disjoint facts.bufferApart bufferCover preemptCover.append_right a ⟨needed,buffer⟩ write

/-- Successful runtime entry checks imply the existing physical precondition,
with its source focus and sole pointer interpretation computed internally. -/
theorem callBoundary_pre {names input coverage initial w root bits key ra}
    (checked : callBoundary names input coverage initial w root bits key ra = .ok ()) :
    ∃ d, w.wg.dev = some d ∧
      AllowedipsEntry (callConfig names w d root bits key) coverage.coverage coverage.preempt ra initial w
        (callView (callConfig names w d root bits key) d) ∧
      Corresponds names input.offsets initial.data.dmem d ∧
      CallFacts names input.offsets coverage initial ra bits key := by
  unfold callBoundary at checked
  obtain ⟨_,asserted,checked⟩ := bind_ok checked
  obtain ⟨_,inputOk,checked⟩ := bind_ok checked
  obtain ⟨base,addressOk,checked⟩ := bind_ok checked
  obtain ⟨abi,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨d,device,related,heapOk⟩ := assertAt_ok asserted
  have facts := callFrameCheck_sound checked
  have regs : (initial.pc = AllowedipsImage.Lookup.entry ∧ initial.data.regs.rdi.toNat = base) ∧
      initial.data.regs.rsi.toNat = bits := by simpa only [Bool.and_eq_true,beq_iff_eq] using abi
  exact ⟨d,device,callEntry_of_facts device related heapOk inputOk regs.1.1
    ((u64_of_nat regs.1.2).trans (address_value addressOk).symm) regs.2 facts,related,facts⟩

#print axioms callBoundary_pre

theorem callTotalWrites_cover (s : MachineState) (c : Context) :
    Covers (callStack s false ++ callBuffers c ++ [(preemptCountAddress.toNat,4)])
      (AllowedipsEntry.TotalWrites s c.coverage c.preempt) := by
  intro a read
  rcases read with stack | buffer | preempt
  · exact ((Covers.range (s.data.regs.rsp.toBitVec-144) 144).append_left.append_left) a stack
  · exact (callBuffers_cover c).append_right.append_left a buffer
  · exact (Covers.range preemptCountAddress 4).append_right a preempt

/-- The entry assertion drives actual prologue/endian/BH-disable execution.
The reconstruction at its endpoint is framed from the decoded read set. -/
theorem callEntry_checked (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch)
    (pcContract : AllowedipsTracePcContract fetch) (cmpContract : AllowedipsTraceConstCmp1Contract fetch)
    {names input coverage initial w root bits key ra}
    (checked : callBoundary names input coverage initial w root bits key ra = .ok ()) :
    Eventually (historyStep fetch) (fun t => ∃ d, w.wg.dev = some d ∧
      AllowedipsEntry.Post (callConfig names w d root bits key) initial coverage.coverage coverage.preempt ra t.machine ∧
      Corresponds names input.offsets t.machine.data.dmem d) ⟨initial,[initial]⟩ := by
  obtain ⟨d,device,pre,related,facts⟩ := callBoundary_pre checked
  have apart := spansApart_disjoint facts.decoderApart
    (show Covers (decoderSpans names input.offsets) (ReadBytes names input.offsets) from fun _ read => decoderSpans_cover read)
    (callTotalWrites_cover initial coverage)
  have executed := AllowedipsEntry.execution fetch decoder pcContract cmpContract pre w.netRxSection
  apply eventually_weaken (historyStep fetch) _ _ _ _ executed
  rintro t ⟨post,_⟩
  exact ⟨d,device,post,(reconstruct_frame names input.offsets post.frame apart).symm.trans related⟩

#print axioms callEntry_checked
end Binary.Pair.Trie
