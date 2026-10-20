import SourceAdapter
import PairCallHit

namespace Binary.Pair.Trie
open Leanux Leanux.WG TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 4096

theorem after_search_segment (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch) (pc : AllowedipsTracePcContract fetch)
    {names} {input : AllowedipsProbe.Input} {coverage initial entry state w d root bits key ra selected}
    (facts : CallFacts names input.offsets coverage initial ra bits key)
    (post : AllowedipsEntry.Post (callConfig names w d root bits key) initial coverage.coverage coverage.preempt ra entry)
    (related : Corresponds names input.offsets state.data.dmem d)
    (frame : AllowedipsLoop.Frame entry.data ⟨coverage.coverage,coverage.preempt+512⟩ state.data)
    (position : if root.isNone then selected=none ∧ state.pc=AllowedipsImage.Lookup.entry+0x184 else
      state.pc=AllowedipsImage.Lookup.entry+0x101 ∧
      state.data.regs.rbp.toBitVec=AllowedipsRelation.pointer (interpretation names.nodes) selected)
    (present : ∀ id, selected=some id → ∃ node, d.nodes.get? id=some node) :
    Eventually (instructionStep fetch) (fun t =>
      (match selected with
      | none => t.pc=AllowedipsImage.Lookup.entry+0x184
      | some id => t.pc=AllowedipsImage.Lookup.entry+0x110 ∧ t.data.regs.rbp.toBitVec=interpretation names.nodes id) ∧
      Corresponds names input.offsets t.data.dmem d ∧
      AllowedipsLoop.Frame entry.data ⟨coverage.coverage,coverage.preempt+512⟩ t.data) state := by
  have apart := spansApart_disjoint facts.decoderApart
    (show Covers (decoderSpans names input.offsets) (ReadBytes names input.offsets) from fun _ read => decoderSpans_cover read)
    (callTotalWrites_cover initial coverage)
  have entryRelated : Corresponds names input.offsets entry.data.dmem d :=
    (reconstruct_frame names input.offsets frame.memory
      (fun a read write => apart a read (loopWrites_total post.stack write))).trans related
  by_cases empty : root.isNone=true
  · rw [ite_eq_left empty] at position
    rw [position.1]
    exact .done _ ⟨position.2,related,frame⟩
  · rw [ite_eq_right empty] at position
    have run := selected_segment fetch decoder pc position.1 frame
    apply eventually_weaken (instructionStep fetch) _ _ _ _ run
    rintro t ⟨bp,control,nextFrame⟩
    have reconstructed : Corresponds names input.offsets t.data.dmem d :=
      (reconstruct_frame names input.offsets nextFrame.memory
        (fun a read write => apart a read (loopWrites_total post.stack write))).symm.trans entryRelated
    refine ⟨?_,reconstructed,nextFrame⟩
    rw [position.2] at control
    cases selected with
    | none => exact control
    | some id =>
      obtain ⟨node,nodePresent⟩ := present id rfl
      have fields := reconstruct_fields related
      obtain ⟨base,named,_⟩ := fields.node nodePresent
      have bounds := fields.nodeRange id base named
      have nonnull := interpretation_nonnull fields.nodeIds named bounds.1 (by omega)
      refine ⟨?_,by rw [bp]; exact position.2⟩
      simpa only [AllowedipsRelation.pointer,Option.map_some,Option.getD_some,beq_iff_eq,nonnull,↓reduceIte] using control

/-- Complete sequential allowed-IPs lookup. The only data/physical entry
premise is the executable assertion used by both captured and constructed
runners. Decoder and callback behavior remain explicit named hypotheses.
No decision alignment or future-state premise is used. -/
theorem lookup_checked (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch) (peerDecoder : AnchoredDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp1 : AllowedipsTraceCmp1Contract fetch)
    (cmp4 : AllowedipsTraceConstCmp4Contract fetch) (byte : AllowedipsTraceConstCmp1Contract fetch)
    (bh : AllowedipsBhEnableContract fetch)
    {names input coverage initial w root bits key ra answer final}
    (checked : callBoundary names input coverage initial w root bits key ra=.ok ())
    (accepted : (Source.lookup root bits key).run w=.ok (answer,final)) :
    Eventually (instructionStep fetch) (fun t =>
      AllowedipsTail.Post initial coverage.coverage coverage.preempt ra
        (.ofBitVec (AllowedipsRelation.pointer (interpretation names.peers) answer)) t ∧
      (∃ d, final.wg.dev=some d ∧ Corresponds names input.offsets t.data.dmem d) ∧
      EqualOutside (fun a => AllowedipsEntry.TotalWrites initial coverage.coverage coverage.preempt a ∨
        CountBytes names input.offsets a) initial.data.dmem t.data.dmem) initial := by
  obtain ⟨d,device,pre,related,facts⟩ := callBoundary_pre checked
  obtain ⟨source,searched,selected,sourceDevice,sourceRun,selection,effect⟩ := lookup_effect device accepted
  have apart := spansApart_disjoint facts.decoderApart
    (show Covers (decoderSpans names input.offsets) (ReadBytes names input.offsets) from fun _ read => decoderSpans_cover read)
    (callTotalWrites_cover initial coverage)
  have entered := AllowedipsEntry.execution fetch decoder callbacks.pc byte pre 0
  have entryRun := Sequential.forget (Q := fun s => AllowedipsEntry.Post
    (callConfig names w d root bits key) initial coverage.coverage coverage.preempt ra s)
    entered (fun _ h => h.1)
  apply eventually_trans (instructionStep fetch) _ _ _ entryRun
  intro entry post
  have entryRelated : Corresponds names input.offsets entry.data.dmem d :=
    (reconstruct_frame names input.offsets post.frame apart).symm.trans related
  have search := search_segment fetch decoder callbacks cmp1 pre facts post entryRelated
    source searched selected sourceDevice sourceRun
  apply eventually_trans (instructionStep fetch) _ _ _ search
  rintro state ⟨position,searchRelated,frame⟩
  have present : ∀ id, selected=some id → ∃ node, d.nodes.get? id=some node := by
    intro id equal
    rw [equal] at effect
    obtain ⟨node,_,_,nodePresent,_⟩ := effect
    exact ⟨node,nodePresent⟩
  have selectRun := after_search_segment fetch decoder callbacks.pc facts post searchRelated frame position present
  apply eventually_trans (instructionStep fetch) _ _ _ selectRun
  rintro state ⟨position,selectedRelated,frame⟩
  have middleRun : Eventually (instructionStep fetch) (fun t => ∃ d', final.wg.dev=some d' ∧
      MiddlePost names input.offsets d' (callConfig names w d root bits key)
        (callView (callConfig names w d root bits key) d) coverage initial entry answer t) state := by
    cases selected with
    | none =>
      obtain ⟨result,finalDevice⟩ := effect
      subst answer
      have run := miss_segment (v := callView (callConfig names w d root bits key) d) fetch decoder post position frame selectedRelated
      apply eventually_weaken (instructionStep fetch) _ _ _ _ run
      exact fun _ h => ⟨d,finalDevice,h⟩
    | some id =>
      obtain ⟨node,pid,peer,nodePresent,word,peerPresent,result,positive,bound,finalDevice⟩ := effect
      subst answer
      have run := hit_segment fetch decoder peerDecoder callbacks.pc cmp4 byte pre facts post position.1 frame
        selectedRelated selection nodePresent word peerPresent positive bound position.2
      apply eventually_weaken (instructionStep fetch) _ _ _ _ run
      exact fun _ h => ⟨_,finalDevice,h⟩
  apply eventually_trans (instructionStep fetch) _ _ _ middleRun
  rintro state ⟨d',finalDevice,middle⟩
  have tailRun := finish_segment fetch decoder callbacks.pc bh pre facts post middle
  apply eventually_weaken (instructionStep fetch) _ _ _ _ tailRun
  rintro finalState ⟨returned,reconstructed,memory⟩
  refine ⟨returned,⟨d',finalDevice,reconstructed⟩,?_⟩
  intro a outside
  apply (post.frame a (fun written => outside (.inl written))).trans
  apply memory a
  rintro (written | ⟨pid,count,focus,_,_,countRead⟩)
  · exact outside (.inl written)
  · exact outside (.inr (callCount_bytes related focus countRead))

#print axioms lookup_checked

end Binary.Pair.Trie
