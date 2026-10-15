import LookupAdequacy

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupObservation
local instance : Labels := Image.linkedLabels

/-- Extend the interpreted observations by a frame, without extending R or
    constraining lookup's entry. The source observer and its representation
    are parameters of the frame rule, not additional execution contracts. -/
def FramedLookupRun {α : Type} (c : Config) (observer : World → α)
    (represents : Mem 64 → α → Prop) (final : Executed)
    (run : MirrorHistory.Run (Option (IndexOwner × PeerId))) : Prop :=
  RealizesLookupRun c final run ∧
  represents final.machine.data.dmem (observer run.finalWorld) ∧
  ∀ i current, final.history[i]? = some current → current.pc ∈ Image.cutPoints →
    ∃ events last,
      observe c.rxSection (final.history.take (i+1)) = .ok events ∧
      PrefixMatches (ExecutedCorrespondence.AtPoint (R c) c.rxSection (final.history.take (i+1)))
        events run.points ∧
      (run.points.take events.length).getLast? = some last ∧
      R c (final.history.take (i+1)) events current last.world ∧
      represents current.data.dmem (observer last.world)

/-- Every interpretation insensitive to the actual write footprint holds
    at all anchored cuts. No assertion about arbitrary service interiors is
    made by their endpoint contracts. -/
theorem LookupPost.frame_cuts (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (ra : UInt64)
    (initial : MachineState) (world : World) (answer : Option (IndexOwner × PeerId))
    (finalWorld : World) (final : Executed)
    (post : LookupPost c coverage preempt ra initial world answer finalWorld final)
    (F : Mem 64 → Prop) (initialFrame : F initial.data.dmem)
    (stable : ∀ v, LookupEntry c coverage preempt ra initial world v →
      ∀ before after, EqualOutside (LookupWrites c coverage preempt initial.data v) before after → F before → F after) :
    ∀ current ∈ final.history, current.pc ∈ Image.cutPoints → F current.data.dmem := by
  obtain ⟨_, _, v, _, _, entry, _, _, _, _, _, _, frames⟩ := post
  intro current member cut
  exact stable v entry _ _ (frames current member cut) initialFrame

/-- Generic transport with untouched observations carried by a frame rule.
    A source-side invariant is a theorem about accepted runs, just like P;
    the physical premise supplies the initial meaning of that observation.
    Neither is silently assumed by Pre_lookup or by minimal R. -/
theorem lookup_framed_transport {α : Type} (fetch : Int64 → Option Decoded)
    (decoder : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp4 : TraceCmp4Contract fetch)
    (traceConstCmp4 : TraceConstCmp4Contract fetch) (traceConstCmp1 : TraceConstCmp1Contract fetch)
    (bhEnable : BhEnableContract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (initial : MachineState) (world : World)
    (pre : Pre_lookup c coverage preempt returnAddress initial world)
    (answer : Option (IndexOwner × PeerId)) (finalWorld : World)
    (accepted : (indexLookup c.kinds c.query).run world = .ok (answer, finalWorld))
    (P : MirrorHistory.Run (Option (IndexOwner × PeerId)) → Prop)
    (property : ∀ run, MirrorHistory.Accepted (MirrorHistory.lookup c.kinds c.query) world run → P run)
    (observer : World → α) (represents : Mem 64 → α → Prop)
    (initialFrame : represents initial.data.dmem (observer world))
    (frameRule : ∀ v, LookupEntry c coverage preempt returnAddress initial world v →
      ∀ before after, EqualOutside (LookupWrites c coverage preempt initial.data v) before after →
        represents before (observer world) → represents after (observer world))
    (sourceFrame : ∀ run, MirrorHistory.Accepted (MirrorHistory.lookup c.kinds c.query) world run →
      observer run.finalWorld = observer world ∧ ∀ point ∈ run.points, observer point.world = observer world) :
    Eventually (historyStep fetch) (fun final =>
      LookupPost c coverage preempt returnAddress initial world answer finalWorld final ∧
      ∃ run, run.result = answer ∧ run.finalWorld = finalWorld ∧
        MirrorHistory.Accepted (MirrorHistory.lookup c.kinds c.query) world run ∧
        FramedLookupRun c observer represents final run ∧ P run)
      ⟨initial, [initial]⟩ := by
  have run := lookup_transport fetch decoder tracePc traceCmp4 traceConstCmp4 traceConstCmp1 bhEnable
    c coverage preempt returnAddress initial world pre answer finalWorld accepted P property
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro final ⟨post, sourceRun, resultEq, worldEq, acceptedRun, realizes, propertyRun⟩
  have finalFrame := post.frame c coverage preempt returnAddress initial world answer finalWorld final
    (fun memory => represents memory (observer world)) initialFrame
    frameRule
  have cutFrames := post.frame_cuts c coverage preempt returnAddress initial world answer finalWorld final
    (fun memory => represents memory (observer world)) initialFrame
    frameRule
  obtain ⟨finalSource, sourcePoints⟩ := sourceFrame sourceRun acceptedRun
  refine ⟨post, sourceRun, resultEq, worldEq, acceptedRun, ⟨realizes, ?_, ?_⟩, propertyRun⟩
  · rw [finalSource]
    exact finalFrame
  · intro i current present cut
    obtain ⟨_, _, _, aligned, _⟩ := realizes
    obtain ⟨events, last, observed, matching, latest, related⟩ := aligned i current present cut
    refine ⟨events, last, observed, matching, latest, related, ?_⟩
    rw [sourcePoints last (List.mem_of_mem_take (List.mem_of_getLast? latest))]
    exact cutFrames current (List.mem_of_getElem? present) cut

#print axioms LookupPost.frame_cuts
#print axioms lookup_framed_transport
end Binary.LookupRelation
