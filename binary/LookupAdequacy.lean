import LookupSelectedReturn
import LookupMissExecution

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Function-level lookup simulation under the named decoder and physical
    service contracts. Every machine premise is in the witnessed Pre_lookup;
    no region preservation, future readiness, live-peer restriction or source
    decision sequence is a premise. Kraken's undefined instruction outcomes
    remain universally quantified by historyStep/Eventually. -/
theorem lookup_simulation (fetch : Int64 → Option Decoded)
    (decoder : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp4 : TraceCmp4Contract fetch)
    (traceConstCmp4 : TraceConstCmp4Contract fetch) (traceConstCmp1 : TraceConstCmp1Contract fetch)
    (bhEnable : BhEnableContract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (initial : MachineState) (world : World)
    (pre : Pre_lookup c coverage preempt returnAddress initial world)
    (answer : Option (IndexOwner × PeerId)) (finalWorld : World)
    (accepted : (indexLookup c.kinds c.query).run world = .ok (answer, finalWorld)) :
    Eventually (historyStep fetch)
      (LookupPost c coverage preempt returnAddress initial world answer finalWorld)
      ⟨initial, [initial]⟩ := by
  have entryPC : initial.pc = Image.Lookup.entry := by obtain ⟨_, entry⟩ := pre; exact entry.pc
  cases initial with
  | mk s pc =>
    dsimp only at entryPC
    subst pc
    cases focused : c.focus.owner with
    | some owner =>
      exact selected_execution fetch decoder tracePc traceCmp4 traceConstCmp4 traceConstCmp1 bhEnable
        c coverage preempt returnAddress s world pre owner focused answer finalWorld accepted
    | none =>
      have run := miss_execution fetch decoder tracePc traceCmp4 traceConstCmp4 bhEnable
        c coverage preempt returnAddress s world pre focused answer finalWorld accepted
      apply eventually_weaken (historyStep fetch) _ _ _ _ run
      rintro final ⟨ret, zero, answerEq, rest⟩
      exact ⟨ret, by simpa only [answerEq, LookupResult] using zero, rest⟩

/-- The source run realized at actual machine correspondence points and
    cuts. This does not choose a different source history for each property. -/
def RealizesLookupRun (c : Config) (final : Executed)
    (run : MirrorHistory.Run (Option (IndexOwner × PeerId))) : Prop :=
  ∃ points,
    observe c.rxSection final.history = .ok points ∧
    MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history) points run.points ∧
    ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history run.points ∧
    R c final.history points final.machine run.finalWorld

/-- Generic transport is one application of lookup_simulation, for every
    predicate on accepted mirror runs. The same accepted run is realized by
    the machine execution; no result-specific statement or proof is used. -/
theorem lookup_transport (fetch : Int64 → Option Decoded)
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
    (property : ∀ run, MirrorHistory.Accepted (MirrorHistory.lookup c.kinds c.query) world run → P run) :
    Eventually (historyStep fetch) (fun final =>
      LookupPost c coverage preempt returnAddress initial world answer finalWorld final ∧
      ∃ run, run.result = answer ∧ run.finalWorld = finalWorld ∧
        MirrorHistory.Accepted (MirrorHistory.lookup c.kinds c.query) world run ∧
        RealizesLookupRun c final run ∧ P run)
      ⟨initial, [initial]⟩ := by
  have simulation := lookup_simulation fetch decoder tracePc traceCmp4 traceConstCmp4 traceConstCmp1 bhEnable
    c coverage preempt returnAddress initial world pre answer finalWorld accepted
  apply eventually_weaken (historyStep fetch) _ _ _ _ simulation
  intro final post
  have originalPost := post
  obtain ⟨_, _, v, points, source, _, _, sourceRun, observed, matched, aligned, related, _⟩ := post
  let run : MirrorHistory.Run (Option (IndexOwner × PeerId)) := ⟨answer, finalWorld, source⟩
  have acceptedRun : MirrorHistory.Accepted (MirrorHistory.lookup c.kinds c.query) world run := sourceRun
  exact ⟨originalPost, run, rfl, rfl, acceptedRun, ⟨points, observed, matched, aligned, related⟩, property run acceptedRun⟩

/-- Every memory interpretation insensitive to the proved writes is
    preserved. Untouched structures need no clause in the lookup relation. -/
theorem LookupPost.frame (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (ra : UInt64)
    (initial : MachineState) (world : World) (answer : Option (IndexOwner × PeerId))
    (finalWorld : World) (final : Executed)
    (post : LookupPost c coverage preempt ra initial world answer finalWorld final)
    (F : Mem 64 → Prop) (initialFrame : F initial.data.dmem)
    (stable : ∀ v, LookupEntry c coverage preempt ra initial world v →
      ∀ before after, EqualOutside (LookupWrites c coverage preempt initial.data v) before after → F before → F after) :
    F final.machine.data.dmem := by
  obtain ⟨_, _, v, _, _, entry, frame, _⟩ := post
  exact stable v entry _ _ frame initialFrame

#print axioms lookup_simulation
#print axioms lookup_transport
#print axioms LookupPost.frame
end Binary.LookupRelation
