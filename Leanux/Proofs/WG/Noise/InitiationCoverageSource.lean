import Leanux.Proofs.WG.Noise.InitiationCoverageFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.InitiationCaller
open Leanux Leanux.WG TimerDiscipline

def Call.receipts : Call → List TagReceipt
  | .rateLimited => []
  | .noCreation receipt | .created _ receipt => [receipt]

theorem createObserved_coverage (pid : PeerId) (entry : Campaign2.Snapshot) :
    Ensures (createObserved pid) (fun g => responseTagMap g.dev = entry.tagAt)
      (fun out g => TagCoverage entry.tagAt [out.2] (responseTagMap g.dev)) := by
  intro g ambient out final after pre run
  change (((createInitiation pid).run g).run ambient >>= fun ((message,current),inputs) =>
    Except.ok (((message,(⟨.createInitiation pid,Campaign2.snapshot g ambient,
      .created message,Campaign2.snapshot current inputs⟩ : TagReceipt)),current),inputs)) = _ at run
  cases actual : ((createInitiation pid).run g).run ambient with
  | error stop => rw [actual] at run; cases run
  | ok result =>
    obtain ⟨⟨message,current⟩,inputs⟩ := result
    rw [actual] at run
    cases run
    refine ⟨?_,?_,TagsRetained.refl _⟩
    · intro target tag present
      rw [← pre]
      exact present
    · exact createInitiation_tagMap_projected pid (Campaign2.snapshot g ambient)
        g ambient message final after rfl actual

theorem prelude_coverage (pid : PeerId) (entry : Campaign2.Snapshot) :
    Ensures (prelude pid) (fun g => responseTagMap g.dev = entry.tagAt)
      (fun out g => TagCoverage entry.tagAt out.1.receipts (responseTagMap g.dev)) := by
  let P : WGWorld → Prop := fun g => responseTagMap g.dev = entry.tagAt
  have read : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P)
      g ambient p final after pre run).1
  unfold prelude
  refine ensures_bind _ _ read ?_
  intro p
  have expired : Ensures
      (branchExpired .initRateLimited p.lastSentHandshake REKEY_TIMEOUT (!·)) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr
      (((Leanux.Proofs.Framing.branchExpired_sameWGWorld _ _ _ (!·)).factor
        (fun g => responseTagMap g.dev)) entry.tagAt)
  refine ensures_bind _ _ expired ?_
  intro limited
  cases limited with
  | true =>
    intro g ambient result final after pre run
    cases run
    change TagsRetained entry.tagAt (responseTagMap g.dev)
    rw [pre]
    exact TagsRetained.refl _
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    change Ensures ((do
        let now ← hiddenClock64 .initLastSent
        modifyPeer pid fun p => {p with lastSentHandshake := now}
        let (created,receipt) ← createObserved pid
        if ← branch .initCreated created.isSome then
          let some msg := created | invariant "unreachable"
          let authenticated ← addMacToPacket pid msg
          return (.created msg receipt,some authenticated)
        return (.noCreation receipt,none)) : WG.M (Call × Option (List UInt8))) P
      (fun out g => TagCoverage entry.tagAt out.1.receipts (responseTagMap g.dev))
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · intro g ambient now final after pre run
      exact (ResponseCaller.clock_tag_frame _ g ambient now final after run).trans pre
    · intro now
      refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
      · intro g ambient value final after pre run
        exact (ResponseCaller.lastSent_tag_frame pid now g ambient value final after run).trans pre
      · intro u
        refine ensures_bind _ _ (createObserved_coverage pid entry) ?_
        intro out
        obtain ⟨created,receipt⟩ := out
        refine ensures_bind _ _
          ((ensures_iff _ _ _).mpr (Config.branch_state_spec
            (fun g : WGWorld => TagCoverage entry.tagAt [receipt] (responseTagMap g.dev))
            .initCreated created.isSome)) ?_
        intro made g ambient result final after pre run
        have madeEq := pre.1
        subst made
        cases created with
        | none =>
          simp only [Option.isSome_none,Bool.false_eq_true,ite_false] at run
          cases run
          exact pre.2
        | some message =>
          simp only [Option.isSome_some,ite_true] at run
          change (((addMacToPacket pid message).run g).run ambient >>= fun ((authenticated,current),inputs) =>
            Except.ok (((Call.created message receipt,some authenticated),current),inputs)) = _ at run
          cases mac : ((addMacToPacket pid message).run g).run ambient with
          | error stop => rw [mac] at run; cases run
          | ok out =>
            obtain ⟨⟨authenticated,current⟩,inputs⟩ := out
            have frame := addMacToPacket_spec_tagMap_variant pid message g.dev
              g ambient authenticated current inputs rfl mac
            rw [mac] at run
            cases run
            change TagCoverage entry.tagAt [receipt] (responseTagMap final.dev)
            rw [frame]
            exact pre.2

theorem observe_coverage (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observe pid) (fun s => s.tagAt = entry.tagAt)
      (fun call final => TagCoverage entry.tagAt call.receipts final.tagAt) := by
  change Ensures _ (fun (g : WGWorld) => responseTagMap g.dev = entry.tagAt)
    (fun (call : Call) (g : WGWorld) => TagCoverage entry.tagAt call.receipts (responseTagMap g.dev))
  unfold observe
  refine ensures_bind _ _ (prelude_coverage pid entry) ?_
  intro out
  refine ensures_bind (Q := fun _ g =>
    TagCoverage entry.tagAt out.1.receipts (responseTagMap g.dev)) _ _ ?_ ?_
  · intro g ambient result final after pre run
    have frame := initiationTraversalSuffix_tag_frame pid out.2 g.dev
      g ambient result final after rfl run
    rw [frame]
    exact pre
  · intro u g ambient result final after pre run
    cases run
    exact pre

theorem observeWorker_coverage (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observeWorker pid) (fun s => s.tagAt = entry.tagAt)
      (fun call final => TagCoverage entry.tagAt call.receipts final.tagAt) := by
  change Ensures _ (fun (g : WGWorld) => responseTagMap g.dev = entry.tagAt)
    (fun (call : Call) (g : WGWorld) => TagCoverage entry.tagAt call.receipts (responseTagMap g.dev))
  unfold observeWorker
  refine ensures_bind (Q := fun (call : Call) (g : WGWorld) =>
    TagCoverage entry.tagAt call.receipts (responseTagMap g.dev)) _ _ (observe_coverage pid entry) ?_
  intro call
  refine ensures_bind (Q := fun _ g =>
    TagCoverage entry.tagAt call.receipts (responseTagMap g.dev)) _ _ ?_ ?_
  · intro g ambient result final after pre run
    exact pre.final_retained
      (Index.staging_tags (WG.peerPut (some pid))
        (fun initial => Index.staging_peerPut initial (some pid))
        g ambient result final after run)
  · intro u g ambient result final after pre run
    cases run
    exact pre

end Leanux.Proofs.WG.Noise.InitiationCaller
