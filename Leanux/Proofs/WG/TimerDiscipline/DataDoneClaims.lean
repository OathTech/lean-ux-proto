import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource
import Leanux.Proofs.WG.Config.BranchSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Std.Do Campaign2
variable {α β : Type}

theorem dataDoneObservedStep_facts (pid : PeerId) (id : SkbId) (before : Bool) :
    Noise.Product.Ensures (liftWG (dataDoneObservedStep pid id before)) (fun _ => True)
      (fun result _ =>
        result.1 = .yield (before || result.2.qualifies) ∧
        result.2.id = id ∧
        result.2.qualifies = (result.2.sent && !(result.2.packet.bytes.length == MESSAGE_DATA_LEN_0))) := by
  have native : Noise.Ensures (dataDoneObservedStep pid id before) (fun _ => True)
      (fun result _ => result.1 = .yield (before || result.2.qualifies) ∧ result.2.id = id ∧
        result.2.qualifies = (result.2.sent && !(result.2.packet.bytes.length == MESSAGE_DATA_LEN_0))) := by
    have trivial_call {γ : Type} (operation : WG.M γ) :
        Noise.Ensures operation (fun _ => True) (fun _ _ => True) := by
      intro entry ambient result final after pre run
      trivial
    unfold dataDoneObservedStep
    refine Noise.ensures_bind _ _ (trivial_call _) ?_
    intro packet
    refine Noise.ensures_bind _ _ (trivial_call _) ?_
    intro ignored
    refine Noise.ensures_bind _ _ (trivial_call _) ?_
    intro sent g ambient result final after pre run
    cases sent <;> cases keepalive : packet.bytes.length == MESSAGE_DATA_LEN_0 <;>
      cases before <;>
      simp [WG.andM, branch, AmbientM.branch, keepalive] at run <;>
      cases run <;> simp_all
  intro entry result final pre run
  change (((dataDoneObservedStep pid id before).run entry.wg).run entry.ambient >>= _) = _ at run
  cases step : ((dataDoneObservedStep pid id before).run entry.wg).run entry.ambient with
  | error stop => rw [step] at run; cases run
  | ok pair =>
    obtain ⟨⟨out, state⟩, after⟩ := pair
    rw [step] at run
    cases run
    exact native entry.wg entry.ambient _ _ _ trivial step

theorem dataDoneObservedItems_facts (pid : PeerId) (items : List SkbId) (before : Bool) :
    Noise.Product.Ensures (liftWG (dataDoneObservedItems pid items before)) (fun _ => True)
      (fun out _ =>
        out.2.map DataDoneItem.id = items ∧
        (∀ observation ∈ out.2,
          observation.qualifies =
            (observation.sent && !(observation.packet.bytes.length == MESSAGE_DATA_LEN_0))) ∧
        out.1 = (before || out.2.any
          (fun observation => observation.sent && !(observation.packet.bytes.length == MESSAGE_DATA_LEN_0)))) := by
  induction items generalizing before with
  | nil =>
    intro entry out final pre run
    change Except.ok ((before, []), entry) = .ok (out, final) at run
    cases run
    simp
  | cons id rest ih =>
    intro entry out final pre run
    simp only [dataDoneObservedItems, liftWG_bind_variant] at run
    change ((liftWG (dataDoneObservedStep pid id before)).run entry >>= _) = _ at run
    cases headRun : (liftWG (dataDoneObservedStep pid id before)).run entry with
    | error stop => rw [headRun] at run; cases run
    | ok pair =>
      rcases pair with ⟨⟨next, observation⟩, middle⟩
      obtain ⟨nextEq, idEq, qualifiesEq⟩ :=
        dataDoneObservedStep_facts pid id before entry (next, observation) middle trivial headRun
      change next = .yield (before || observation.qualifies) at nextEq
      subst next
      change observation.id = id at idEq
      change observation.qualifies =
        (observation.sent && !(observation.packet.bytes.length == MESSAGE_DATA_LEN_0)) at qualifiesEq
      rw [headRun] at run
      simp only [bind, Except.bind] at run
      change (liftWG (dataDoneObservedItems pid rest (before || observation.qualifies) >>= fun tail =>
        pure (tail.1, observation :: tail.2))).run middle = .ok (out, final) at run
      rw [liftWG_bind_variant] at run
      change ((liftWG (dataDoneObservedItems pid rest (before || observation.qualifies))).run middle >>=
        fun tail => Except.ok ((tail.1.1, observation :: tail.1.2), tail.2)) = .ok (out, final) at run
      cases tailRun : (liftWG (dataDoneObservedItems pid rest (before || observation.qualifies))).run middle with
      | error stop => rw [tailRun] at run; cases run
      | ok pair =>
        rcases pair with ⟨⟨flag, tail⟩, dataDoneFinish⟩
        rw [tailRun] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
        obtain ⟨ids, qualifiers, accumulator⟩ :=
          ih (before || observation.qualifies) middle (flag, tail) dataDoneFinish trivial tailRun
        refine ⟨?_, ?_, ?_⟩
        · simp [idEq, ids]
        · intro other member
          rcases List.mem_cons.mp member with rfl | member
          · exact qualifiesEq
          · exact qualifiers other member
        · simpa [List.any_cons, qualifiesEq, Bool.or_assoc] using accumulator


theorem dataDoneCapture_facts (operation : Leanux.M Unit) (probe : Leanux.M α)
    (P : Product.Snapshot → Prop) (Q : (Product.Outcome α × Unit) → Product.Snapshot → Prop)
    (contract : Campaign2.Product.Ensures (observed operation probe) P Q) :
    Noise.Product.Ensures (dataDoneCapture operation probe) (fun _ => True)
      (fun cut final => cut.after = Product.snapshot final ∧
        (P cut.before → Q (cut.value, ()) cut.after)) := by
  intro entry cut final pre run
  change ((observed operation probe).run entry >>= fun out =>
    Except.ok (DataDoneTimerCut.mk (Product.snapshot entry) out.1.1 (Product.snapshot out.2), out.2)) =
      .ok (cut, final) at run
  cases hr : (observed operation probe).run entry with
  | error stop => rw [hr] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨value, u⟩, after⟩
    cases u
    rw [hr] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact ⟨rfl, fun h => contract entry (value, ()) after h hr⟩


theorem dataDoneTraversal_facts (pid : PeerId) :
    Noise.Product.Ensures (dataDoneCapture (liftWG (timersTraversal pid))
      (prefixClockPath (liftWG (traversalPrefix pid)) .timerJiffiesTraversal))
      (fun _ => True) (fun cut _ => DataDoneTraversalFacts pid cut) := by
  intro entry cut final pre run d p device resident enabled running alive records
  have effect := dataDoneCapture_facts _ _ _ _
    (projected_traversal_recorded pid d p resident enabled running alive)
    entry cut final trivial run
  exact effect.2 ⟨device, records⟩

theorem dataDoneSent_facts (pid : PeerId) :
    Noise.Product.Ensures (dataDoneCapture (liftWG (timersDataSent pid))
      (prefixClockJitterPath (liftWG (dataSentPrefix pid)) .timerJiffiesDataSent .newHandshakeJitter))
      (fun _ => True) (fun cut _ => DataDoneSentFacts pid cut) := by
  intro entry cut final pre run d p device resident absent running alive records
  have effect := dataDoneCapture_facts _ _ _ _
    (projected_data_sent_recorded pid d p resident absent running alive)
    entry cut final trivial run
  exact effect.2 ⟨device, records⟩

theorem observedDataDone_facts (pid : PeerId) (items : List SkbId) :
    Campaign2.Product.Ensures (observedDataDone pid items) (fun _ => True)
      (fun cut _ => DataDoneFacts pid items cut) := by
  have keep {γ : Type} (operation : Leanux.M γ) (fact : Prop) :
      Noise.Product.Ensures operation (fun _ => fact) (fun _ _ => fact) := by
    intro entry result final h run
    exact h
  change Noise.Product.Ensures _ _ _
  unfold observedDataDone dataDonePrefix
  simp only [bind_assoc, pure_bind]
  refine Noise.Product.ensures_bind _ _ (dataDoneTraversal_facts pid) ?_
  intro traversal
  refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
  intro ignored
  refine Noise.Product.ensures_bind
    (Q := fun out _ => DataDoneTraversalFacts pid traversal ∧
      out.2.map DataDoneItem.id = items ∧
      (∀ observation ∈ out.2, observation.qualifies =
        (observation.sent && !(observation.packet.bytes.length == MESSAGE_DATA_LEN_0))) ∧
      out.1 = (false || out.2.any
        (fun observation => observation.sent && !(observation.packet.bytes.length == MESSAGE_DATA_LEN_0))))
    _ _ (fun entry out final h run =>
      ⟨h, dataDoneObservedItems_facts pid items false entry out final trivial run⟩) ?_
  intro pair
  obtain ⟨sent, observations⟩ := pair
  let bodyFacts : Prop := DataDoneTraversalFacts pid traversal ∧
    observations.map DataDoneItem.id = items ∧
    (∀ observation ∈ observations, observation.qualifies =
      (observation.sent && !(observation.packet.bytes.length == MESSAGE_DATA_LEN_0))) ∧
    sent = (false || observations.any
      (fun observation => observation.sent && !(observation.packet.bytes.length == MESSAGE_DATA_LEN_0)))
  refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
  intro ignored
  refine Noise.Product.ensures_bind (Q := fun selected _ => selected = sent ∧ bodyFacts) _ _ ?_ ?_
  · intro entry selected final h run
    change Except.ok (sent, {entry with ambient := {entry.ambient with steps := entry.ambient.steps.push {decision := .doneDataSent, outcome := sent, netRx := entry.ambient.netRxSection}}}) = .ok (selected, final) at run
    cases run
    exact ⟨rfl, h⟩
  · intro selected
    refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
    intro beforeSent
    cases selected with
    | false =>
      change Noise.Product.Ensures (do
        liftWG (keepKeyFresh pid)
        pure (DataDoneObservation.mk traversal observations sent beforeSent none)) _ _
      refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
      intro ignored entry cut final facts run
      cases run
      obtain ⟨selectedEq, traversalFacts, ids, qualifies, accumulated⟩ := facts
      refine ⟨ids, qualifies, ?_, selectedEq, traversalFacts, ?_⟩
      · simpa only [Bool.false_or] using accumulated
      · intro other impossible
        cases impossible
    | true =>
      simp only [Bool.true_eq, ite_true, bind_assoc, pure_bind]
      change Noise.Product.Ensures (do
        let hook ← dataDoneCapture (liftWG (timersDataSent pid))
          (prefixClockJitterPath (liftWG (dataSentPrefix pid)) .timerJiffiesDataSent .newHandshakeJitter)
        liftWG (keepKeyFresh pid)
        pure (DataDoneObservation.mk traversal observations sent beforeSent (some hook))) _ _
      refine Noise.Product.ensures_bind
        (Q := fun hook _ => (true = sent ∧ bodyFacts) ∧ DataDoneSentFacts pid hook)
        _ _ (fun entry hook final h run =>
          ⟨⟨h.1.symm, h.2⟩, dataDoneSent_facts pid entry hook final trivial run⟩) ?_
      intro hook
      refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
      intro ignored entry cut final facts run
      cases run
      obtain ⟨⟨selectedEq, traversalFacts, ids, qualifies, accumulated⟩, hookFacts⟩ := facts
      refine ⟨ids, qualifies, ?_, selectedEq, traversalFacts, ?_⟩
      · simpa only [Bool.false_or] using accumulated
      · intro other same
        cases same
        exact hookFacts


theorem observedDataDone_gate (pid : PeerId) (items : List SkbId) :
    Noise.Product.Ensures (observedDataDone pid items) (fun _ => True)
      (fun cut _ => cut.items.map DataDoneItem.id = items ∧
        cut.sent = cut.items.any
          (fun x => x.sent && !(x.packet.bytes.length == MESSAGE_DATA_LEN_0)) ∧
        cut.dataHook.isSome = cut.sent) := by
  intro entry cut final pre run
  obtain ⟨ids, _, sent, hook, _, _⟩ := observedDataDone_facts pid items entry cut final trivial run
  exact ⟨ids, sent, hook⟩

end Leanux.Proofs.WG.TimerDiscipline
