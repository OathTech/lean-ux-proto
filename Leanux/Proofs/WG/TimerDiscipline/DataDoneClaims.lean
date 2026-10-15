import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Std.Do Campaign2
variable {α β : Type}

theorem dataDoneObservedStep_facts (pid : PeerId) (id : SkbId) (before : Bool) :
    Noise.Ensures (dataDoneObservedStep pid id before) (fun _ => True)
      (fun result _ =>
        result.1 = .yield (before || result.2.qualifies) ∧
        result.2.id = id ∧
        result.2.qualifies = (result.2.sent && !(result.2.packet.bytes.length == MESSAGE_DATA_LEN_0))) := by
  have trivial_call {α : Type} (operation : M α) :
      ⦃fun _ => ⌜True⌝⦄ operation ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry result final pre run
    trivial
  have hg := trivial_call (getTxSkb id)
  have hs := fun bytes ds => trivial_call (sendSkbToPeer pid bytes ds)
  rw [ensures_iff]
  mvcgen [dataDoneObservedStep, branch, WG.andM, hg, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all


theorem dataDoneObservedItems_facts (pid : PeerId) (items : List SkbId) (before : Bool) :
    Noise.Ensures (dataDoneObservedItems pid items before) (fun _ => True)
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
    rw [dataDoneObservedItems] at run
    change ((dataDoneObservedStep pid id before).run entry >>= _) = _ at run
    cases headRun : (dataDoneObservedStep pid id before).run entry with
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
      change ((dataDoneObservedItems pid rest (before || observation.qualifies)).run middle >>=
        fun tail => Except.ok ((tail.1.1, observation :: tail.1.2), tail.2)) = .ok (out, final) at run
      cases tailRun : (dataDoneObservedItems pid rest (before || observation.qualifies)).run middle with
      | error stop => rw [tailRun] at run; cases run
      | ok pair =>
        rcases pair with ⟨⟨flag, tail⟩, dataDoneFinish⟩
        rw [tailRun] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
        obtain ⟨ids, qualifiers, accumulator⟩ :=
          ih (before || observation.qualifies) middle (flag, tail) dataDoneFinish trivial tailRun
        refine ⟨?_, ?_, ?_⟩
        · simpa [idEq, ids]
        · intro other member
          rcases List.mem_cons.mp member with rfl | member
          · exact qualifiesEq
          · exact qualifiers other member
        · simpa [List.any_cons, qualifiesEq, Bool.or_assoc] using accumulator


theorem dataDoneCapture_facts (operation : M Unit) (probe : M α)
    (P : Snapshot → Prop) (Q : (Outcome α × Unit) → Snapshot → Prop)
    (contract : Campaign2.Ensures (observed operation probe) P Q) :
    Noise.Ensures (dataDoneCapture operation probe) (fun _ => True)
      (fun cut final => cut.after = snapshot final ∧
        (P cut.before → Q (cut.value, ()) cut.after)) := by
  intro entry cut final pre run
  change ((observed operation probe).run entry >>= fun out =>
    Except.ok (DataDoneTimerCut.mk (snapshot entry) out.1.1 (snapshot out.2), out.2)) =
      .ok (cut, final) at run
  cases hr : (observed operation probe).run entry with
  | error stop => rw [hr] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨value, unit⟩, after⟩
    cases unit
    rw [hr] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact ⟨rfl, fun h => contract entry (value, ()) after h hr⟩


theorem observedDataDone_gate (pid : PeerId) (items : List SkbId) :
    Noise.Ensures (observedDataDone pid items) (fun _ => True)
      (fun cut _ => cut.items.map DataDoneItem.id = items ∧
        cut.sent = cut.items.any
          (fun x => x.sent && !(x.packet.bytes.length == MESSAGE_DATA_LEN_0)) ∧
        cut.dataHook.isSome = cut.sent) := by
  have trivial_call {α : Type} (operation : M α) :
      ⦃fun _ => ⌜True⌝⦄ operation ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry result final pre run
    trivial
  have ht := trivial_call (dataDoneCapture (timersTraversal pid)
    (prefixClockPath (traversalPrefix pid) .timerJiffiesTraversal))
  have ha := trivial_call (timersAnyAuthenticatedPacketSent pid)
  have hi := (ensures_iff _ _ _).mp (dataDoneObservedItems_facts pid items false)
  have hd := trivial_call (dataDoneCapture (timersDataSent pid)
    (prefixClockJitterPath (dataSentPrefix pid) .timerJiffiesDataSent .newHandshakeJitter))
  have hk := trivial_call (keepKeyFresh pid)
  have hr := Roaming.read_snapshot (fun _ => True)
  rw [ensures_iff]
  mvcgen [observedDataDone, dataDonePrefix, branch, ht, ha, hi, hd, hk, hr]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all



theorem dataDoneTraversal_facts (pid : PeerId) :
    Noise.Ensures (dataDoneCapture (timersTraversal pid)
      (prefixClockPath (traversalPrefix pid) .timerJiffiesTraversal))
      (fun _ => True) (fun cut _ => DataDoneTraversalFacts pid cut) := by
  intro entry cut final pre run d p device resident enabled running alive records
  have effect := dataDoneCapture_facts _ _ _ _
    (projected_traversal_recorded pid d p resident enabled running alive)
    entry cut final trivial run
  exact effect.2 ⟨device, records⟩

theorem dataDoneSent_facts (pid : PeerId) :
    Noise.Ensures (dataDoneCapture (timersDataSent pid)
      (prefixClockJitterPath (dataSentPrefix pid) .timerJiffiesDataSent .newHandshakeJitter))
      (fun _ => True) (fun cut _ => DataDoneSentFacts pid cut) := by
  intro entry cut final pre run d p device resident absent running alive records
  have effect := dataDoneCapture_facts _ _ _ _
    (projected_data_sent_recorded pid d p resident absent running alive)
    entry cut final trivial run
  exact effect.2 ⟨device, records⟩

theorem observedDataDone_facts (pid : PeerId) (items : List SkbId) :
    Campaign2.Ensures (observedDataDone pid items) (fun _ => True)
      (fun cut _ => DataDoneFacts pid items cut) := by
  have trivial_call {α : Type} (operation : M α) :
      ⦃fun _ => ⌜True⌝⦄ operation ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry result final pre run
    trivial
  have ht := (ensures_iff _ _ _).mp (dataDoneTraversal_facts pid)
  have ha := trivial_call (timersAnyAuthenticatedPacketSent pid)
  have hi := (ensures_iff _ _ _).mp (dataDoneObservedItems_facts pid items false)
  have hd := (ensures_iff _ _ _).mp (dataDoneSent_facts pid)
  have hk := trivial_call (keepKeyFresh pid)
  have hr := Roaming.read_snapshot (fun _ => True)
  change Noise.Ensures _ _ _
  rw [ensures_iff]
  mvcgen [observedDataDone, dataDonePrefix, branch, ht, ha, hi, hd, hk, hr]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [DataDoneFacts]

end Leanux.Proofs.WG.TimerDiscipline
