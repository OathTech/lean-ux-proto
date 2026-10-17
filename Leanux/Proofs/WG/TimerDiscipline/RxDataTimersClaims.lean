import Leanux.Proofs.WG.TimerDiscipline.RxDataTimersSource
import Leanux.Proofs.WG.TimerDiscipline.DataDoneClaims
import Leanux.Proofs.WG.TimerDiscipline.ArmingSourceClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

theorem rxDataReceipt_facts (pid : PeerId) :
    Noise.Product.Ensures (dataDoneCapture (liftWG (timersDataReceived pid))
      (prefixClockPath (liftWG (dataReceivedPrefix pid)) .timerJiffiesDataReceived))
      (fun _ => True) (fun cut _ => RxDataReceiptFacts pid cut) := by
  intro entry cut final pre run
  constructor
  · intro d p device resident
    have contract : Campaign2.Product.Ensures (observed (liftWG (timersDataReceived pid))
        (prefixClockPath (liftWG (dataReceivedPrefix pid)) .timerJiffiesDataReceived))
        (fun s => s = cut.before ∧ s.wg.device = some d)
        (fun _ after => RxDataReceiptEffect pid d p cut.before after) := by
      apply observed_effect
      intro initial result finish h actual
      change (((timersDataReceived pid).run initial.wg).run initial.ambient >>= fun ((value, current), inputs) =>
        Except.ok (value, {initial with wg := current, ambient := inputs})) = .ok (result, finish) at actual
      cases nativeRun : ((timersDataReceived pid).run initial.wg).run initial.ambient with
      | error stop => rw [nativeRun] at actual; cases actual
      | ok pair =>
        obtain ⟨⟨value, current⟩, inputs⟩ := pair
        cases value
        rw [nativeRun] at actual
        cases actual
        have effect := source_data_received pid d p resident cut.before.toSnapshot
          initial.wg initial.ambient () current inputs ⟨congrArg Product.Snapshot.toSnapshot h.1, h.2⟩ nativeRun
        exact effect
    have effect := dataDoneCapture_facts _ _ _ _ contract entry cut final trivial run
    exact effect.2 ⟨rfl, device⟩
  · intro d p device resident absent running alive records
    have effect := dataDoneCapture_facts _ _ _ _
      (projected_data_received_recorded pid d p resident absent running alive)
      entry cut final trivial run
    exact effect.2 ⟨device, records⟩

theorem rxDataTimersObservedPrefix_facts (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    Noise.Product.Ensures (rxDataTimersObservedPrefix pid pkt e) (fun _ => True)
      (fun cut _ => RxDataTimersFacts pid pkt cut) := by
  have keep {α : Type} (action : Leanux.M α) (P : Prop) :
      Noise.Product.Ensures action (fun _ => P) (fun _ _ => P) := by
    intro initial result final pre run
    exact pre
  unfold rxDataTimersObservedPrefix
  refine Noise.Product.ensures_bind _ _ (keep _ True) ?_
  intro ignored
  refine Noise.Product.ensures_bind _ _ (dataDoneTraversal_facts pid) ?_
  intro traversal
  refine Noise.Product.ensures_bind
    (Q := fun selected _ => selected = (pkt.bytes.length == 0) ∧ DataDoneTraversalFacts pid traversal)
    _ _ ?_ ?_
  · intro initial selected final facts run
    change Except.ok ((pkt.bytes.length == 0), {initial with ambient := {initial.ambient with steps := initial.ambient.steps.push {decision := .doneRxKeepalive, outcome := (pkt.bytes.length == 0), netRx := initial.ambient.netRxSection}}}) = .ok (selected, final) at run
    cases run
    exact ⟨rfl, facts⟩
  · intro selected
    cases selected with
    | false =>
      refine Noise.Product.ensures_bind
        (Q := fun receipt _ => (false = (pkt.bytes.length == 0) ∧ DataDoneTraversalFacts pid traversal) ∧
          RxDataReceiptFacts pid receipt)
        _ _ (fun initial receipt final h run => ⟨h, rxDataReceipt_facts pid initial receipt final trivial run⟩) ?_
      intro receipt initial cut final facts run
      cases run
      exact ⟨facts.1.1, rfl, facts.1.2, by intro other same; cases same; exact facts.2⟩
    | true =>
      refine Noise.Product.ensures_bind _ _ (keep _ _) ?_
      intro ignored initial cut final facts run
      cases run
      exact ⟨facts.1, rfl, facts.2, by intro other impossible; cases impossible⟩

theorem observedRxDataTimers_facts (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    Campaign2.Product.Ensures (observedRxDataTimers pid pkt e) (fun _ => True)
      (fun result _ => RxDataTimersFacts pid pkt result.1) := by
  change Noise.Product.Ensures _ _ _
  unfold observedRxDataTimers
  refine Noise.Product.ensures_bind _ _ (rxDataTimersObservedPrefix_facts pid pkt e) ?_
  intro cut
  refine Noise.Product.ensures_bind (Q := fun _ _ => RxDataTimersFacts pid pkt cut) _ _ ?_ ?_
  · intro initial result final pre run
    exact pre
  · intro result initial out final facts run
    cases run
    exact facts


end Leanux.Proofs.WG.TimerDiscipline
