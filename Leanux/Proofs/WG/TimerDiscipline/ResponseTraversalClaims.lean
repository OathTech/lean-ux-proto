import Leanux.Proofs.WG.TimerDiscipline.ResponseTraversalSource
import Leanux.Proofs.WG.TimerDiscipline.OutgoingResponseSessionClaims
import Leanux.Proofs.WG.TimerDiscipline.DataDoneClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Std.Do

theorem traversalCapture_entry (pid : PeerId) (before : Snapshot) :
    Noise.Ensures (dataDoneCapture (timersTraversal pid)
      (prefixClockPath (traversalPrefix pid) .timerJiffiesTraversal))
      (fun w => snapshot w = before)
      (fun cut _ => cut.before = before ∧ DataDoneTraversalFacts pid cut) := by
  intro entry cut final pre run
  have facts := dataDoneTraversal_facts pid entry cut final trivial run
  refine ⟨?_, facts⟩
  change ((observed (timersTraversal pid)
      (prefixClockPath (traversalPrefix pid) .timerJiffiesTraversal)).run entry >>= fun out =>
    Except.ok (DataDoneTimerCut.mk (snapshot entry) out.1.1 (snapshot out.2), out.2)) =
      .ok (cut, final) at run
  cases h : (observed (timersTraversal pid)
      (prefixClockPath (traversalPrefix pid) .timerJiffiesTraversal)).run entry with
  | error err => rw [h] at run; cases run
  | ok pair =>
    rw [h] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact pre

theorem responseTraversalPrefix_facts (pid : PeerId) :
    Noise.Ensures (responseTraversalPrefix pid) (fun _ => True)
      (fun cut _ => ResponseTraversalFacts pid cut) := by
  have hp := (ensures_iff _ _ _).mp (outgoingResponseSessionPrefix_facts pid)
  have ht := fun before => (ensures_iff _ _ _).mp (traversalCapture_entry pid before)
  have hr := fun candidate => Roaming.read_snapshot (fun w =>
    ∀ cut : OutgoingResponseSessionCall, candidate = some cut →
      ResponseSessionFacts pid cut.session ∧ responseSessionEnd cut.session = snapshot w)
  rw [ensures_iff]
  mvcgen [responseTraversalPrefix, hp, ht, hr]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ResponseTraversalFacts]

theorem observedResponseTraversal_facts (pid : PeerId) :
    Campaign2.Ensures (observedResponseTraversal pid) (fun _ => True)
      (fun cut _ => ResponseTraversalFacts pid cut) := by
  have hp := (ensures_iff _ _ _).mp (responseTraversalPrefix_facts pid)
  have hs (response : Option OutgoingResponseSessionCall) :
      ⦃fun _ => ⌜True⌝⦄ responseTraversalFinish pid response ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro entry ret final pre run
    trivial
  change Noise.Ensures _ _ _
  rw [ensures_iff]
  mvcgen [observedResponseTraversal, hp, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

end Leanux.Proofs.WG.TimerDiscipline
