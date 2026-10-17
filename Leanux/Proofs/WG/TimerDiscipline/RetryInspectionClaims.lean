import Leanux.Proofs.WG.TimerDiscipline.RetryInspectionSource
import Leanux.Proofs.WG.TimerDiscipline.FireSectionSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- The actual selected wheel-unit callback leaves an empty queue or a singleton
with eligibility justified by the queue bit it inspected on that same run. -/
theorem fireSelected_empty (pid : PeerId) (we : WheelEntry) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = [])
    (limit : p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES) :
    Product.Ensures (observedFireSelected pid we)
      (fun w => w.wg.dev = some d)
      (fun seen w => ∃ out, w.wg.dev = some out ∧
        (out.sendWorkQueue = [] ∨ (out.sendWorkQueue = [pid] ∧
          ∃ queued, out.peers[pid]? = some queued ∧ InspectedFreshRetryPeer p queued seen))) := by
  let detached := FireReady.detachedPeer p
  let detachedDevice := withPeer d pid detached
  let P : WGWorld → Prop := fun g => g.dev = some detachedDevice
  let Q : Option Bool → WGWorld → Prop := fun seen g => ∃ out, g.dev = some out ∧
    (out.sendWorkQueue = [] ∨ (out.sendWorkQueue = [pid] ∧
      ∃ queued, out.peers[pid]? = some queued ∧ InspectedFreshRetryPeer p queued seen))
  have ambientFrame {α : Type} (action : AmbientM α) (R : WGWorld → Prop) :
      Product.Ensures (liftAmbient action) (fun w => R w.wg) (fun _ w => R w.wg) := by
    intro w result final pre run
    change (action.run w.ambient >>= fun (value, after) =>
      .ok (value, {w with ambient := after})) = .ok (result, final) at run
    cases actual : action.run w.ambient with
    | error stop => rw [actual] at run; cases run
    | ok pair => rw [actual] at run; cases run; exact pre
  have native : Ensures (observedRetransmitHandshake pid) P Q := by
    simpa only [P, Q, detached, FireReady.detachedPeer, InspectedFreshRetryPeer,
      Peer.setTimer, Peer.setWheel] using
      expiredRetransmit_empty pid detachedDevice detached (by simp [detachedDevice, withPeer]) empty rfl limit
  have callback : Product.Ensures (liftWG (observedRetransmitHandshake pid))
      (fun w => P w.wg) (fun seen w => Q seen w.wg) := by
    intro w result final pre run
    change (((observedRetransmitHandshake pid).run w.wg).run w.ambient >>= fun ((value, state), input) =>
      .ok (value, {w with wg := state, ambient := input})) = _ at run
    cases actual : ((observedRetransmitHandshake pid).run w.wg).run w.ambient with
    | error stop => rw [actual] at run; cases run
    | ok pair =>
      obtain ⟨⟨value, state⟩, input⟩ := pair
      rw [actual] at run
      cases run
      exact native w.wg w.ambient result state input pre actual
  have sectionContract : Product.Ensures (observedRetransmitSection pid)
      (fun w => P w.wg) (fun seen w => Q seen w.wg) := by
    change Product.Ensures (do
      liftAmbient (modify fun s => {s with fired := s.fired.push Worker.timerRetransmit.symbol})
      let _ ← liftAmbient (AmbientM.hidden (.sectionStart .timerRetransmit))
      let seen ← liftWG (observedRetransmitHandshake pid)
      let _ ← liftAmbient (AmbientM.hidden (.sectionStop .timerRetransmit))
      pure seen) _ _
    refine Product.ensures_bind _ _ (ambientFrame _ P) ?_
    intro ignored
    refine Product.ensures_bind _ _ (ambientFrame _ P) ?_
    intro ignored
    refine Product.ensures_bind _ _ callback ?_
    intro seen
    refine Product.ensures_bind _ _ (ambientFrame _ (Q seen)) ?_
    intro ignored w result final pre run
    cases run
    exact pre
  have deletion : Product.Ensures (liftWG (delTimer pid .retransmitHandshake))
      (fun w => w.wg.dev = some d) (fun _ w => P w.wg) := by
    intro w result final pre run
    rw [FireReady.detach w d p pid pre resident] at run
    cases run
    rfl
  have enter : Product.Ensures (modifyWG fun s => {s with timerPassStep := some we.bucketExpiry})
      (fun (w : World) => P w.wg) (fun _ (w : World) => P w.wg) := by
    intro w result final pre run
    cases run
    exact pre
  have leave (seen : Option Bool) :
      Product.Ensures (modifyWG fun s => {s with timerPassStep := none})
        (fun (w : World) => Q seen w.wg) (fun _ (w : World) => Q seen w.wg) := by
    intro w result final pre run
    cases run
    exact pre
  change Product.Ensures (do
    liftWG (delTimer pid .retransmitHandshake)
    modifyWG fun s => {s with timerPassStep := some we.bucketExpiry}
    let seen ← observedRetransmitSection pid
    modifyWG fun s => {s with timerPassStep := none}
    pure seen) _ _
  refine Product.ensures_bind _ _ deletion ?_
  intro ignored
  refine Product.ensures_bind _ _ enter ?_
  intro ignored
  refine Product.ensures_bind _ _ sectionContract ?_
  intro seen
  refine Product.ensures_bind _ _ (leave seen) ?_
  intro ignored w result final pre run
  cases run
  exact pre
end Leanux.Proofs.WG.TimerDiscipline
