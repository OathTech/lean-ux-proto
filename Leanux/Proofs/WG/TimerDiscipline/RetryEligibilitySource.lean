import Leanux.Proofs.WG.TimerDiscipline.RetryEligibilityModel
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchLeaves

/-! Correct the old empty-queue guarantee using each execution's actual queue-record inspection. The resident, empty-queue, detached-timer and retry-limit domains are retained. Erasure preserves the original computations and every error. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do
theorem queuedAfterClock_empty (pid : PeerId) (d : Device) (p : Peer) (now : Int64)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = []) :
    Ensures (observedQueuedAfterClock pid p now) (fun g => g.dev = some d)
      (fun seen g => ∃ out, g.dev = some out ∧ RetryQueueOutcome pid p seen out) := by
  intro g ambient seen final after device run
  have facts := queuedAfterClock_exact pid d p now resident g ambient seen final after device run
  cases inspected : seen with
  | none =>
    simp only [inspected] at facts
    exact ⟨d, facts.1, Or.inl empty⟩
  | some queued =>
    simp only [inspected] at facts
    obtain ⟨expired, alive, finalDevice⟩ := facts
    have rawRun : ((queuedAfterClock pid p now).run g).run ambient = .ok (((), final), after) := by
      rw [← observedQueuedAfterClock_erase]
      change (((observedQueuedAfterClock pid p now).run g).run ambient >>= fun ((_, current), inputs) =>
        .ok (((), current), inputs)) = _
      rw [run]
      rfl
    have positive := queuedAfterClock_positive pid d p now resident expired alive
      g ambient () final after device rawRun
    refine ⟨queuedDeviceAfterInspection d pid p now queued, finalDevice, ?_⟩
    cases refused : p.handshakePending && !queued with
    | true =>
      left
      simp [queuedDeviceAfterInspection, expired, alive, refused, withPeer, empty]
    | false =>
      right
      refine ⟨?_, ?_, alive, positive, queued, rfl, refused⟩
      · simp [queuedDeviceAfterInspection, expired, alive, refused, withPeer, empty]
      · simp [queuedDeviceAfterInspection, expired, alive, refused, withPeer]

theorem sendQueuedRetry_empty (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = []) :
    Ensures (observedSendQueuedRetry pid) (fun g => g.dev = some d)
      (fun result g => ∃ out, g.dev = some out ∧ RetryQueueOutcome pid p result.2 out) := by
  intro g ambient result final ending device run
  obtain ⟨value, before, beforeAmbient, prefixRun, valueEq, beforeDevice⟩ :=
    retryReadPrefix_returns pid d p resident g ambient device
  subst value
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (input : Ambient) :
      (((action >>= next).run state).run input) =
        (((action.run state).run input) >>= fun ((value, middle), remaining) =>
          ((next value).run middle).run remaining) := rfl
  have okBind {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  simp only [observedSendQueuedRetry, bindRun, prefixRun, okBind] at run
  cases clockRun : ((hiddenClock64 .birthdateExpired : WG.M Int64).run before).run beforeAmbient with
  | error stop => rw [clockRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨now, afterClock⟩, clockAmbient⟩ := pair
    rw [clockRun] at run
    simp only [okBind] at run
    have clockDevice := (ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.hiddenClock64 .birthdateExpired)
        (fun g : WGWorld => g.dev = some d))
      before beforeAmbient now afterClock clockAmbient beforeDevice clockRun
    cases observedRun : ((observedQueuedAfterClock pid p now).run afterClock).run clockAmbient with
    | error stop => rw [observedRun] at run; cases run
    | ok pair =>
      obtain ⟨⟨seen, complete⟩, after⟩ := pair
      rw [observedRun] at run
      cases run
      exact queuedAfterClock_empty pid d p now resident empty
        afterClock clockAmbient seen complete after clockDevice observedRun
def retryClearQueue (pid : PeerId) : WG.M Unit := do
  clearPeerEndpointSrc pid
  sendQueuedHandshakeInitiation pid true

def observedRetryClearQueue (pid : PeerId) : WG.M (Option Bool) := do
  clearPeerEndpointSrc pid
  let queued ← observedSendQueuedRetry pid
  pure queued.2

theorem observedRetryClearQueue_erase (pid : PeerId) :
    (do let _ ← observedRetryClearQueue pid; pure ()) = retryClearQueue pid := by
  rw [retryClearQueue, ← observedSendQueuedRetry_erase]
  simp only [observedRetryClearQueue, bind_assoc, pure_bind]

theorem retryClearQueue_empty (pid : PeerId) (d : Device) (p : Peer)
    (_resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = [])
    (detached : p.timerRetransmitHandshake = none) :
    Ensures (observedRetryClearQueue pid)
      (fun g => g.dev = some (withPeer d pid {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1}))
      (fun seen g => ∃ out, g.dev = some out ∧
        (out.sendWorkQueue = [] ∨ (out.sendWorkQueue = [pid] ∧
          ∃ queued, out.peers[pid]? = some queued ∧ InspectedFreshRetryPeer p queued seen))) := by
  intro g ambient seen final ending pre run
  change (((clearPeerEndpointSrc pid).run g).run ambient >>= fun ((_, after), inputs) =>
    ((observedSendQueuedRetry pid).run after).run inputs >>= fun ((result, done), last) =>
      .ok ((result.2, done), last)) = _ at run
  cases clearRun : ((clearPeerEndpointSrc pid).run g).run ambient with
  | error stop => rw [clearRun] at run; cases run
  | ok output =>
    obtain ⟨⟨ignored, after⟩, inputs⟩ := output
    rw [clearRun] at run
    simp only [Bind.bind, Except.bind] at run
    obtain ⟨cleared, reset, device, fields, peer, _⟩ := clearEndpointSource_exact pid
      (withPeer d pid {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1})
      {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1}
      (by simp [withPeer]) g ambient ignored after inputs pre clearRun
    have queue : cleared.sendWorkQueue = [] := by
      have unchanged := congrArg Device.sendWorkQueue fields
      simpa [withPeer, empty] using unchanged
    cases queuedRun : ((observedSendQueuedRetry pid).run after).run inputs with
    | error stop => rw [queuedRun] at run; cases run
    | ok output =>
      obtain ⟨⟨result, done⟩, last⟩ := output
      rw [queuedRun] at run
      cases run
      obtain ⟨out, outDevice, casesQueue⟩ := sendQueuedRetry_empty pid cleared
        (clearedSource {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1} reset)
        peer queue after inputs result done last device queuedRun
      refine ⟨out, outDevice, ?_⟩
      rcases casesQueue with noQueue | ⟨single, stored, alive, positive, inspected, observed, eligible⟩
      · exact Or.inl noQueue
      · right
        refine ⟨single, _, stored, ?_⟩
        exact ⟨alive, ⟨inspected, observed, eligible⟩, positive, rfl, rfl, rfl, rfl, detached⟩

def observedRetransmitHandshake (pid : PeerId) : WG.M (Option Bool) := do
  let attempts := (← getPeer pid).timerHandshakeAttempts
  if ← branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES then
    retransmitGiveUp pid
    pure none
  else
    let p ← getPeer pid
    setPeer pid {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1}
    observedRetryClearQueue pid

theorem observedRetransmitHandshake_erase (pid : PeerId) :
    (do let _ ← observedRetransmitHandshake pid; pure ()) = expiredRetransmitHandshake pid := by
  rw [expiredRetransmit_source]
  simp only [observedRetransmitHandshake, bind_assoc]
  congr 1
  funext peer
  congr 1
  funext giveUp
  cases giveUp <;> simp only [Bool.false_eq_true, ite_false, ite_true, bind_assoc, pure_bind]
  · congr 1
    funext current
    congr 1
    funext ignored
    exact observedRetryClearQueue_erase pid
  · simp

theorem expiredRetransmit_empty (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = [])
    (detached : p.timerRetransmitHandshake = none)
    (limit : p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES) :
    Ensures (observedRetransmitHandshake pid) (fun g => g.dev = some d)
      (fun seen g => ∃ out, g.dev = some out ∧
        (out.sendWorkQueue = [] ∨ (out.sendWorkQueue = [pid] ∧
          ∃ queued, out.peers[pid]? = some queued ∧ InspectedFreshRetryPeer p queued seen))) := by
  intro g ambient seen final ending device run
  have notAbove : ¬p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES := by omega
  simp [observedRetransmitHandshake, getPeer, getDev, device, resident,
    branchCmp, AmbientM.branchCmp, notAbove, setPeer, modifyDev] at run
  exact retryClearQueue_empty pid d p resident empty detached _ _ seen final ending rfl run

end Leanux.Proofs.WG.TimerDiscipline
