import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchModel
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchFrames
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchClaims
import Leanux.Proofs.WG.TimerDiscipline.FireSelectionSource
import Leanux.Proofs.WG.Config.QuietTimers

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- The original pair, without a scheduler inserted between its two calls. -/
def retryDispatch (horizon : UInt64) : M Unit := do
  Env.fireTimer .timerRetransmit horizon
  Env.runOneSendWorker

/-- Each copied observation begins at that original call's actual entry. -/
def observedRetryDispatch (horizon : UInt64) : M RetryDispatchObservation := do
  let timer ← observed (Env.fireTimer .timerRetransmit horizon)
    (timerExecutionPath .timerRetransmit horizon)
  let afterTimer ← Campaign2.read
  let send ← observed Env.runOneSendWorker sendWorkerExecution
  return ⟨timer.1, afterTimer, send.1⟩

/-- Eligible queueing must successfully acquire its original reference. -/
theorem queuedAfterClock_positive (pid : PeerId) (d : Device) (p : Peer) (now : Int64)
    (resident : d.peers[pid]? = some p)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now)
    (alive : p.isDead = false) :
    Ensures (queuedAfterClock pid p now) (fun w => w.k.wg = some d)
      (fun _ _ => 0 < p.refcount) := by
  have hg := peerGet_exact pid d p resident
  have hp := unconstrained_prefix (peerPut (some pid))
  have hq := unconstrained_prefix (recordQueued .sendWorker pid)
  rw [ensures_iff]
  mvcgen [queuedAfterClock, branchCmp, branch, expired, alive, hg, hp, hq,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

/-- An empty entry queue either remains empty or receives exactly this newly
pending peer, with the positive old count established by original acquisition. -/
theorem queuedAfterClock_empty (pid : PeerId) (d : Device) (p : Peer) (now : Int64)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = []) :
    Ensures (queuedAfterClock pid p now) (fun w => w.k.wg = some d)
      (fun _ w => ∃ out, w.k.wg = some out ∧
        (out.sendWorkQueue = [] ∨ (out.sendWorkQueue = [pid] ∧
          out.peers[pid]? = some { p with refcount := p.refcount + 1, handshakePending := true } ∧
          p.isDead = false ∧ p.handshakePending = false ∧ 0 < p.refcount))) := by
  intro w result final pre run
  have device := queuedAfterClock_exact pid d p now resident w result final pre run
  refine ⟨queuedDevice d pid p now, device, ?_⟩
  by_cases expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now
  · by_cases dead : p.isDead = true
    · left; simp [queuedDevice, expired, dead, empty]
    · have alive : p.isDead = false := by simpa using dead
      by_cases pending : p.handshakePending = true
      · left; simp [queuedDevice, expired, alive, pending, withPeer, empty]
      · have fresh : p.handshakePending = false := by simpa using pending
        have positive := queuedAfterClock_positive pid d p now resident expired alive w result final pre run
        right
        simp [queuedDevice, expired, alive, fresh, withPeer, empty, positive]
  · left; simp [queuedDevice, expired, empty]

theorem sendQueuedRetry_empty (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = []) :
    Ensures (sendQueuedHandshakeInitiation pid true) (fun w => w.k.wg = some d)
      (fun _ w => ∃ out, w.k.wg = some out ∧
        (out.sendWorkQueue = [] ∨ (out.sendWorkQueue = [pid] ∧
          out.peers[pid]? = some { p with refcount := p.refcount + 1, handshakePending := true } ∧
          p.isDead = false ∧ p.handshakePending = false ∧ 0 < p.refcount))) := by
  intro w result final pre run
  cases result
  obtain ⟨value, before, first, same, device⟩ := retryReadPrefix_returns pid d p resident w pre
  subst value
  rw [sendQueuedRetry_factor, StateT.run_bind, first] at run
  change ((hiddenClock64 .birthdateExpired).run before >>= fun out =>
    (queuedAfterClock pid p out.1).run out.2) = .ok ((), final) at run
  cases clock : (hiddenClock64 .birthdateExpired).run before with
  | error e => rw [clock] at run; cases run
  | ok pair =>
    obtain ⟨now, after⟩ := pair
    rw [clock] at run
    have afterDevice := (ensures_iff _ _ _).mpr
      (hiddenClock64_kernel_spec (fun k => k.wg = some d) .birthdateExpired)
      before now after device clock
    exact queuedAfterClock_empty pid d p now resident empty after () final afterDevice run

def retryClearQueue (pid : PeerId) : M Unit := do
  clearPeerEndpointSrc pid
  sendQueuedHandshakeInitiation pid true

theorem retryClearQueue_empty (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = [])
    (detached : p.timerRetransmitHandshake = none) :
    Ensures (retryClearQueue pid)
      (fun w => w.k.wg = some (withPeer d pid { p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1 }))
      (fun _ w => ∃ out, w.k.wg = some out ∧
        (out.sendWorkQueue = [] ∨ (out.sendWorkQueue = [pid] ∧
          ∃ queued, out.peers[pid]? = some queued ∧ FreshRetryPeer p queued))) := by
  intro w result final pre run
  simp only [retryClearQueue, StateT.run_bind] at run
  cases hc : (clearPeerEndpointSrc pid).run w with
  | error e => rw [hc] at run; cases run
  | ok pair =>
    obtain ⟨u, after⟩ := pair
    rw [hc] at run
    obtain ⟨cleared, reset, device, fields, peer, others⟩ := clearEndpointSource_exact pid
      (withPeer d pid { p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1 })
      { p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1 }
      (by simp [withPeer]) w u after pre hc
    have queue : cleared.sendWorkQueue = [] := by
      have h := congrArg Device.sendWorkQueue fields
      simpa [withPeer, empty] using h
    obtain ⟨out, outDevice, casesQueue⟩ := sendQueuedRetry_empty pid cleared
      (clearedSource { p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1 } reset)
      peer queue after result final device run
    refine ⟨out, outDevice, ?_⟩
    rcases casesQueue with none | ⟨single, stored, alive, fresh, positive⟩
    · exact Or.inl none
    · right
      refine ⟨single, _, stored, ?_⟩
      simpa [FreshRetryPeer, clearedSource, detached] using And.intro alive (And.intro fresh positive)

theorem expiredRetransmit_empty (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = [])
    (detached : p.timerRetransmitHandshake = none)
    (limit : p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES) :
    Ensures (expiredRetransmitHandshake pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ out, w.k.wg = some out ∧
        (out.sendWorkQueue = [] ∨ (out.sendWorkQueue = [pid] ∧
          ∃ queued, out.peers[pid]? = some queued ∧ FreshRetryPeer p queued))) := by
  have ht := (ensures_iff _ _ _).mp (retryClearQueue_empty pid d p resident empty detached)
  rw [expiredRetransmit_source]
  change Ensures (do
    let attempts := (← getPeer pid).timerHandshakeAttempts
    if ← branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES then
      retransmitGiveUp pid
    else
      let current ← getPeer pid
      setPeer pid { current with timerHandshakeAttempts := current.timerHandshakeAttempts + 1 }
      retryClearQueue pid) _ _
  rw [ensures_iff]
  mvcgen [getPeer, getDev, getK, setPeer, modifyDev, modifyK, branchCmp, invariant, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [withPeer]
  all_goals omega

theorem fireSelected_empty (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = [])
    (limit : p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES) :
    Ensures (fireSelected .timerRetransmit pid .retransmitHandshake)
      (fun w => w.k.wg = some d)
      (fun _ w => ∃ out, w.k.wg = some out ∧
        (out.sendWorkQueue = [] ∨ (out.sendWorkQueue = [pid] ∧
          ∃ queued, out.peers[pid]? = some queued ∧ FreshRetryPeer p queued))) := by
  intro w result final pre run
  let detached := p.setTimer .retransmitHandshake none
  let detachedDevice := withPeer d pid detached
  have resident' : detachedDevice.peers[pid]? = some detached := by simp [detachedDevice, withPeer]
  have empty' : detachedDevice.sendWorkQueue = [] := empty
  have limit' : detached.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES := limit
  have hc := (ensures_iff _ _ _).mp
    (expiredRetransmit_empty pid detachedDevice detached resident' empty' rfl limit')
  have hs := runTimerSection_kernel_contract .timerRetransmit (expiredRetransmitHandshake pid)
    (fun k => k.wg = some detachedDevice)
    (fun k => ∃ out, k.wg = some out ∧
      (out.sendWorkQueue = [] ∨ (out.sendWorkQueue = [pid] ∧
        ∃ queued, out.peers[pid]? = some queued ∧ FreshRetryPeer detached queued))) hc
  obtain ⟨u, after, deletion, device⟩ := delTimer_returns pid .retransmitHandshake d p resident w pre
  simp only [fireSelected, timerCallback, StateT.run_bind, deletion] at run
  have result' := (ensures_iff _ _ _).mpr hs after result final device run
  simpa [detached, FreshRetryPeer, Peer.setTimer] using result'

/-- Selection supplies nonemptiness without any reference-count assumption. -/
theorem sendDispatch_nonempty (d : Device) :
    Ensures Env.runOneSendWorker (fun w => w.k.wg = some d)
      (fun _ _ => d.sendWorkQueue ≠ []) := by
  intro w result final pre run
  rw [runOneSendWorker_source, StateT.run_bind] at run
  cases hs : sendWorkerSelection.run w with
  | error e => rw [hs] at run; cases run
  | ok pair =>
    obtain ⟨selected, after⟩ := pair
    have effect := sendWorkerSelection_effect d w.unitPeers w selected after ⟨pre, rfl⟩ hs
    intro empty
    have member := effect.2.2.1
    simp [empty] at member

/-- Normal worker selection eliminates the callback's empty-queue alternatives.
Only then is the retained-worker contract applied. -/
theorem retry_send_completed (pid : PeerId) (before : Peer) (afterTimer final : World)
    (facts : ∃ d, afterTimer.k.wg = some d ∧
      (d.sendWorkQueue = [] ∨ (d.sendWorkQueue = [pid] ∧
        ∃ queued, d.peers[pid]? = some queued ∧ FreshRetryPeer before queued)))
    (run : Env.runOneSendWorker.run afterTimer = .ok ((), final)) :
    ∃ send, sendWorkerExecution.run afterTimer = .ok (send, final) ∧
      CompletedRetryDispatch pid before (Campaign2.snapshot afterTimer) send (Campaign2.snapshot final) := by
  obtain ⟨d, device, queueCases⟩ := facts
  have nonempty := sendDispatch_nonempty d afterTimer () final device run
  rcases queueCases with empty | ⟨single, queued, resident, fresh⟩
  · exact False.elim (nonempty empty)
  · have retained : RetainedSendQueue d := by
      intro selected member peer same
      have selectedEq : selected = pid := by simpa [single] using member
      subst selected
      rw [resident] at same
      cases same
      have oldPositive := fresh.2.2.1
      have increment := fresh.2.2.2.2.2.1
      omega
    obtain ⟨send, execution⟩ := sendWorkerExecution_success afterTimer final run
    have completed := sendWorkerExecution_effect d afterTimer.unitPeers retained
      afterTimer send final ⟨device, rfl⟩ execution
    have selectedEq : send.pid = pid := by simpa [single] using completed.1.1
    have finalView := completed.2
    obtain ⟨actual, actualResident, _, _, _, _, view⟩ := finalView
    rw [selectedEq, resident] at actualResident
    cases actualResident
    refine ⟨send, execution, d, queued, device, single, resident, fresh, selectedEq, completed, ?_⟩
    rw [selectedEq] at view
    have identity := fresh.2.2.2.1
    have attempts := fresh.2.2.2.2.1
    have refs := fresh.2.2.2.2.2.1
    simpa [identity, attempts, refs] using view

/-- Above the retry limit, the original callback leaves the send queue empty. -/
theorem expiredRetransmit_giveUp_empty (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = [])
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts) :
    Ensures (expiredRetransmitHandshake pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg.map Device.sendWorkQueue = some []) := by
  have hg := retransmitGiveUp_sendQueue pid (some [])
  rw [expiredRetransmit_source, ensures_iff]
  mvcgen [getPeer, getDev, getK, branchCmp, invariant, hg]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals omega

theorem fireSelected_giveUp_empty (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = [])
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts) :
    Ensures (fireSelected .timerRetransmit pid .retransmitHandshake)
      (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg.map Device.sendWorkQueue = some []) := by
  intro w result final pre run
  let detached := p.setTimer .retransmitHandshake none
  let detachedDevice := withPeer d pid detached
  have resident' : detachedDevice.peers[pid]? = some detached := by simp [detachedDevice, withPeer]
  have empty' : detachedDevice.sendWorkQueue = [] := empty
  have limit' : MAX_TIMER_HANDSHAKES < detached.timerHandshakeAttempts := limit
  have hc := (ensures_iff _ _ _).mp
    (expiredRetransmit_giveUp_empty pid detachedDevice detached resident' empty' limit')
  have hs := runTimerSection_kernel_contract .timerRetransmit (expiredRetransmitHandshake pid)
    (fun k => k.wg = some detachedDevice)
    (fun k => k.wg.map Device.sendWorkQueue = some []) hc
  obtain ⟨u, after, deletion, device⟩ := delTimer_returns pid .retransmitHandshake d p resident w pre
  simp only [fireSelected, timerCallback, StateT.run_bind, deletion] at run
  exact (ensures_iff _ _ _).mpr hs after result final device run

/-- The following original worker cannot select work after an empty give-up path. -/
theorem fireSelected_send_limit (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = [])
    (selected afterTimer final : World) (device : selected.k.wg = some d)
    (timerRun : (fireSelected .timerRetransmit pid .retransmitHandshake).run selected = .ok ((), afterTimer))
    (sendRun : Env.runOneSendWorker.run afterTimer = .ok ((), final)) :
    p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES := by
  by_cases limit : p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES
  · exact limit
  apply False.elim
  have above : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts := by omega
  have queue := fireSelected_giveUp_empty pid d p resident empty above
    selected () afterTimer device timerRun
  cases hd : afterTimer.k.wg with
  | none => simp [hd] at queue
  | some out =>
    have emptied : out.sendWorkQueue = [] := by simpa [hd] using queue
    exact sendDispatch_nonempty out afterTimer () final hd sendRun emptied

theorem observedRetryDispatch_run (horizon : UInt64) (w : World) :
    (observedRetryDispatch horizon).run w =
      ((Env.fireTimer .timerRetransmit horizon).run w >>= fun timerOut =>
        Env.runOneSendWorker.run timerOut.2 >>= fun sendOut =>
          Except.ok (RetryDispatchObservation.mk
            (Campaign2.observeResult ((timerExecutionPath .timerRetransmit horizon).run w))
            (Campaign2.snapshot timerOut.2)
            (Campaign2.observeResult (sendWorkerExecution.run timerOut.2)), sendOut.2)) := by
  simp only [observedRetryDispatch, observed, StateT.run_bind, StateT.run_pure]
  dsimp only [Campaign2.inspect, Campaign2.read, StateT.run, Bind.bind, Except.bind, Pure.pure]
  cases ht : Env.fireTimer .timerRetransmit horizon w with
  | error e => rfl
  | ok pair =>
    obtain ⟨u, after⟩ := pair
    dsimp only [Except.pure]
    cases hs : Env.runOneSendWorker after <;> rfl

/-- Removing both observations preserves the exact original pair, including errors. -/
theorem observedRetryDispatch_erase (horizon : UInt64) :
    (do let _ ← observedRetryDispatch horizon; pure ()) = retryDispatch horizon := by
  funext w
  change StateT.run _ w = StateT.run _ w
  rw [StateT.run_bind, observedRetryDispatch_run]
  simp only [retryDispatch, StateT.run_bind, StateT.run_pure]
  cases ht : (Env.fireTimer .timerRetransmit horizon).run w with
  | error e => rfl
  | ok pair =>
    obtain ⟨u, after⟩ := pair
    dsimp only [Bind.bind, Except.bind, Pure.pure]
    cases hs : Env.runOneSendWorker.run after with
    | error e => rfl
    | ok pair =>
      obtain ⟨u, final⟩ := pair
      cases u
      rfl

end Leanux.Proofs.WG.TimerDiscipline
