import Leanux.Proofs.WG.TimerDiscipline.RetryGiveUpFrames
import Leanux.Proofs.WG.TimerDiscipline.RetryEligibilitySource
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchLeaves
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchModel
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchFrames
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchClaims
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchWorkSource
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
