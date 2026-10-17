import Leanux.Proofs.WG.TimerDiscipline.RetryGiveUpSource
import Leanux.Proofs.WG.TimerDiscipline.View
import Leanux.Proofs.WG.Config.QueuedHandshake

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- The retry prefix logs its false reset decision and preserves the attempt count. -/
def retryReadPrefix (pid : PeerId) : WG.M Peer := do
  requireNotPending pid "queueing a handshake"
  _ ← branch .queuedNotRetry false
  getPeer pid

theorem sendQueuedRetry_factor (pid : PeerId) :
    sendQueuedHandshakeInitiation pid true = (do
      let p ← retryReadPrefix pid
      let now ← hiddenClock64 .birthdateExpired
      queuedAfterClock pid p now) := by
  simp [sendQueuedHandshakeInitiation, retryReadPrefix, queuedAfterClock,
    requireNotPending, branchExpired, birthdateTest, branch, AmbientM.branch, bind_assoc]

theorem retryReadPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (retryReadPrefix pid) (fun g => g.dev = some d)
      (fun result g => result = p ∧ g.dev = some d) := by
  intro g ambient device
  refine ⟨p, g, {ambient with steps := ambient.steps.push {
    decision := .queuedNotRetry, outcome := false, netRx := ambient.netRxSection}}, ?_, rfl, device⟩
  simp [retryReadPrefix, requireNotPending, branch, AmbientM.branch,
    getPeer, getDev, device, resident]
  rfl

/-- Decorate the actual retry clock and queue inspection without resetting attempts. -/
def observedSendQueuedRetry (pid : PeerId) : WG.M (Int64 × Option Bool) := do
  let p ← retryReadPrefix pid
  let now ← hiddenClock64 .birthdateExpired
  let seen ← observedQueuedAfterClock pid p now
  pure (now, seen)

theorem observedSendQueuedRetry_erase (pid : PeerId) :
    (do let _ ← observedSendQueuedRetry pid; pure ()) = sendQueuedHandshakeInitiation pid true := by
  rw [sendQueuedRetry_factor]
  simp only [observedSendQueuedRetry, bind_assoc, pure_bind]
  congr 1
  funext p
  congr 1
  funext now
  exact observedQueuedAfterClock_erase pid p now

/-- Corrected exact retry effect, indexed by this call's actual clock and queue
inspection. The original resident-only, normal-return domain is unchanged. -/
theorem sendQueuedRetry_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (observedSendQueuedRetry pid) (fun s => s.wg.device = some d)
      (fun result s => match result.2 with
        | none => s.wg.device = some d ∧
            (¬p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ result.1 ∨ p.isDead = true)
        | some queued => p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ result.1 ∧
            p.isDead = false ∧ s.wg.device = some (queuedDeviceAfterInspection d pid p result.1 queued)) := by
  intro g ambient result final ending device run
  change g.dev = some d at device
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
      exact queuedAfterClock_exact pid d p now resident
        afterClock clockAmbient seen complete after clockDevice observedRun

def retryAt (g : WGWorld) (pid : PeerId) : Option RetryView :=
  (peerAt g pid).map retryView

end Leanux.Proofs.WG.TimerDiscipline
