import Leanux.Proofs.WG.Progress.CookieControlSource
import Leanux.Proofs.WG.Progress.ActivationRefillFrames
import Leanux.Proofs.WG.Progress.CookieRingSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

def cookieMissStepView (w : World) (d : Device) (rest : PtrRing (List UInt8 × SkbSource)) : World :=
  { w with
    wg := {w.wg with dev := some {d with handshakeQueue := rest, handshakeQueueLen := d.handshakeQueueLen - 1}}
    ambient := {w.ambient with steps := cookiePacketSteps w.ambient.netRxSection w.ambient.steps} }

theorem receiveStep_cookieMiss (w : World) (d : Device) (msg : List UInt8) (src : SkbSource)
    (rest : PtrRing (List UInt8 × SkbSource)) (device : w.wg.dev = some d)
    (queue : d.handshakeQueue.consume = (some (msg,src), rest)) (table : d.indexTable = [])
    (cookie : messageType msg = MESSAGE_HANDSHAKE_COOKIE) :
    (liftM receiveStep : Leanux.M Bool).run w = .ok (true, cookieMissStepView w d rest) := by
  have step := receiveStep_cookieMiss_ring w.wg w.ambient d msg src rest device queue table cookie
  change (((receiveStep.run w.wg).run w.ambient) >>= _) = _
  rw [step]
  rfl

theorem cookieIter_run (a : Activation) (receive : a.worker = .receiveWorker)
    (w : World) (d : Device) (msg : List UInt8) (src : SkbSource)
    (rest : PtrRing (List UInt8 × SkbSource)) (records : List HiddenRecord)
    (device : w.wg.dev = some d) (queue : d.handshakeQueue.consume = (some (msg,src), rest))
    (table : d.indexTable = []) (cookie : messageType msg = MESSAGE_HANDSHAKE_COOKIE)
    (present : w.ambient.hidden = some records) :
    (Activation.iter a).run w =
      match cookieReschedResult records with
      | .error error => .error error
      | .ok (yielded, tail) => .ok
          ((if yielded then .yielded else .continued),
           {cookieMissStepView w d rest with ambient := {(cookieMissStepView w d rest).ambient with hidden := some tail}}) := by
  simp only [Activation.iter, receive, workerIter]
  rw [StateT.run_bind, receiveStep_cookieMiss w d msg src rest device queue table cookie]
  change ((do if !true then return IterResult.ended
              return if ← condResched .receiveWorker then .yielded else .continued : Leanux.M IterResult).run
              (cookieMissStepView w d rest)) = _
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [StateT.run_bind, cookieResched_run (cookieMissStepView w d rest) records present]
  cases cookieReschedResult records with
  | error error => rfl
  | ok pair => rcases pair with ⟨yielded, tail⟩; rfl

theorem cookieEmptyStep_run (w : World) (d : Device)
    (device : w.wg.dev = some d) (empty : d.handshakeQueue.peek = none) :
    (liftM receiveStep : Leanux.M Bool).run w = .ok (false, {w with ambient := {w.ambient with
      steps := w.ambient.steps.push {decision := .workerConsumed, outcome := false, netRx := w.ambient.netRxSection}}}) := by
  change (((receiveStep.run w.wg).run w.ambient) >>= _) = _
  simp [receiveStep, getDev, PtrRing.consume, device, empty, branch, AmbientM.branch]

theorem cookieEmptyIter_run (a : Activation) (receive : a.worker = .receiveWorker)
    (w : World) (d : Device) (device : w.wg.dev = some d) (empty : d.handshakeQueue.peek = none) :
    (Activation.iter a).run w = .ok (.ended, {w with ambient := {w.ambient with
      steps := w.ambient.steps.push {decision := .workerConsumed, outcome := false, netRx := w.ambient.netRxSection}}}) := by
  simp only [Activation.iter, receive, workerIter]
  rw [StateT.run_bind, cookieEmptyStep_run w d device empty]
  rfl

theorem cookieEmptyActivation_run (a : Activation) (receive : a.worker = .receiveWorker)
    (w : World) (d : Device) (records : List HiddenRecord)
    (device : w.wg.dev = some d) (empty : d.handshakeQueue.peek = none)
    (present : w.ambient.hidden = some records) :
    (Activation.run a).run w =
      match resolveCookieRead false records with
      | .error error => .error error
      | .ok (_, rest) => .ok ((), {w with ambient := {w.ambient with
          hidden := some rest
          steps := w.ambient.steps.push {decision := .workerConsumed, outcome := false, netRx := w.ambient.netRxSection}}}) := by
  have occupancy : (Activation.occupancy a).run w = .ok (d.handshakeQueue.count, w) := by
    change ((liftM getDev : Leanux.M Device).run w >>= _) = _
    have read : (liftM getDev : Leanux.M Device).run w = .ok (d, w) := by
      change (((getDev.run w.wg).run w.ambient) >>= _) = _
      simp [getDev, device]
    rw [read]
    simp [receive]
    rfl
  have refill := RecordSuffix.activationRefills_run w d device
  rw [present] at refill
  simp only [Option.map_some, Option.getD_some] at refill
  rw [activation_run_source, StateT.run_bind, occupancy]
  change ((do
    let refills ← Activation.refills
    let state ← activationLoopSource (List.range' 0 (d.handshakeQueue.count + refills + 1)) a
    activationFinishSource a d.handshakeQueue.count refills state).run w) = _
  rw [StateT.run_bind, refill]
  change ((do let state ← activationLoopSource (List.range' 0
                (d.handshakeQueue.count + (records.length +
                  d.peers.toList.countP (fun pair : PeerId × Peer => pair.2.napiScheduled) * NAPI_POLL_WEIGHT) + 1)) a
              activationFinishSource a d.handshakeQueue.count
                (records.length + d.peers.toList.countP (fun pair : PeerId × Peer => pair.2.napiScheduled) * NAPI_POLL_WEIGHT)
                state).run w) = _
  simp only [activationLoopSource, List.range'_succ, List.forIn_cons, activationStepSource, StateT.run_bind]
  rw [cookieEmptyIter_run a receive w d device empty]
  simp only [Bind.bind, Except.bind]
  rw [receive]
  have read := hidden_cookie_control false
    {w with ambient := {w.ambient with steps := (w.ambient.steps.push
      {decision := .workerConsumed, outcome := false, netRx := w.ambient.netRxSection})}}
    records present
  simp only [cookieControlSite, Bool.false_eq_true, ite_false] at read
  simp only [StateT.run, StateT.bind] at read ⊢
  rw [read]
  cases resolveCookieRead false records with
  | error error => rfl
  | ok pair => rcases pair with ⟨bytes, rest⟩; rfl

end Leanux.Proofs.WG.Progress
