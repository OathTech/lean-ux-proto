import Leanux.Proofs.WG.Progress.CookieActivationSource
import Leanux.Proofs.WG.Progress.CookieRingFindings

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- A correctly sized receive section-stop record, with no reschedule before it. -/
def cookieBadTailStopRecords : List HiddenRecord :=
  [{site := (HiddenSite.sectionStop .receiveWorker).info.id, bytes := List.replicate 8 0}]

/-- Current physical endpoint after the two productive polls and the empty poll
of this fixed malformed ring. The supplied section-stop record is consumed. -/
def cookieBadTailFinal (w : World) (d : Device) : World :=
  let d1 := cookieRingTailDevice d
  let w1 := {cookieMissStepView w d d.handshakeQueue.consume.2 with
    ambient := {(cookieMissStepView w d d.handshakeQueue.consume.2).ambient with
      hidden := some cookieBadTailStopRecords}}
  let w2 := {cookieMissStepView w1 d1 d1.handshakeQueue.consume.2 with
    ambient := {(cookieMissStepView w1 d1 d1.handshakeQueue.consume.2).ambient with
      hidden := some cookieBadTailStopRecords}}
  {w2 with ambient := {w2.ambient with
    hidden := some []
    steps := w2.ambient.steps.push {decision := .workerConsumed, outcome := false, netRx := w2.ambient.netRxSection}}}

/-- The count-only resolver predicts a completed one-packet activation, but the
malformed ring needs two productive polls before it first becomes empty. -/
theorem cookieBadTail_resolver_contrast (msg : List UInt8) (src : SkbSource) :
    (cookieBadTailRing msg src).count = 1 ∧
    (cookieRingAfter 1 (cookieBadTailRing msg src)).peek = some (msg, src) ∧
    (cookieRingAfter 2 (cookieBadTailRing msg src)).empty = true ∧
    resolveCookieActivation (cookieBadTailRing msg src).count cookieBadTailStopRecords =
      .ok ⟨1, false, []⟩ := by
  simp [cookieBadTailRing, cookieRingAfter, PtrRing.count, PtrRing.consume,
    PtrRing.peek, PtrRing.empty, PtrRing.discardOne, PtrRing.discardOne.clear,
    cookieBadTailStopRecords, resolveCookieActivation, cookieReschedResult,
    cookieNext, resolveCookieRead, cookieControlSite, cookieIncrement,
    HiddenSite.info, HiddenSite.passive, Worker.sectionId, Worker.index]
  rfl

/-- The current refill-aware budget completes this historical malformed-tail
witness. This is an arbitrary-state regression, not a reachability claim. -/
theorem cookieBadTail_activation_run (a : Activation) (w : World) (d : Device)
    (msg : List UInt8) (src : SkbSource) (receive : a.worker = .receiveWorker)
    (device : w.wg.dev = some d) (queue : d.handshakeQueue = cookieBadTailRing msg src)
    (table : d.indexTable = []) (cookie : messageType msg = MESSAGE_HANDSHAKE_COOKIE)
    (present : w.ambient.hidden = some cookieBadTailStopRecords) :
    (Activation.run a).run w = .ok ((), cookieBadTailFinal w d) := by
  have resched : cookieReschedResult cookieBadTailStopRecords =
      .ok (false, cookieBadTailStopRecords) := by rfl
  have first : d.handshakeQueue.consume.1 = some (msg, src) := by
    simp [queue, cookieBadTailRing, PtrRing.consume, PtrRing.peek]
  let d1 := cookieRingTailDevice d
  let w1 := {cookieMissStepView w d d.handshakeQueue.consume.2 with
    ambient := {(cookieMissStepView w d d.handshakeQueue.consume.2).ambient with
      hidden := some cookieBadTailStopRecords}}
  let a1 := {a with iterations := a.iterations + 1}
  have iter1 : (Activation.iter a).run w = .ok (.continued, w1) := by
    have step := cookieIter_run a receive w d msg src d.handshakeQueue.consume.2
      cookieBadTailStopRecords device (Prod.ext first rfl) table cookie present
    rw [resched] at step
    exact step
  have second : d1.handshakeQueue.consume.1 = some (msg, src) := by
    simp [d1, cookieRingTailDevice, queue, cookieBadTailRing, PtrRing.consume,
      PtrRing.peek, PtrRing.discardOne, PtrRing.discardOne.clear]
  let w2 := {cookieMissStepView w1 d1 d1.handshakeQueue.consume.2 with
    ambient := {(cookieMissStepView w1 d1 d1.handshakeQueue.consume.2).ambient with
      hidden := some cookieBadTailStopRecords}}
  have iter2 : (Activation.iter a1).run w1 = .ok (.continued, w2) := by
    have step := cookieIter_run a1 receive w1 d1 msg src d1.handshakeQueue.consume.2
      cookieBadTailStopRecords rfl (Prod.ext second rfl) table cookie rfl
    rw [resched] at step
    exact step
  have occupancy : (Activation.occupancy a).run w = .ok (1, w) := by
    change ((liftM getDev : Leanux.M Device).run w >>= _) = _
    have read : (liftM getDev : Leanux.M Device).run w = .ok (d, w) := by
      change (((getDev.run w.wg).run w.ambient) >>= _) = _
      simp [getDev, device]
    rw [read]
    simp [receive, queue, cookieBadTailRing, PtrRing.count, PtrRing.peek]
    rfl
  let extra := d.peers.toList.countP (fun pair : PeerId × Peer => pair.2.napiScheduled) * NAPI_POLL_WEIGHT
  have refill : Activation.refills.run w = .ok (1 + extra, w) := by
    have read := RecordSuffix.activationRefills_run w d device
    rw [present] at read
    exact read
  let d2 := cookieRingTailDevice d1
  let a2 := {a1 with iterations := a1.iterations + 1}
  have empty : d2.handshakeQueue.peek = none := by
    simp [d2, d1, cookieRingTailDevice, queue, cookieBadTailRing, PtrRing.consume,
      PtrRing.peek, PtrRing.discardOne, PtrRing.discardOne.clear]
  let w3 := {w2 with ambient := {w2.ambient with
    steps := w2.ambient.steps.push {decision := .workerConsumed, outcome := false, netRx := w2.ambient.netRxSection}}}
  have iter3 : (Activation.iter a2).run w2 = .ok (.ended, w3) :=
    cookieEmptyIter_run a2 receive w2 d2 rfl empty
  have stopped : (hidden (.sectionStop a2.worker) : Leanux.M (List UInt8)).run w3 =
      .ok (List.replicate 8 0, cookieBadTailFinal w d) := by
    have read := hidden_cookie_control false w3 cookieBadTailStopRecords rfl
    change (hidden (.sectionStop .receiveWorker) : Leanux.M (List UInt8)).run w3 =
      .ok (List.replicate 8 0, cookieBadTailFinal w d) at read
    simpa only [a2, a1, receive] using read
  rw [activation_run_source, StateT.run_bind, occupancy]
  change (Activation.refills.run w >>= _) = _
  rw [refill]
  change ((do let state ← activationLoopSource (List.range' 0 (1 + (1 + extra) + 1)) a
              activationFinishSource a 1 (1 + extra) state).run w) = _
  rw [show 1 + (1 + extra) + 1 = extra + 3 by omega]
  simp only [activationLoopSource, List.range'_succ, List.forIn_cons,
    activationStepSource, StateT.run_bind]
  dsimp only [StateT.run, StateT.bind, StateT.pure, Except.pure, Bind.bind, Pure.pure,
    Except.bind] at iter1 iter2 iter3 stopped ⊢
  rw [iter1]
  dsimp only [StateT.run, StateT.bind, StateT.pure, Except.pure, Bind.bind, Pure.pure, Except.bind]
  rw [iter2]
  dsimp only [StateT.run, StateT.bind, StateT.pure, Except.pure, Bind.bind, Pure.pure, Except.bind]
  rw [iter3]
  dsimp only [StateT.run, StateT.bind, StateT.pure, Except.pure, Bind.bind, Pure.pure, Except.bind]
  rw [stopped]
  rfl

end Leanux.Proofs.WG.Progress
