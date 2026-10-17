import Leanux.Proofs.WG.Progress.CookieActivationSource
import Leanux.Proofs.WG.Progress.CookieRingFindings

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- A correctly sized receive section-stop record, with no reschedule before it. -/
def cookieBadTailStopRecords : List HiddenRecord :=
  [{site := (HiddenSite.sectionStop .receiveWorker).info.id, bytes := List.replicate 8 0}]

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

/-- An actual activation exhausts its occupancy-derived fuel. The ring's
consumer tail is malformed; no reachable-state or kernel-bug claim is made. -/
theorem cookieBadTail_activation_run (a : Activation) (w : World) (d : Device)
    (msg : List UInt8) (src : SkbSource) (receive : a.worker = .receiveWorker)
    (device : w.wg.dev = some d) (queue : d.handshakeQueue = cookieBadTailRing msg src)
    (table : d.indexTable = []) (cookie : messageType msg = MESSAGE_HANDSHAKE_COOKIE)
    (present : w.ambient.hidden = some cookieBadTailStopRecords) :
    (Activation.run a).run w = .error (.invariant
      "wg_packet_handshake_receive_worker consumed more items than its queue held (1) in one run") := by
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
      rfl
    rw [read]
    simp [receive, queue, cookieBadTailRing, PtrRing.count, PtrRing.peek]
    rfl
  rw [activation_run_source, StateT.run_bind, occupancy]
  change ((do let state ← activationLoopSource [0, 1] a
              activationFinishSource a 1 state).run w) = _
  simp only [activationLoopSource, List.forIn_cons, activationStepSource, StateT.run_bind]
  rw [iter1]
  change ((do let state ← activationLoopSource [1] a1
              activationFinishSource a 1 state).run w1) = _
  simp only [activationLoopSource, List.forIn_cons, activationStepSource, StateT.run_bind]
  rw [iter2]
  simp only [Bind.bind, Except.bind, List.forIn_nil, activationFinishSource, receive]
  rfl

end Leanux.Proofs.WG.Progress
