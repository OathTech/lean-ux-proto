import Leanux.Proofs.WG.Progress.CookieControlSource
import Leanux.Proofs.WG.Progress.CookieActivationModel
import Leanux.Proofs.WG.Index.LookupSource
/-! Source equations for the unchanged receive worker and its original activation loop. These concrete helpers connect the projected model to the actual monadic execution. -/

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Index
def cookieMissStepView (w : World) (d : Device) (rest : List (List UInt8 × SkbSource)) : World :=
  { w with
    k := { w.k with wg := some {d with handshakeQueue := rest, handshakeQueueLen := d.handshakeQueueLen - 1} }
    steps := ((((w.steps.push {decision := .workerConsumed, outcome := true, netRx := w.netRxSection}).push
      {decision := .hsCookie, outcome := true, netRx := w.netRxSection}).push
      {decision := .idxWalk, outcome := false, netRx := w.netRxSection}).push
      {decision := .idxFound, outcome := false, netRx := w.netRxSection}).push
      {decision := .cookieLookupMiss, outcome := true, netRx := w.netRxSection} }
theorem receiveStep_cookieMiss (w : World) (d : Device) (msg : List UInt8) (src : SkbSource)
    (rest : List (List UInt8 × SkbSource)) (device : w.k.wg = some d)
    (queue : d.handshakeQueue = (msg,src)::rest) (table : d.indexTable = [])
    (cookie : messageType msg = MESSAGE_HANDSHAKE_COOKIE) :
    receiveStep.run w = .ok (true, cookieMissStepView w d rest) := by
  simp [receiveStep, receiveHandshakePacket, cookieMessageConsume,
    indexLookup_source, lookupFinish, indexBucket, getDev, getK, modifyDev, modifyK,
    branch, StateT.run, bind, pure, get, getThe, MonadStateOf.get, set,
    StateT.bind, StateT.pure, StateT.get, StateT.set, StateT.modifyGet, modify, modifyGet, MonadStateOf.modifyGet,
    Except.pure, Except.bind, device, queue, table, cookie, cookieMissStepView,
    List.forIn_nil]
theorem cookieIter_run (a : Activation) (receive : a.worker = .receiveWorker)
    (w : World) (d : Device) (msg : List UInt8) (src : SkbSource)
    (rest : List (List UInt8 × SkbSource)) (records : List HiddenRecord)
    (device : w.k.wg = some d) (queue : d.handshakeQueue = (msg,src)::rest)
    (table : d.indexTable = []) (cookie : messageType msg = MESSAGE_HANDSHAKE_COOKIE)
    (present : w.hidden = some records) :
    (Activation.iter a).run w =
      match cookieReschedResult records with
      | .error error => .error error
      | .ok (yielded, tail) => .ok
          ((if yielded then .yielded else .continued),
           {cookieMissStepView w d rest with hidden := some tail}) := by
  simp only [Activation.iter, receive, workerIter]
  rw [StateT.run_bind, receiveStep_cookieMiss w d msg src rest device queue table cookie]
  change ((do if !true then return IterResult.ended
              return if ← condResched .receiveWorker then .yielded else .continued).run
              (cookieMissStepView w d rest)) = _
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [StateT.run_bind, cookieResched_run (cookieMissStepView w d rest) records present]
  cases cookieReschedResult records with
  | error error => rfl
  | ok pair => rcases pair with ⟨yielded, tail⟩; rfl

theorem cookieEmptyStep_run (w : World) (d : Device)
    (device : w.k.wg = some d) (empty : d.handshakeQueue = []) :
    receiveStep.run w = .ok (false, {w with steps := w.steps.push {decision := .workerConsumed, outcome := false, netRx := w.netRxSection}}) := by
  simp [receiveStep, getDev, getK, branch, StateT.run, bind, pure,
    get, getThe, MonadStateOf.get, StateT.bind, StateT.pure, StateT.get, StateT.modifyGet,
    modify, modifyGet, MonadStateOf.modifyGet, Except.pure, Except.bind, device, empty]

theorem cookieEmptyIter_run (a : Activation) (receive : a.worker = .receiveWorker)
    (w : World) (d : Device) (device : w.k.wg = some d) (empty : d.handshakeQueue = []) :
    (Activation.iter a).run w = .ok (.ended, {w with steps := w.steps.push {decision := .workerConsumed, outcome := false, netRx := w.netRxSection}}) := by
  simp only [Activation.iter, receive, workerIter]
  rw [StateT.run_bind, cookieEmptyStep_run w d device empty]
  rfl

theorem cookieEmptyActivation_run (a : Activation) (receive : a.worker = .receiveWorker)
    (w : World) (d : Device) (records : List HiddenRecord)
    (device : w.k.wg = some d) (empty : d.handshakeQueue = [])
    (present : w.hidden = some records) :
    (Activation.run a).run w =
      match resolveCookieRead false records with
      | .error error => .error error
      | .ok (_, rest) => .ok ((), {w with
          hidden := some rest
          steps := w.steps.push {decision := .workerConsumed, outcome := false, netRx := w.netRxSection}}) := by
  have occupancy : (Activation.occupancy a).run w = .ok (0, w) := by
    simp [Activation.occupancy, receive, getDev, getK, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, StateT.bind, StateT.pure, StateT.get,
      Except.pure, Except.bind, device, empty]
  rw [activation_run_source, StateT.run_bind, occupancy]
  change ((do let state ← activationLoopSource [0] a; activationFinishSource a 0 state).run w) = _
  simp only [activationLoopSource, List.forIn_cons, activationStepSource, StateT.run_bind]
  rw [cookieEmptyIter_run a receive w d device empty]
  simp only [bind, Except.bind]
  rw [receive]
  have read := hidden_cookie_control false
    {w with steps := w.steps.push {decision := .workerConsumed, outcome := false, netRx := w.netRxSection}}
    records present
  simp only [cookieControlSite, Bool.false_eq_true, ite_false] at read
  simp only [StateT.run, StateT.bind] at read ⊢
  rw [read]
  cases resolveCookieRead false records with
  | error error => rfl
  | ok pair => rcases pair with ⟨bytes, rest⟩; rfl

end Leanux.Proofs.WG.Progress
