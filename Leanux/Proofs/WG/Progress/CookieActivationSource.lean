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
theorem hidden_cookie_control (yielded : Bool) (w : World) (records : List HiddenRecord)
    (present : w.hidden = some records) :
    (hidden (cookieControlSite yielded)).run w =
      match resolveCookieRead yielded records with
      | .error error => .error error
      | .ok (bytes, rest) => .ok (bytes, {w with hidden := some rest}) := by
  cases yielded <;> cases stripped : records.dropWhile (fun r => HiddenSite.passive r.site) with
  | nil =>
    simp [hidden, skipAmbient, noteNetRxStart, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
      present, HiddenSite.info, cookieControlSite, Worker.sectionId, Worker.index, Except.pure, Except.bind,
      resolveCookieRead, stripped]
    rfl
  | cons record rest =>
    simp [hidden, skipAmbient, noteNetRxStart, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
      present, HiddenSite.info, cookieControlSite, Worker.sectionId, Worker.index, Except.pure, Except.bind,
      resolveCookieRead, stripped]
    split <;> (try rfl)
    split <;> rfl

theorem cookiePeek_run (w : World) (records : List HiddenRecord)
    (present : w.hidden = some records) :
    peekHiddenSite.run w = .ok
      (((records.dropWhile (fun r => HiddenSite.passive r.site)).head?).map (·.site),
       {w with hidden := some (records.dropWhile (fun r => HiddenSite.passive r.site))}) := by
  simp [peekHiddenSite, skipAmbient, StateT.run, bind, pure,
    get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
    present, Except.pure, Except.bind]
  cases records.dropWhile (fun r => HiddenSite.passive r.site) <;> rfl

theorem cookieResched_run (w : World) (records : List HiddenRecord)
    (present : w.hidden = some records) :
    (condResched .receiveWorker).run w =
      match cookieReschedResult records with
      | .error error => .error error
      | .ok (yielded, rest) => .ok (yielded, {w with hidden := some rest}) := by
  simp only [condResched, Worker.resched?]
  rw [StateT.run_bind, cookiePeek_run w records present]
  change ((if cookieNext records != some HiddenSite.reschedReceive.info.id then pure false else
    do let _ ← hidden .reschedReceive; pure true).run
      {w with hidden := some (records.dropWhile (fun r => HiddenSite.passive r.site))}) = _
  by_cases next : cookieNext records = some HiddenSite.reschedReceive.info.id
  · simp only [next, bne_self_eq_false, Bool.false_eq_true, ite_false]
    have read := hidden_cookie_control true
      {w with hidden := some (records.dropWhile (fun r => HiddenSite.passive r.site))}
      (records.dropWhile (fun r => HiddenSite.passive r.site)) rfl
    simp only [cookieControlSite, ite_true] at read
    rw [StateT.run_bind, read]
    unfold cookieReschedResult
    rw [ite_eq_left next]
    cases resolveCookieRead true (records.dropWhile (fun r => HiddenSite.passive r.site)) with
    | error error => rfl
    | ok pair => rcases pair with ⟨bytes, rest⟩; rfl
  · have different : (cookieNext records != some HiddenSite.reschedReceive.info.id) = true := by
      simp [next]
    rw [different]
    simp only [ite_true, cookieReschedResult, ite_eq_right next]
    rfl

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

def activationStepSource (_ : Nat) (state : Option Unit × Activation) :
    M (ForInStep (Option Unit × Activation)) := do
  let act := state.2
  match ← Activation.iter act with
  | .ended =>
    let _ ← hidden (.sectionStop act.worker)
    pure (.done (some (), act))
  | .continued => pure (.yield (none, {act with iterations := act.iterations + 1}))
  | .yielded =>
    modify fun s => {s with suspended := s.suspended ++ [{act with iterations := act.iterations + 1}]}
    pure (.done (some (), act))

def activationFinishSource (a : Activation) (occupancy : Nat) (state : Option Unit × Activation) : M Unit :=
  match state.1 with
  | some u => pure u
  | none => invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) in one run"

def activationLoopSource (turns : List Nat) (a : Activation) : M (Option Unit × Activation) :=
  forIn turns (none, a) activationStepSource

theorem activation_run_source (a : Activation) :
    Activation.run a = (do
      let occupancy ← Activation.occupancy a
      let state ← activationLoopSource (List.range' 0 (occupancy + 1)) a
      activationFinishSource a occupancy state) := by
  unfold activationLoopSource activationStepSource activationFinishSource
  simp [Activation.run, Std.Legacy.Range.forIn_eq_forIn_range']
  congr 1
  funext occupancy
  congr 1
  funext state
  rcases state with ⟨result, act⟩
  cases result <;> rfl

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
