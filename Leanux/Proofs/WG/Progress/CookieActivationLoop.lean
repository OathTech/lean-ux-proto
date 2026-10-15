import Leanux.Proofs.WG.Progress.CookieActivationSource
import Leanux.Proofs.WG.Campaign2.Bridge
/-! Original loop adequacy for the closed cookie-only, empty-index queue domain. The induction threads every actual intermediate state and needs only queue length plus one turns. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

def cookieActivationWorld (a : Activation) (w : World) (d : Device)
    (summary : CookieActivationSummary) : World :=
  {w with
    k := {w.k with wg := some {d with
      handshakeQueue := d.handshakeQueue.drop summary.processed
      handshakeQueueLen := d.handshakeQueueLen - summary.processed}}
    hidden := some summary.rest
    suspended := if summary.yielded then
      w.suspended ++ [{a with iterations := a.iterations + summary.processed}]
      else w.suspended
    steps := cookieFinalSteps w.netRxSection summary w.steps}

theorem cookieActivationWorld_continue (a : Activation) (w : World) (d : Device)
    (msg : List UInt8) (src : SkbSource) (rest : List (List UInt8 × SkbSource))
    (records : List HiddenRecord) (summary : CookieActivationSummary)
    (queue : d.handshakeQueue = (msg,src)::rest) :
    cookieActivationWorld {a with iterations := a.iterations+1}
      {cookieMissStepView w d rest with hidden := some records} (cookieTailDevice d) summary =
    cookieActivationWorld a w d {summary with processed := summary.processed+1} := by
  simp [cookieActivationWorld, cookieMissStepView, cookieTailDevice, cookieFinalSteps,
    cookieProcessedSteps, cookiePacketSteps, queue, Nat.sub_sub,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem cookieLoop_run (turns : List Nat) (a : Activation) (w : World) (d : Device)
    (records : List HiddenRecord) (receive : a.worker = .receiveWorker)
    (device : w.k.wg = some d) (table : d.indexTable = []) (cookies : CookieOnly d)
    (present : w.hidden = some records) (fuel : d.handshakeQueue.length+1 ≤ turns.length) :
    match resolveCookieActivation d.handshakeQueue.length records with
    | .error error => (activationLoopSource turns a).run w = .error error
    | .ok summary => ∃ finalAct,
        (activationLoopSource turns a).run w =
          .ok ((some (), finalAct), cookieActivationWorld a w d summary) := by
  induction turns generalizing a w d records with
  | nil => simp at fuel
  | cons turn turns ih =>
    cases queue : d.handshakeQueue with
    | nil =>
      simp only [queue, List.length_nil, resolveCookieActivation]
      have iter := cookieEmptyIter_run a receive w d device queue
      have read := hidden_cookie_control false
        {w with steps := w.steps.push {decision := .workerConsumed, outcome := false, netRx := w.netRxSection}}
        records present
      simp only [cookieControlSite, Bool.false_eq_true, ite_false] at read
      simp only [activationLoopSource, List.forIn_cons, activationStepSource, StateT.run_bind]
      rw [iter]
      simp only [bind, Except.bind, receive]
      simp only [StateT.run, StateT.bind] at read ⊢
      rw [read]
      cases result : resolveCookieRead false records with
      | error error => rfl
      | ok pair =>
        rcases pair with ⟨bytes, rest⟩
        refine ⟨a, ?_⟩
        simp [cookieActivationWorld, cookieFinalSteps, cookieProcessedSteps, pure, StateT.pure, Except.pure, ← device]
    | cons packet rest =>
      rcases packet with ⟨msg, src⟩
      have cookie := cookies msg src (by simp [queue])
      have iter := cookieIter_run a receive w d msg src rest records device queue table cookie present
      simp only [queue, List.length_cons, resolveCookieActivation]
      simp only [activationLoopSource, List.forIn_cons, activationStepSource, StateT.run_bind]
      rw [iter]
      cases result : cookieReschedResult records with
      | error error => rfl
      | ok pair =>
        rcases pair with ⟨yielded, tail⟩
        cases yielded with
        | true =>
          refine ⟨a, ?_⟩
          simp [cookieActivationWorld, cookieMissStepView, cookieFinalSteps, cookieProcessedSteps,
            cookiePacketSteps, queue, pure, bind, StateT.run, StateT.bind, StateT.pure,
            modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, Except.pure]
        | false =>
          have nextCookies : CookieOnly (cookieTailDevice d) := by
            intro m s member
            apply cookies m s
            simp only [cookieTailDevice, queue, List.drop_succ_cons, List.drop_zero] at member
            simp [queue, member]
          have nextFuel : (cookieTailDevice d).handshakeQueue.length+1 ≤ turns.length := by
            simp [cookieTailDevice, queue] at fuel ⊢
            omega
          have next := ih {a with iterations := a.iterations+1}
            {cookieMissStepView w d rest with hidden := some tail} (cookieTailDevice d) tail
            receive (by simp [cookieMissStepView, cookieTailDevice, queue]) table nextCookies rfl nextFuel
          simp only [cookieTailDevice, queue, List.drop_succ_cons, List.drop_zero] at next
          dsimp only at ⊢
          cases resolved : resolveCookieActivation rest.length tail with
          | error error =>
            simp only [resolved] at next
            simp only [cookieIncrement, Except.map]
            change (activationLoopSource turns {a with iterations := a.iterations+1}).run
              {cookieMissStepView w d rest with hidden := some tail} = Except.error error
            exact next
          | ok summary =>
            simp only [resolved] at next
            simp only [cookieIncrement, Except.map]
            rcases next with ⟨finalAct, next⟩
            refine ⟨finalAct, ?_⟩
            change (activationLoopSource turns {a with iterations := a.iterations+1}).run
              {cookieMissStepView w d rest with hidden := some tail} = _
            rw [next]
            congr 2
            simpa only [cookieTailDevice, queue, List.drop_succ_cons, List.drop_zero] using
              cookieActivationWorld_continue a w d msg src rest tail summary queue

theorem cookieActivation_run (a : Activation) (w : World) (d : Device)
    (records : List HiddenRecord) (receive : a.worker = .receiveWorker)
    (device : w.k.wg = some d) (table : d.indexTable = []) (cookies : CookieOnly d)
    (present : w.hidden = some records) :
    (Activation.run a).run w =
      match resolveCookieActivation d.handshakeQueue.length records with
      | .error error => .error error
      | .ok summary => .ok ((), cookieActivationWorld a w d summary) := by
  have occupancy : (Activation.occupancy a).run w = .ok (d.handshakeQueue.length, w) := by
    simp [Activation.occupancy, receive, getDev, getK, StateT.run, bind, pure,
      get, getThe, MonadStateOf.get, StateT.bind, StateT.pure, StateT.get,
      Except.pure, Except.bind, device]
  have loop := cookieLoop_run (List.range' 0 (d.handshakeQueue.length+1)) a w d records
    receive device table cookies present (by simp)
  rw [activation_run_source, StateT.run_bind, occupancy]
  change ((do let state ← activationLoopSource (List.range' 0 (d.handshakeQueue.length+1)) a
              activationFinishSource a d.handshakeQueue.length state).run w) = _
  rw [StateT.run_bind]
  cases result : resolveCookieActivation d.handshakeQueue.length records with
  | error error =>
    simp only [result] at loop
    rw [loop]
    rfl
  | ok summary =>
    simp only [result] at loop
    rcases loop with ⟨finalAct, loop⟩
    rw [loop]
    rfl

end Leanux.Proofs.WG.Progress
