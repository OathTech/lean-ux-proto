import Leanux.Proofs.WG.Progress.CookieActivationSource
import Leanux.Proofs.WG.Progress.CookieDomain

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Optimize only the currently observed cookie-miss leaf. Every other physical
packet, table, and absent-device case executes the actual receive operation. -/
def cookieHybridReceive : WG.M Bool := fun g ambient =>
  match g.dev with
  | none => (receiveStep.run g).run ambient
  | some d =>
    match d.handshakeQueue.consume with
    | (none, _) => (receiveStep.run g).run ambient
    | (some (msg, _src), rest) =>
      if d.indexTable = [] ∧ messageType msg = MESSAGE_HANDSHAKE_COOKIE then
        .ok ((true, {g with dev := some {d with handshakeQueue := rest, handshakeQueueLen := d.handshakeQueueLen - 1}}),
          {ambient with steps := cookiePacketSteps ambient.netRxSection ambient.steps})
      else (receiveStep.run g).run ambient

private theorem cookieHybridReceive_eq : cookieHybridReceive = receiveStep := by
  funext g ambient
  dsimp only [cookieHybridReceive]
  cases device : g.dev with
  | none => rfl
  | some d =>
    dsimp only
    cases queue : d.handshakeQueue.consume with
    | mk packet rest =>
      cases packet with
      | none => rfl
      | some pair =>
        obtain ⟨msg, src⟩ := pair
        dsimp only
        by_cases selected : d.indexTable = [] ∧ messageType msg = MESSAGE_HANDSHAKE_COOKIE
        · rw [ite_eq_left selected]
          exact (receiveStep_cookieMiss_ring g ambient d msg src rest device queue
            selected.1 selected.2).symm
        · rw [ite_eq_right selected]
          rfl

def cookieHybridIteration (_a : Activation) (w : World) : Except Stop (IterResult × World) := do
  let (productive, after) ← (liftWG cookieHybridReceive).run w
  if !productive then return (.ended, after)
  let (yielded, afterResched) ← (condResched .receiveWorker).run after
  return ((if yielded then .yielded else .continued), afterResched)

private theorem cookieHybridIteration_eq (a : Activation)
    (receive : a.worker = .receiveWorker) (w : World) :
    (Activation.iter a).run w = cookieHybridIteration a w := by
  rw [cookieHybridIteration, cookieHybridReceive_eq]
  simp only [Activation.iter, receive, workerIter, StateT.run_bind]
  cases executed : (liftWG receiveStep).run w with
  | error stop => rfl
  | ok pair =>
    obtain ⟨productive, after⟩ := pair
    cases productive <;> rfl

/-- Zero fuel returns the uncompleted activation without polling. Productive
continuations consume one unit of fuel. End and yield use the actual control
operations; arbitrary receive and record errors are retained verbatim. -/
def cookieHybridLoop : Nat → Activation → World → Except Stop ((Option Unit × Activation) × World)
  | 0, a, w => .ok ((none, a), w)
  | fuel + 1, a, w => do
    let (result, after) ← cookieHybridIteration a w
    match result with
    | .ended =>
      let (_, stopped) ← (hidden (.sectionStop a.worker) : Leanux.M _).run after
      return ((some (), a), stopped)
    | .continued => cookieHybridLoop fuel {a with iterations := a.iterations + 1} after
    | .yielded =>
      return ((some (), a), {after with ambient := {after.ambient with
        suspended := after.ambient.suspended ++ [{a with iterations := a.iterations + 1}]}})

private theorem cookieHybridLoop_eq (turns : List Nat) (a : Activation) (w : World)
    (receive : a.worker = .receiveWorker) :
    (activationLoopSource turns a).run w = cookieHybridLoop turns.length a w := by
  induction turns generalizing a w with
  | nil => rfl
  | cons turn turns ih =>
    simp only [activationLoopSource, activationLoopSourceWith, List.forIn_cons, activationStepSourceWith,
      StateT.run_bind, List.length_cons, cookieHybridLoop]
    rw [cookieHybridIteration_eq a receive w]
    cases executed : cookieHybridIteration a w with
    | error stop => rfl
    | ok pair =>
      obtain ⟨result, after⟩ := pair
      cases result with
      | ended =>
        simp only [bind, Except.bind, StateT.run, StateT.bind]
        cases stopped : (hidden (.sectionStop a.worker) : Leanux.M _).run after with
        | error stop => rw [show (hidden (.sectionStop a.worker) : Leanux.M _) after = .error stop from stopped]
        | ok pair =>
          obtain ⟨bytes, final⟩ := pair
          rw [show (hidden (.sectionStop a.worker) : Leanux.M _) after = .ok (bytes, final) from stopped]
          rfl
      | continued => exact ih {a with iterations := a.iterations + 1} after receive
      | yielded => rfl

/-- Correction of the former count-based drain assertion: the original entry
premises describe exact bounded hybrid execution, not adequate fuel for draining. -/
theorem cookieLoop_run (turns : List Nat) (a : Activation) (w : World) (d : Device)
    (records : List HiddenRecord) (receive : a.worker = .receiveWorker)
    (_device : w.wg.dev = some d) (_table : d.indexTable = []) (_cookies : CookieOnly d)
    (_present : w.ambient.hidden = some records)
    (_fuel : d.handshakeQueue.count + 1 ≤ turns.length) :
    (activationLoopSource turns a).run w = cookieHybridLoop turns.length a w :=
  cookieHybridLoop_eq turns a w receive

/-- The supplied entry occupancy is followed by the actual refill-budget read.
The combined budget retains the original read and exhaustion outcomes. -/
def cookieHybridRun (a : Activation) (occupancy : Nat) (w : World) : Except Stop (Unit × World) := do
  let (refills, ready) ← Activation.refills.run w
  let (state, after) ← cookieHybridLoop (occupancy + refills + 1) a ready
  (activationFinishSource a occupancy refills state).run after

/-- Correction of the former count-resolver correspondence. This exact full
Product outcome includes ordinary completion, yield, receive/record failures,
and the captured occupancy-plus-refills exhaustion invariant. -/
theorem cookieActivation_run (a : Activation) (w : World) (d : Device)
    (records : List HiddenRecord) (receive : a.worker = .receiveWorker)
    (device : w.wg.dev = some d) (_table : d.indexTable = []) (_cookies : CookieOnly d)
    (_present : w.ambient.hidden = some records) :
    (Activation.run a).run w = cookieHybridRun a d.handshakeQueue.count w := by
  have occupancy : (Activation.occupancy a).run w = .ok (d.handshakeQueue.count, w) := by
    change ((liftM getDev : Leanux.M Device).run w >>= _) = _
    have read : (liftM getDev : Leanux.M Device).run w = .ok (d, w) := by
      change (((getDev.run w.wg).run w.ambient) >>= _) = _
      simp [getDev, device]
    rw [read]
    simp [receive]
    rfl
  rw [activation_run_source, StateT.run_bind, occupancy]
  change (Activation.refills.run w >>= _) = _
  unfold cookieHybridRun
  cases read : Activation.refills.run w with
  | error stop => rfl
  | ok pair =>
    obtain ⟨refills, ready⟩ := pair
    change ((activationLoopSource (List.range' 0 (d.handshakeQueue.count + refills + 1)) a).run ready >>= _) = _
    rw [cookieHybridLoop_eq _ a ready receive]
    simp only [List.length_range']
    rfl

end Leanux.Proofs.WG.Progress
