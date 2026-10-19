import Leanux.Proofs.WG.Progress.Dispatch
import Leanux.Proofs.WG.Progress.ScheduleProbeFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

def resumeCandidatesWith (run : Activation → M Unit) (stack : Option Worker) (candidates : List Activation) : M TurnResult := do
  match candidates with
  | [] => return turnReturn
  | [a] =>
    if let some w := stack then
      if ← Activation.hasWork { worker := w } then
        unsupported "the records do not determine which suspended worker resumed"
    modifyAmbient fun s => { s with suspended := s.suspended.filter (· != a) }
    run a
    return turnContinue
  | _ =>
    unsupported "the records do not determine which suspended worker resumed"
    return turnContinue


def resumeCandidates (stack : Option Worker) (candidates : List Activation) : M TurnResult :=
  resumeCandidatesWith Activation.run stack candidates

/-- One original scheduler iteration, including its explicit return marker. -/
def scheduleTurnWith (run : Activation → M Unit) (dispatch : Worker → M Bool)
    (consistent : Activation → M Bool) (napi : M Unit) (stack : Option Worker) : M TurnResult := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  if (← getAmbient).hidden.isNone then
    let d ← getDev
    let next := [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun w =>
      match w with
      | .receiveWorker => !d.handshakeQueue.empty
      | .decryptWorker => !d.decryptQueue.empty
      | .encryptWorker => !d.encryptQueue.empty
      | _ => !d.txWorkQueue.isEmpty
    let some w := next | return turnReturn
    if !(← dispatch w) then invariant s!"{w.symbol} has work but was not dispatched"
    return turnContinue
  let next ← peekHiddenSite
  if let some (w, true) := next.bind sectionOf then
    if ← dispatch w then return turnContinue else return turnReturn
  if next == some netRx && (← getDev).peers.toList.any (·.2.napiScheduled) then
    napi
    if (← peekHiddenSite) == some netRx then return turnReturn
    return turnContinue
  resumeCandidatesWith run stack (← (← getAmbient).suspended.filterM consistent)


def scheduleTurn (stack : Option Worker) : M TurnResult :=
  scheduleTurnWith Activation.run Env.dispatch Activation.consistent napiSoftirq stack

theorem schedule_source (stack : Option Worker) :
    schedule stack = (do
      let budget ← recordBudget
      let result ← forIn [0:budget] ((none, ()) : Option Unit × Unit)
        (fun _ _ => scheduleTurn stack)
      match result.1 with
      | some ret => pure ret
      | none => budgetExhausted "the scheduler loop") := by
  simp only [schedule, scheduleTurn, scheduleTurnWith, resumeCandidatesWith, turnContinue, turnReturn]
  congr 1
  funext budget
  congr 1
  funext result
  cases result.1 <;> rfl

def detached (w : World) (a : Activation) : World :=
  { w with ambient := { w.ambient with suspended := w.ambient.suspended.filter (· != a) } }

theorem resumeCandidates_singleton (a : Activation) (initial : World) :
    (resumeCandidates none [a]).run initial =
      ((Activation.run a).run (detached initial a) >>= fun out => pure (turnContinue, out.2)) := rfl

theorem turn_resumption (stack : Option Worker) (initial afterPeek : World) (next : Option Nat)
    (d : Device) (records : initial.ambient.hidden.isNone = false)
    (peek : (peekHiddenSite : Leanux.M (Option Nat)).run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.wg.dev = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false) :
    (scheduleTurn stack).run initial =
      ((afterPeek.ambient.suspended.filterM Activation.consistent).run afterPeek >>= fun out =>
        (resumeCandidates stack out.1).run out.2) := by
  have hd : (monadLift getDev : Leanux.M Device).run afterPeek = .ok (d, afterPeek) := by
    have native : ((getDev.run afterPeek.wg).run afterPeek.ambient) =
        .ok ((d, afterPeek.wg), afterPeek.ambient) := by
      simp [getDev, device]
      rfl
    change (((getDev.run afterPeek.wg).run afterPeek.ambient) >>= fun ((value, wg), ambient) =>
      Except.ok (value, {afterPeek with wg, ambient})) = _
    rw [native]
    rfl
  have hok {α β : Type} (x : α) (f : α → Except Stop β) :
      (Except.ok x >>= f) = f x := rfl
  have hg (w : World) : (getAmbient : Leanux.M Ambient).run w = .ok (w.ambient, w) := rfl
  simp only [scheduleTurn, scheduleTurnWith, StateT.run_bind, hg, hok]
  simp only [records, Bool.false_eq_true, ite_false]
  simp only [StateT.run_bind, peek, hok]
  cases hs : next.bind sectionOf with
  | none =>
    simp only [hd, hok]
    simp only [noPoll, Bool.false_eq_true, ite_false, StateT.run_bind, hg, hok, resumeCandidates]
  | some pair =>
    obtain ⟨worker, start⟩ := pair
    cases start with
    | true => exact False.elim (noStart worker hs)
    | false =>
      simp only [hd, hok]
      simp only [noPoll, Bool.false_eq_true, ite_false, StateT.run_bind, hg, hok, resumeCandidates]

theorem turn_resumes_singleton (initial afterPeek : World) (next : Option Nat)
    (d : Device) (a : Activation) (records : initial.ambient.hidden.isNone = false)
    (peek : (peekHiddenSite : Leanux.M (Option Nat)).run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.wg.dev = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.ambient.suspended.filterM Activation.consistent).run afterPeek =
      .ok ([a], afterPeek)) :
    (scheduleTurn none).run initial =
      ((Activation.run a).run (detached afterPeek a) >>= fun out => pure (turnContinue, out.2)) := by
  rw [turn_resumption none initial afterPeek next d records peek noStart device noPoll, candidates]
  exact resumeCandidates_singleton a afterPeek

theorem turn_no_candidates (stack : Option Worker) (initial afterPeek : World) (next : Option Nat)
    (d : Device) (records : initial.ambient.hidden.isNone = false)
    (peek : (peekHiddenSite : Leanux.M (Option Nat)).run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.wg.dev = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.ambient.suspended.filterM Activation.consistent).run afterPeek =
      .ok ([], afterPeek)) :
    (scheduleTurn stack).run initial = .ok (turnReturn, afterPeek) := by
  rw [turn_resumption stack initial afterPeek next d records peek noStart device noPoll, candidates]
  rfl

theorem turn_ambiguous (stack : Option Worker) (initial afterPeek : World) (next : Option Nat)
    (d : Device) (a b : Activation) (rest : List Activation) (records : initial.ambient.hidden.isNone = false)
    (peek : (peekHiddenSite : Leanux.M (Option Nat)).run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.wg.dev = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.ambient.suspended.filterM Activation.consistent).run afterPeek =
      .ok (a :: b :: rest, afterPeek)) :
    (scheduleTurn stack).run initial =
      .error (.outsideDomain (match afterPeek.ambient.steps.back? with
        | some s => s!"{s.decision.info.file}:{s.decision.info.line}"
        | none => "syscall entry")
        "the records do not determine which suspended worker resumed") := by
  rw [turn_resumption stack initial afterPeek next d records peek noStart device noPoll, candidates]
  rfl

end Leanux.Proofs.WG.Progress
