import Leanux.Proofs.WG.Progress.Dispatch

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

def resumeCandidates (stack : Option Worker) (candidates : List Activation) : M TurnResult := do
  match candidates with
  | [] => return turnReturn
  | [a] =>
    if let some w := stack then
      if ← Activation.hasWork { worker := w } then
        unsupported "the records do not determine which suspended worker resumed"
    modify fun s => { s with suspended := s.suspended.filter (· != a) }
    Activation.run a
    return turnContinue
  | _ =>
    unsupported "the records do not determine which suspended worker resumed"
    return turnContinue

/-- One original scheduler iteration, including its explicit return marker. -/
def scheduleTurn (stack : Option Worker) : M TurnResult := do
  let netRx := (HiddenSite.sectionStart .netRx).info.id
  if (← get).hidden.isNone then
    let d ← getDev
    let next := [Worker.receiveWorker, .decryptWorker, .encryptWorker, .txWorker].find? fun w =>
      match w with
      | .receiveWorker => !d.handshakeQueue.isEmpty
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
    napiSoftirq
    if (← peekHiddenSite) == some netRx then return turnReturn
    return turnContinue
  resumeCandidates stack (← (← get).suspended.filterM Activation.consistent)

theorem schedule_source (stack : Option Worker) :
    schedule stack = (do
      let budget ← recordBudget
      let result ← forIn [0:budget] ((none, ()) : Option Unit × Unit)
        (fun _ _ => scheduleTurn stack)
      match result.1 with
      | some ret => pure ret
      | none => budgetExhausted "the scheduler loop") := by
  simp only [schedule, scheduleTurn, resumeCandidates, turnContinue, turnReturn, bind_assoc, pure_bind]
  congr 1
  funext budget
  congr 1
  funext result
  cases result.1 <;> rfl

def probeAccepted (a : Activation) (w : World) : Bool :=
  match (Activation.run a).run w with
  | .ok _ => true
  | .error _ => false

theorem consistent_result (a : Activation) (initial final : World) (result : Bool)
    (run : (Activation.consistent a).run initial = .ok (result, final)) :
    final = initial ∧ result = probeAccepted a initial := by
  rw [consistent_exact] at run
  unfold probeAccepted
  cases ha : (Activation.run a).run initial with
  | ok out => simpa [ha, probeResult, eq_comm, and_comm] using run
  | error err => cases err <;> simp_all [probeResult, eq_comm]

theorem filterAux_consistent_result (candidates acc : List Activation) (initial final : World)
    (result : List Activation)
    (run : (List.filterAuxM Activation.consistent candidates acc).run initial = .ok (result, final)) :
    final = initial ∧ result = (candidates.filter (probeAccepted · initial)).reverse ++ acc := by
  induction candidates generalizing initial final result acc with
  | nil =>
    change Except.ok (acc, initial) = Except.ok (result, final) at run
    simpa [eq_comm, and_comm] using run
  | cons a rest ih =>
    simp only [List.filterAuxM, StateT.run_bind] at run
    cases hp : (Activation.consistent a).run initial with
    | error err => rw [hp] at run; cases run
    | ok pair =>
      obtain ⟨accepted, afterProbe⟩ := pair
      obtain ⟨same, value⟩ := consistent_result a initial afterProbe accepted hp
      subst afterProbe
      rw [hp] at run
      have effect := ih (cond accepted (a :: acc) acc) initial final result run
      cases accepted <;> simp_all [List.filter_cons, List.reverse_cons, List.append_assoc]

theorem filter_consistent_result (candidates : List Activation) (initial final : World)
    (result : List Activation)
    (run : (candidates.filterM Activation.consistent).run initial = .ok (result, final)) :
    final = initial ∧ result = candidates.filter (probeAccepted · initial) := by
  simp only [List.filterM, StateT.run_bind] at run
  cases hf : (List.filterAuxM Activation.consistent candidates []).run initial with
  | error err => rw [hf] at run; cases run
  | ok pair =>
    obtain ⟨reversed, afterProbe⟩ := pair
    obtain ⟨same, values⟩ := filterAux_consistent_result candidates [] initial afterProbe reversed hf
    subst afterProbe
    rw [hf] at run
    change Except.ok (reversed.reverse, initial) = Except.ok (result, final) at run
    obtain ⟨rfl, rfl⟩ := Except.ok.inj run
    exact ⟨rfl, by simp [values]⟩

def detached (w : World) (a : Activation) : World :=
  { w with suspended := w.suspended.filter (· != a) }

theorem resumeCandidates_singleton (a : Activation) (initial : World) :
    (resumeCandidates none [a]).run initial =
      ((Activation.run a).run (detached initial a) >>= fun out => pure (turnContinue, out.2)) := rfl

theorem turn_resumption (stack : Option Worker) (initial afterPeek : World) (next : Option Nat)
    (d : Device) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false) :
    (scheduleTurn stack).run initial =
      ((afterPeek.suspended.filterM Activation.consistent).run afterPeek >>= fun out =>
        (resumeCandidates stack out.1).run out.2) := by
  have hd : getDev.run afterPeek = .ok (d, afterPeek) := by
    have ht : Leanux.Proofs.WG.Config.Returns getDev (fun w => w = afterPeek)
        (fun result w => result = d ∧ w = afterPeek) := by
      rw [Leanux.Proofs.WG.Config.returns_iff]
      mvcgen [getDev, getK, invariant]
      all_goals try dsimp +zetaDelta only at *
      all_goals repeat intro
      all_goals simp_all
    obtain ⟨result, after, run, rfl, rfl⟩ := ht afterPeek rfl
    exact run
  simp only [scheduleTurn, StateT.run_bind, StateT.run_get, pure_bind]
  simp only [records, Bool.false_eq_true, ite_false]
  have hok {α β : Type} (x : α) (f : α → Except Stop β) :
      (Except.ok x >>= f) = f x := rfl
  simp only [StateT.run_bind, peek, hok]
  cases hs : next.bind sectionOf with
  | none =>
    simp only [StateT.run_bind, hd, hok]
    simp only [noPoll, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_get, pure_bind]
  | some pair =>
    obtain ⟨worker, start⟩ := pair
    cases start with
    | true => exact False.elim (noStart worker hs)
    | false =>
      simp only [StateT.run_bind, hd, hok]
      simp only [noPoll, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_get, pure_bind]

theorem turn_resumes_singleton (initial afterPeek : World) (next : Option Nat)
    (d : Device) (a : Activation) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek =
      .ok ([a], afterPeek)) :
    (scheduleTurn none).run initial =
      ((Activation.run a).run (detached afterPeek a) >>= fun out => pure (turnContinue, out.2)) := by
  rw [turn_resumption none initial afterPeek next d records peek noStart device noPoll, candidates]
  exact resumeCandidates_singleton a afterPeek

theorem turn_no_candidates (stack : Option Worker) (initial afterPeek : World) (next : Option Nat)
    (d : Device) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek =
      .ok ([], afterPeek)) :
    (scheduleTurn stack).run initial = .ok (turnReturn, afterPeek) := by
  rw [turn_resumption stack initial afterPeek next d records peek noStart device noPoll, candidates]
  rfl

theorem turn_ambiguous (stack : Option Worker) (initial afterPeek : World) (next : Option Nat)
    (d : Device) (a b : Activation) (rest : List Activation) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek =
      .ok (a :: b :: rest, afterPeek)) :
    (scheduleTurn stack).run initial =
      .error (.outsideDomain (match afterPeek.steps.back? with
        | some s => s!"{s.decision.info.file}:{s.decision.info.line}"
        | none => "syscall entry")
        "the records do not determine which suspended worker resumed") := by
  rw [turn_resumption stack initial afterPeek next d records peek noStart device noPoll, candidates]
  rfl

end Leanux.Proofs.WG.Progress
