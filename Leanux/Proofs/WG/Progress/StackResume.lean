import Leanux.Proofs.WG.Progress.StackFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Noise Std.Do

def resumptionAmbiguity (w : World) : Stop :=
  .outsideDomain (match w.steps.back? with
    | some s => s!"{s.decision.info.file}:{s.decision.info.line}"
    | none => "syscall entry")
    "the records do not determine which suspended worker resumed"

theorem resumeCandidates_stack_busy (worker : Worker) (a : Activation) (initial after : World)
    (busy : (Activation.hasWork { worker }).run initial = .ok (true, after)) :
    (resumeCandidates (some worker) [a]).run initial = .error (resumptionAmbiguity initial) := by
  have same := hasWork_world { worker } initial initial true after rfl busy
  subst after
  simp only [resumeCandidates, StateT.run_bind, busy]
  rfl

theorem resumeCandidates_stack_idle (worker : Worker) (a : Activation) (initial after : World)
    (idle : (Activation.hasWork { worker }).run initial = .ok (false, after)) :
    (resumeCandidates (some worker) [a]).run initial =
      ((Activation.run a).run (detached initial a) >>= fun out => pure (turnContinue, out.2)) := by
  have same := hasWork_world { worker } initial initial false after rfl idle
  subst after
  simp only [resumeCandidates, StateT.run_bind, idle]
  rfl

theorem resumeCandidates_stack_error (worker : Worker) (a : Activation) (initial : World) (err : Stop)
    (failed : (Activation.hasWork { worker }).run initial = .error err) :
    (resumeCandidates (some worker) [a]).run initial = .error err := by
  simp only [resumeCandidates, StateT.run_bind, failed]
  rfl

theorem turn_stack_busy (worker : Worker) (initial afterPeek : World) (next : Option Nat)
    (d : Device) (a : Activation) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek = .ok ([a], afterPeek))
    (busy : (Activation.hasWork { worker }).run afterPeek = .ok (true, afterPeek)) :
    (scheduleTurn (some worker)).run initial = .error (resumptionAmbiguity afterPeek) := by
  rw [turn_resumption (some worker) initial afterPeek next d records peek noStart device noPoll, candidates]
  exact resumeCandidates_stack_busy worker a afterPeek afterPeek busy

theorem turn_stack_idle (worker : Worker) (initial afterPeek : World) (next : Option Nat)
    (d : Device) (a : Activation) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek = .ok ([a], afterPeek))
    (idle : (Activation.hasWork { worker }).run afterPeek = .ok (false, afterPeek)) :
    (scheduleTurn (some worker)).run initial =
      ((Activation.run a).run (detached afterPeek a) >>= fun out => pure (turnContinue, out.2)) := by
  rw [turn_resumption (some worker) initial afterPeek next d records peek noStart device noPoll, candidates]
  exact resumeCandidates_stack_idle worker a afterPeek afterPeek idle

theorem turn_stack_error (worker : Worker) (initial afterPeek : World) (next : Option Nat)
    (d : Device) (a : Activation) (err : Stop) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek = .ok ([a], afterPeek))
    (failed : (Activation.hasWork { worker }).run afterPeek = .error err) :
    (scheduleTurn (some worker)).run initial = .error err := by
  rw [turn_resumption (some worker) initial afterPeek next d records peek noStart device noPoll, candidates]
  exact resumeCandidates_stack_error worker a afterPeek err failed

end Leanux.Proofs.WG.Progress
