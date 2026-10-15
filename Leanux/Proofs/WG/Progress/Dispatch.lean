import Leanux.Proofs.WG.Progress.Model
import Leanux.Proofs.WG.Progress.Scheduler
import Leanux.Proofs.WG.Config.Returns

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Config Std.Do

/-- Original dispatch selection and detachment, stopping before the section-start read. -/
def dispatchPrefix (w : Worker) : M (Option (Option Nat)) := do
  let d ← getDev
  let mut pid : Option Nat := none
  match w with
  | .encryptWorker => if d.encryptQueue.empty then return none
  | .decryptWorker => if d.decryptQueue.empty then return none
  | .receiveWorker => if d.handshakeQueue.isEmpty then return none
  | .txWorker =>
    let some headPid := d.txWorkQueue.head? | return none
    let p ← match ← peekUnit .txWorker with
      | some u => resolveUnit .txWorker u d.txWorkQueue
      | none => pure headPid
    modifyDev fun d => { d with txWorkQueue := d.txWorkQueue.erase p }
    pid := some p
  | _ => return none
  return some pid

def dispatchAfterPrefix (w : Worker) : Option (Option Nat) → M Bool
  | none => pure false
  | some pid => do
    _ ← hidden (.sectionStart w)
    Activation.run { worker := w, pid }
    return true

theorem dispatch_source (w : Worker) :
    dispatch w = (do let a ← dispatchPrefix w; dispatchAfterPrefix w a) := by
  cases w <;> simp only [dispatch, dispatchPrefix, dispatchAfterPrefix, bind_assoc, pure_bind]
  all_goals congr 1
  all_goals funext d
  all_goals split <;> simp_all only [bind_assoc, pure_bind, dispatchAfterPrefix]
  all_goals congr 1
  all_goals funext unit
  all_goals cases unit <;> simp only [bind_assoc, pure_bind, dispatchAfterPrefix]

/-- The selected activation really executes after the original start read. -/
def DispatchRun (w : Worker) (initial final : World) : Prop :=
  ∃ pid selected bytes afterStart,
    (dispatchPrefix w).run initial = .ok (some pid, selected) ∧
    (hidden (.sectionStart w)).run selected = .ok (bytes, afterStart) ∧
    (Activation.run { worker := w, pid }).run afterStart = .ok ((), final)

theorem dispatch_success_iff (w : Worker) (initial final : World) :
    (dispatch w).run initial = .ok (true, final) ↔ DispatchRun w initial final := by
  rw [dispatch_source, StateT.run_bind]
  unfold DispatchRun
  cases hp : (dispatchPrefix w).run initial with
  | error e =>
    change Except.error e = Except.ok (true, final) ↔ _
    simp
  | ok pair =>
    obtain ⟨choice, selected⟩ := pair
    cases choice with
    | none =>
      change Except.ok (false, selected) = Except.ok (true, final) ↔ _
      simp
    | some pid =>
      change ((hidden (.sectionStart w)).run selected >>= fun out =>
        ((Activation.run { worker := w, pid }).run out.2 >>= fun result =>
          pure (true, result.2))) = .ok (true, final) ↔ _
      cases hs : (hidden (.sectionStart w)).run selected with
      | error e =>
        change Except.error e = Except.ok (true, final) ↔ _
        simp [hs]
      | ok pair =>
        obtain ⟨bytes, afterStart⟩ := pair
        change ((Activation.run { worker := w, pid }).run afterStart >>= fun result =>
          pure (true, result.2)) = .ok (true, final) ↔ _
        cases ha : (Activation.run { worker := w, pid }).run afterStart with
        | error e =>
          change Except.error e = Except.ok (true, final) ↔ _
          simp [hs, ha]
        | ok pair =>
          obtain ⟨unit, afterRun⟩ := pair
          cases unit
          change Except.ok (true, afterRun) = Except.ok (true, final) ↔ _
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and, Option.some.injEq]
          constructor
          · intro same
            subst afterRun
            exact ⟨pid, selected, bytes, afterStart, ⟨rfl, rfl⟩, hs, ha⟩
          · rintro ⟨pid2, selected2, bytes2, afterStart2, ⟨rfl, rfl⟩, read, ran⟩
            rw [hs] at read
            obtain ⟨rfl, rfl⟩ := Except.ok.inj read
            rw [ha] at ran
            exact (congrArg Prod.snd (Except.ok.inj ran))

theorem dispatch_no_work (worker : Worker) (d : Device) (initial : World)
    (device : initial.k.wg = some d) (empty : NoDispatchWork worker d) :
    (dispatch worker).run initial = .ok (false, initial) := by
  have ht : Returns getDev (fun w => w = initial)
      (fun result w => result = d ∧ w = initial) := by
    rw [returns_iff]
    mvcgen [getDev, getK, invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all
  obtain ⟨result, after, hd, rfl, rfl⟩ := ht initial rfl
  have hok {α β : Type} (x : α) (f : α → Except Stop β) :
      (Except.ok x >>= f) = f x := rfl
  have hpure {α : Type} (x : α) (v : World) : (pure x : M α).run v = .ok (x, v) := rfl
  cases worker <;> simp only [NoDispatchWork] at empty
  all_goals simp only [dispatch, StateT.run_bind, hd, hok]
  all_goals simp [empty, hpure, StateT.run_pure]

theorem dispatch_false_iff (worker : Worker) (initial final : World) :
    (dispatch worker).run initial = .ok (false, final) ↔
      (dispatchPrefix worker).run initial = .ok (none, final) := by
  rw [dispatch_source, StateT.run_bind]
  cases hp : (dispatchPrefix worker).run initial with
  | error e =>
    change Except.error e = Except.ok (false, final) ↔ _
    simp
  | ok pair =>
    obtain ⟨choice, selected⟩ := pair
    cases choice with
    | none =>
      change Except.ok (false, selected) = Except.ok (false, final) ↔ _
      simp
    | some pid =>
      change ((hidden (.sectionStart worker)).run selected >>= fun out =>
        ((Activation.run { worker, pid }).run out.2 >>= fun result =>
          pure (true, result.2))) = .ok (false, final) ↔ _
      cases hs : (hidden (.sectionStart worker)).run selected with
      | error e =>
        change Except.error e = Except.ok (false, final) ↔ _
        simp
      | ok pair =>
        obtain ⟨bytes, afterStart⟩ := pair
        change ((Activation.run { worker, pid }).run afterStart >>= fun result =>
          pure (true, result.2)) = .ok (false, final) ↔ _
        cases ha : (Activation.run { worker, pid }).run afterStart with
        | error e =>
          change Except.error e = Except.ok (false, final) ↔ _
          simp
        | ok pair =>
          obtain ⟨ret, afterRun⟩ := pair
          change Except.ok (true, afterRun) = Except.ok (false, final) ↔ _
          simp

end Leanux.Proofs.WG.Progress
