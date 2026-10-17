import Leanux.Env
import Leanux.Proofs.WG.Noise.Execution

/-! Arbitrary Product callback contracts on the joint subsystem owners. Section reads and the NET_RX ordinal updates remain actual Ambient operations. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Noise Std.Do
theorem runWorker_kernel_contract (worker : Worker) (body : Leanux.M Unit)
    (P Q : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop)
    (contract : ⦃fun w => ⌜P w.wg w.fs w.tasks w.seccomp⌝⦄ body
      ⦃⇓? _ w => ⌜Q w.wg w.fs w.tasks w.seccomp⌝⦄) :
    ⦃fun w => ⌜P w.wg w.fs w.tasks w.seccomp⌝⦄ runWorker worker body
      ⦃⇓? _ w => ⌜Q w.wg w.fs w.tasks w.seccomp⌝⦄ := by
  apply (Product.ensures_iff _ _ _).mp
  have frame {α : Type} (action : AmbientM α)
      (R : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
      Product.Ensures (liftAmbient action) (fun (w : World) => R w.wg w.fs w.tasks w.seccomp)
        (fun _ w => R w.wg w.fs w.tasks w.seccomp) := by
    intro w result final pre run
    change (action.run w.ambient >>= fun (value, after) =>
      .ok (value, {w with ambient := after})) = .ok (result, final) at run
    cases actual : action.run w.ambient with
    | error stop => rw [actual] at run; cases run
    | ok pair => rw [actual] at run; cases run; exact pre
  have bodyContract := (Product.ensures_iff _ _ _).mpr contract
  have start (R : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
      Product.Ensures (if worker == .netRx then
        modifyAmbient fun s => {s with netRxSection := s.netRxSections} else pure ())
        (fun (w : World) => R w.wg w.fs w.tasks w.seccomp)
        (fun _ w => R w.wg w.fs w.tasks w.seccomp) := by
    split
    · intro w result final pre run
      cases run
      exact pre
    · intro w result final pre run; cases run; exact pre
  have stop (R : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
      Product.Ensures (if worker == .netRx then
        modifyAmbient fun s => {s with netRxSection := 0} else pure ())
        (fun (w : World) => R w.wg w.fs w.tasks w.seccomp)
        (fun _ w => R w.wg w.fs w.tasks w.seccomp) := by
    split
    · intro w result final pre run
      cases run
      exact pre
    · intro w result final pre run; cases run; exact pre
  have factor : runWorker worker body = (do
    let _ ← liftAmbient (AmbientM.hidden (.sectionStart worker))
    (if worker == .netRx then modifyAmbient fun s => {s with netRxSection := s.netRxSections} else pure ())
    body
    (if worker == .netRx then modifyAmbient fun s => {s with netRxSection := 0} else pure ())
    let _ ← liftAmbient (AmbientM.hidden (.sectionStop worker))
    pure ()) := by
    by_cases netRx : (worker == Worker.netRx) = true <;>
      simp [runWorker, netRx] <;> rfl
  rw [factor]
  refine Product.ensures_bind _ _ (frame _ P) ?_
  intro ignored
  refine Product.ensures_bind _ _ (start P) ?_
  intro ignored
  refine Product.ensures_bind _ _ bodyContract ?_
  intro ignored
  refine Product.ensures_bind _ _ (stop Q) ?_
  intro ignored
  refine Product.ensures_bind _ _ (frame _ Q) ?_
  intro ignored w result final pre run
  cases run
  exact pre

theorem runTimerSection_kernel_contract (worker : Worker) (body : Leanux.M Unit)
    (P Q : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop)
    (contract : ⦃fun w => ⌜P w.wg w.fs w.tasks w.seccomp⌝⦄ body
      ⦃⇓? _ w => ⌜Q w.wg w.fs w.tasks w.seccomp⌝⦄) :
    ⦃fun w => ⌜P w.wg w.fs w.tasks w.seccomp⌝⦄ runTimerSection worker body
      ⦃⇓? _ w => ⌜Q w.wg w.fs w.tasks w.seccomp⌝⦄ := by
  apply (Product.ensures_iff _ _ _).mp
  intro w result final pre run
  have inner := (Product.ensures_iff _ _ _).mpr
    (runWorker_kernel_contract worker body P Q contract)
  cases timer : worker.timer? with
  | none => simp [runTimerSection, timer, invariant, AmbientM.invariant] at run; cases run
  | some timer =>
    simp only [runTimerSection, timer, Option.isNone_some, Bool.false_eq_true, ite_false] at run
    change (runWorker worker body).run
      {w with ambient := {w.ambient with fired := w.ambient.fired.push worker.symbol}} = _ at run
    exact inner {w with ambient := {w.ambient with fired := w.ambient.fired.push worker.symbol}}
      result final pre run


end Leanux.Proofs.WG.TimerDiscipline
