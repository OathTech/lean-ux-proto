import Leanux.Proofs.WG.TimerDiscipline.RecordedFrames
import Leanux.Proofs.WG.TimerDiscipline.JitterFrames
import Leanux.Proofs.WG.TimerDiscipline.JitterRecordsSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- The actual finite jitter loop preserves its input mode on normal return. -/
theorem jitter_arm_mode (modeValue : Bool) (site : HiddenSite) (g : WGWorld) :
    Product.Ensures ((jitterBelowRekeyTimeout site).run g)
      (fun ambient => ambient.armRecords = modeValue)
      (fun _ ambient => ambient.armRecords = modeValue) := by
  have step (turn : Nat) (state : Option Nat × Unit) (g : WGWorld) :
      Product.Ensures ((jitterStep site turn state).run g)
        (fun ambient => ambient.armRecords = modeValue)
        (fun _ ambient => ambient.armRecords = modeValue) := by
    intro ambient result after pre run
    have hiddenRun : ((hidden site : WG.M (List UInt8)).run g).run ambient =
        ((AmbientM.hidden site).run ambient).map (fun (bytes, current) => ((bytes, g), current)) := rfl
    simp only [jitterStep, StateT.run_bind, hiddenRun, Except.map] at run
    cases read : (AmbientM.hidden site).run ambient with
    | error stop => rw [read] at run; cases run
    | ok pair =>
      obtain ⟨bytes, current⟩ := pair
      have preserved := InitiationReady.hidden_mode modeValue site ambient bytes current pre read
      rw [read] at run
      dsimp only [Bind.bind, Except.bind] at run
      split at run <;> cases run <;> exact preserved
  have loop (turns : List Nat) (state : Option Nat × Unit) (g : WGWorld) :
      Product.Ensures ((forIn turns state (jitterStep site) : WG.M _).run g)
        (fun ambient => ambient.armRecords = modeValue)
        (fun _ ambient => ambient.armRecords = modeValue) := by
    induction turns generalizing state g with
    | nil =>
      intro ambient result after pre run
      cases run
      exact pre
    | cons turn turns ih =>
      intro ambient result after pre run
      simp only [List.forIn_cons, StateT.run_bind] at run
      cases first : ((jitterStep site turn state).run g).run ambient with
      | error stop => rw [first] at run; cases run
      | ok pair =>
        obtain ⟨⟨out, middle⟩, current⟩ := pair
        have preserved := step turn state g ambient (out, middle) current pre first
        rw [first] at run
        cases out with
        | done value => cases run; exact preserved
        | yield value => exact ih value middle current result after preserved run
  intro ambient result after pre run
  let budget := match ambient.hidden with
    | some rs => rs.length + 1
    | none => DOMAIN_FILTER_TURNS
  have budgetRun : ((recordBudget : WG.M Nat).run g).run ambient = .ok ((budget, g), ambient) := rfl
  rw [jitter_source] at run
  simp only [StateT.run_bind, budgetRun] at run
  dsimp only [Bind.bind, Except.bind] at run
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at run
  cases first : ((forIn (List.range' ([:budget] : Std.Legacy.Range).start ([:budget] : Std.Legacy.Range).size ([:budget] : Std.Legacy.Range).step) (none, ()) (jitterStep site) : WG.M _).run g).run ambient with
  | error stop => rw [first] at run; cases run
  | ok pair =>
    obtain ⟨⟨state, current⟩, middle⟩ := pair
    have preserved := loop _ (none, ()) g ambient (state, current) middle pre first
    rw [first] at run
    cases value : state.1 with
    | some n =>
      simp only [jitterFinish, value] at run
      cases run
      exact preserved
    | none =>
      cases hidden : middle.hidden <;>
        simp [jitterFinish, value, budgetExhausted, AmbientM.budgetExhausted,
          hidden, AmbientM.invariant, AmbientM.unsupported] at run
      all_goals cases run

/-- Jitter preserves every subsystem owner and either input mode; its numeric
bound concerns the same actual successful run. -/
theorem jitter_mode_bounded (modeValue : Bool)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) (site : HiddenSite) :
    Product.Ensures (liftWG (jitterBelowRekeyTimeout site))
      (fun w => P w.wg w.fs w.tasks w.seccomp ∧ w.ambient.armRecords = modeValue)
      (fun n w => (P w.wg w.fs w.tasks w.seccomp ∧ w.ambient.armRecords = modeValue) ∧ n < HZ / 3) := by
  intro w result final pre run
  change (((jitterBelowRekeyTimeout site).run w.wg).run w.ambient >>= fun ((value, current), after) =>
    .ok (value, {w with wg := current, ambient := after})) = .ok (result, final) at run
  cases native : ((jitterBelowRekeyTimeout site).run w.wg).run w.ambient with
  | error stop => rw [native] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, current⟩, after⟩ := pair
    rw [native] at run
    cases run
    have frame := jitter_wg_spec (fun g => P g w.fs w.tasks w.seccomp) site
      w.wg w.ambient result current after pre.1 native
    have recorded := jitter_arm_mode modeValue site w.wg w.ambient (result, current) after pre.2 native
    have bound := jitter_bounded site w.wg w.ambient result current after trivial native
    exact ⟨⟨frame, recorded⟩, bound⟩

theorem jitter_input_effect (site : HiddenSite) (g final : WGWorld)
    (ambient after : Ambient) (jitter : Nat)
    (run : ((jitterBelowRekeyTimeout site).run g).run ambient = .ok ((jitter,final),after)) :
    final = g ∧ after.armRecords = ambient.armRecords ∧ jitter < HZ / 3 := by
  have same := jitter_wg_spec (fun w=>w=g) site g ambient jitter final after rfl run
  have mode := jitter_arm_mode ambient.armRecords site g ambient (jitter,final) after rfl run
  exact ⟨same,mode,jitter_bounded site g ambient jitter final after trivial run⟩

/-- Original recorded-mode contract retained as an exact-header instance. -/
theorem jitter_recorded_bounded
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) (site : HiddenSite) :
    Product.Ensures (liftWG (jitterBelowRekeyTimeout site))
      (fun w => P w.wg w.fs w.tasks w.seccomp ∧ w.ambient.armRecords = true)
      (fun n w => (P w.wg w.fs w.tasks w.seccomp ∧ w.ambient.armRecords = true) ∧ n < HZ / 3) :=
  jitter_mode_bounded true P site


end Leanux.Proofs.WG.TimerDiscipline
