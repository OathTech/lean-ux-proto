import Leanux.Proofs.Logged.Runner
import Leanux.Proofs.WG.Keypairs.Evolution.Rules
import Leanux.Proofs.Framing.Product

/-! The explicit-World outer runner carries the proved lifetime invariant
through every actual observed syscall and ambient-record step. -/
namespace Leanux.Proofs.WG.Keypairs.RunnerProof
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged
open Leanux.Proofs.Framing Std.Do

set_option maxHeartbeats 2000000
set_option pp.structureInstances false

theorem runAtLogged_inv_wp {g : GhostM α} (hg : Evolves g)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜Inv (snapshot w.wg) h⌝⦄ runAtLogged index w g
    ⦃⇓? out h => ⌜Inv (snapshot out.2.wg) h⌝⦄ := by
  apply (stateExceptHoare_iff_triple _ _ _).mp
  intro h out h' hp hr
  exact hg.preserves h w out.1 h' out.2 hp
    ((runAtLogged_ok_iff index w g h out.1 h' out.2).mp hr)

theorem ordinary_runAt_inv_wp {a : Leanux.M α} (ha : ProductOrdinaryAction a)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜Inv (snapshot w.wg) h⌝⦄
      (liftM ((a.run w).mapError (fun e => (index, e))) :
        StateT History (Except (Nat × Stop)) (α × World))
    ⦃⇓? out h => ⌜Inv (snapshot out.2.wg) h⌝⦄ := by
  apply (stateExceptHoare_iff_triple _ _ _).mp
  intro h out h' hp hr
  change ((a.run w).mapError (fun e => (index, e)) >>= fun x => pure (x, h)) = .ok (out, h') at hr
  cases he : a.run w with
  | error e => simp [he, Except.mapError] at hr; cases hr
  | ok value =>
    simp [he, Except.mapError] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact ((Lifetimes.ProjectedAction.iff_run _ _ _).mp ha w _ _ he).preserves hp

theorem executeTraceLogged_nodup_wp
    (calls : ∀ call, Evolves (syscallLogged call))
    (trace : Trace) (placeholders : Bool) :
    ⦃fun h => ⌜h = []⌝⦄ executeTraceLogged trace placeholders
    ⦃⇓? _ h => ⌜h.Nodup⌝⦄ := by
  have syscall_spec (index : Nat) (w : World) (call : Syscall) :=
    runAtLogged_inv_wp (calls call) index w
  have ambient : SameView (fun w : World => snapshot w.wg) (skipAmbient : Leanux.M Unit) := by
    intro initial
    exact productAmbient_spec AmbientM.skipAmbient (fun w => snapshot w.wg = initial)
      (fun _ _ hp => hp)
  have ambient_spec (index : Nat) (w : World) :=
    ordinary_runAt_inv_wp
      (SameView.ordinary ambient) index w
  have routing (α : Type) (a : Net.M α) :
      SameView (fun w : World => snapshot w.wg) (liftM a : Leanux.M α) := by
    apply sameView_liftWG (fun w => snapshot w.wg) snapshot (liftRouting a)
    · intro initial
      exact hoare_liftRouting a (fun g => snapshot g = initial) (fun _ _ hp => hp)
    · intro w g ambient hg
      exact hg
  have boot : SameView (fun w : World => snapshot w.wg) (show Leanux.M Unit from do
      Net.Fib.bootTables
      if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables) := by
    apply SameView.bind (routing _ _)
    intro _
    split
    · exact routing _ _
    · exact SameView.pure _ _
  have boot_run (w : World) (x : Unit) (v : World)
      (hr : (show Leanux.M Unit from do
        Net.Fib.bootTables
        if trace.foreign then Net.Fib.inCreatorNs Net.Fib.bootTables).run w = .ok (x, v)) :
      snapshot v.wg = snapshot w.wg :=
    (Lifetimes.ProjectedAction.iff_run _ _ _).mp boot w x v hr
  unfold executeTraceLogged
  mvcgen [syscall_spec, ambient_spec]
  case inv1 =>
    exact ((⇓? out h => ⌜Inv (snapshot out.2.1.wg) h⌝) :
      Invariant trace.ops.toList
        (World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json)
        (.arg History (.except (Nat × Stop) .pure)))
  case inv2 =>
    let r : Unit × World := by assumption
    exact ((⇓? _ h => ⌜Inv (snapshot r.2.wg) h⌝) :
      Invariant r.2.ambient.steps.toList (Array Json)
        (.arg History (.except (Nat × Stop) .pure)))
  case inv3 =>
    let r : Unit × World := by assumption
    exact ((⇓? _ h => ⌜Inv (snapshot r.2.wg) h⌝) :
      Invariant r.2.ambient.fired.toList (Array Json)
        (.arg History (.except (Nat × Stop) .pure)))
  case inv4 =>
    exact ((⇓? out h => ⌜Inv (snapshot out.2.1.wg) h⌝) :
      Invariant trace.ops.toList
        (World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json)
        (.arg History (.except (Nat × Stop) .pure)))
  case inv5 =>
    let r : Unit × World := by assumption
    exact ((⇓? _ h => ⌜Inv (snapshot r.2.wg) h⌝) :
      Invariant r.2.ambient.steps.toList (Array Json)
        (.arg History (.except (Nat × Stop) .pure)))
  case inv6 =>
    let r : Unit × World := by assumption
    exact ((⇓? _ h => ⌜Inv (snapshot r.2.wg) h⌝) :
      Invariant r.2.ambient.fired.toList (Array Json)
        (.arg History (.except (Nat × Stop) .pure)))
  case inv7 =>
    exact ((⇓? out h => ⌜Inv (snapshot out.2.1.wg) h⌝) :
      Invariant trace.ops.toList
        (World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json)
        (.arg History (.except (Nat × Stop) .pure)))
  case inv8 =>
    let r : Unit × World := by assumption
    exact ((⇓? _ h => ⌜Inv (snapshot r.2.wg) h⌝) :
      Invariant r.2.ambient.steps.toList (Array Json)
        (.arg History (.except (Nat × Stop) .pure)))
  case inv9 =>
    let r : Unit × World := by assumption
    exact ((⇓? _ h => ⌜Inv (snapshot r.2.wg) h⌝) :
      Invariant r.2.ambient.fired.toList (Array Json)
        (.arg History (.except (Nat × Stop) .pure)))
  case inv10 =>
    exact ((⇓? out h => ⌜Inv (snapshot out.2.1.wg) h⌝) :
      Invariant trace.ops.toList
        (World × Array Int × Array (Option (Nat × Nat)) × Array Json × Array Json × Array Json)
        (.arg History (.except (Nat × Stop) .pure)))
  case inv11 =>
    let r : Unit × World := by assumption
    exact ((⇓? _ h => ⌜Inv (snapshot r.2.wg) h⌝) :
      Invariant r.2.ambient.steps.toList (Array Json)
        (.arg History (.except (Nat × Stop) .pure)))
  case inv12 =>
    let r : Unit × World := by assumption
    exact ((⇓? _ h => ⌜Inv (snapshot r.2.wg) h⌝) :
      Invariant r.2.ambient.fired.toList (Array Json)
        (.arg History (.except (Nat × Stop) .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try trivial
  all_goals try exact Inv.nodup (by assumption)
  all_goals try exact id
  all_goals try (rename_i history hh; subst history)
  all_goals try
    change Inv (snapshot (Runner.initialWG trace.net trace.bare)) []
    rw [initial_snapshot]
    exact inv_empty 0
  all_goals try
    have hb := boot_run _ _ _ (by assumption)
    change Inv _ []
    rw [hb]
    change Inv (snapshot (Runner.initialWG trace.net trace.bare)) []
    rw [initial_snapshot]
    exact inv_empty 0

/-- Successful runner histories have no repeated event once the concrete
syscall observer contracts are supplied. This is an intermediate composition
lemma; the final S1 theorem discharges its caller premise. -/
theorem executeTraceLogged_nodup_of_calls
    (calls : ∀ call, Evolves (syscallLogged call))
    (trace : Trace) (placeholders : Bool) (json : Json) (history : History)
    (hr : (executeTraceLogged trace placeholders).run [] = .ok (json, history)) :
    history.Nodup :=
  (stateExceptHoare_iff_triple _ _ _).mpr
    (executeTraceLogged_nodup_wp calls trace placeholders) [] json history rfl hr

end Leanux.Proofs.WG.Keypairs.RunnerProof
