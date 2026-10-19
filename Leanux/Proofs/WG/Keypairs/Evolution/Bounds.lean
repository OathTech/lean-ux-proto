import Leanux.Proofs.WG.CounterWindow.Bounds
import Leanux.Proofs.WG.Keypairs.Evolution.Runner

/-! The acceptance history's lower edge, carried through lifetime evolution
and the original runner's observer. The pairwise relation states the bound
against every earlier acceptance in the same allocation lifetime. -/
namespace Leanux.Proofs.WG.Keypairs
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Leanux.Proofs.WG.CounterWindow Leanux.Proofs.Framing Std.Do

/-- A later acceptance in the same lifetime is at most one window behind. -/
def WithinWindow (earlier later : AcceptedEvent) : Prop :=
  earlier.keypair = later.keypair →
    earlier.nonce ≤ later.nonce + COUNTER_WINDOW_SIZE

/-- Every earlier acceptance bounds every later acceptance of that lifetime. -/
def FloorHistory (history : History) : Prop := history.Pairwise WithinWindow

/-- A named validator transition preserves the history's inclusive floor. -/
theorem Inv.validate_floor (hi : Inv s history) (hf : FloorHistory history)
    (hc : s.slots i = some c) (nonce : Nat) :
    FloorHistory (logResult history c nonce) := by
  unfold logResult
  split
  · rename_i ha
    apply List.pairwise_append.mpr
    refine ⟨hf, by simp, ?_⟩
    intro earlier he later hl
    have hl' := List.mem_singleton.mp hl
    subst later
    intro hid
    have hm := (hi.remembers i c hc earlier he hid).1
    have hb := (step_accepted_bounds c.counter nonce ha).1
    dsimp only [WithinWindow]
    omega
  · exact hf

/-- All finite lifetime evolutions preserve the bound, including deletion,
fresh allocation and arbitrary compositions of named validator transitions. -/
theorem Evolution.floor (he : Evolution s h t g) (hi : Inv s h)
    (hf : FloorHistory h) : FloorHistory g := by
  induction he with
  | refl => exact hf
  | ordinary => exact hf
  | validate hc n => exact hi.validate_floor hf hc n
  | trans h₁ _ ih₁ ih₂ => exact ih₂ (h₁.preserves hi) (ih₁ hi hf)

/-- The ordinary lifetime invariant and the ordered acceptance bound. -/
def FloorInv (s : Snapshot) (h : History) : Prop := Inv s h ∧ FloorHistory h

theorem Evolves.preserves_floor {g : GhostM α} (hg : Evolves g)
    (h : History) (w : World) (x : α) (h' : History) (w' : World)
    (hi : FloorInv (snapshot w.wg) h)
    (hr : ((g.run h).run w) = .ok ((x, h'), w')) :
    FloorInv (snapshot w'.wg) h' := by
  have he := hg h w x h' w' hi.1 hr
  exact ⟨he.preserves hi.1, he.floor hi.1 hi.2⟩

namespace RunnerProof

set_option maxHeartbeats 2000000
set_option pp.structureInstances false

theorem runAtLogged_floor_wp {g : GhostM α} (hg : Evolves g)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜FloorInv (snapshot w.wg) h⌝⦄ runAtLogged index w g
    ⦃⇓? out h => ⌜FloorInv (snapshot out.2.wg) h⌝⦄ := by
  apply (stateExceptHoare_iff_triple _ _ _).mp
  intro h out h' hp hr
  exact hg.preserves_floor h w out.1 h' out.2 hp
    ((runAtLogged_ok_iff index w g h out.1 h' out.2).mp hr)

theorem ordinary_runAt_floor_wp {a : Leanux.M α} (ha : ProductOrdinaryAction a)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜FloorInv (snapshot w.wg) h⌝⦄
      (liftM ((a.run w).mapError (fun e => (index, e))) :
        StateT History (Except (Nat × Stop)) (α × World))
    ⦃⇓? out h => ⌜FloorInv (snapshot out.2.wg) h⌝⦄ := by
  apply (stateExceptHoare_iff_triple _ _ _).mp
  intro h out h' hp hr
  change ((a.run w).mapError (fun e => (index, e)) >>= fun x => pure (x, h)) =
    .ok (out, h') at hr
  cases he : a.run w with
  | error e => simp [he, Except.mapError] at hr; cases hr
  | ok value =>
    simp [he, Except.mapError] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact ⟨((Lifetimes.ProjectedAction.iff_run _ _ _).mp ha w _ _ he).preserves hp.1, hp.2⟩

-- The additional pending-work refusal expands the literal runner WP.
set_option maxHeartbeats 4000000 in
theorem executeTraceLogged_floor_wp
    (calls : ∀ call, Evolves (syscallLogged call))
    (trace : Trace) (placeholders : Bool) :
    ⦃fun h => ⌜h = []⌝⦄ executeTraceLogged trace placeholders
    ⦃⇓? _ h => ⌜FloorHistory h⌝⦄ := by
  have syscall_spec (index : Nat) (w : World) (call : Syscall) :=
    runAtLogged_floor_wp (calls call) index w
  have ambient : SameView (fun w : World => snapshot w.wg) (skipAmbient : Leanux.M Unit) := by
    intro initial
    exact productAmbient_spec AmbientM.skipAmbient (fun w => snapshot w.wg = initial)
      (fun _ _ hp => hp)
  have ambient_spec (index : Nat) (w : World) :=
    ordinary_runAt_floor_wp
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

  let runnerInv : World → Assertion (.arg History (.except (Nat × Stop) .pure)) :=
    fun w h => ⌜FloorInv (snapshot w.wg) h⌝
  unfold executeTraceLogged
  repeat' first
    | (lifetime_runner_head runAtLogged;
        apply Triple.entails_wp_of_pre_post (syscall_spec _ _ _))
    | (lifetime_runner_head liftM;
        apply Triple.entails_wp_of_pre_post (ambient_spec _ _))
    | lifetime_runner_step runnerInv

  all_goals try
    solve
    | simp only [WP.monadLift_StateT, WP.throw_Except]
      intro history hi
      trivial
  all_goals try dsimp only [runnerInv] at *
  all_goals try exact .rfl
  all_goals try exact ⟨fun _ => .rfl, .rfl⟩
  all_goals try (solve | intros; assumption)
  all_goals try (solve | intro history hi; exact hi.2)
  all_goals try
    solve
    | intro history hh
      change history = [] at hh
      subst history
      change FloorInv (snapshot (Runner.initialWG trace.net trace.bare)) []
      constructor
      · rw [initial_snapshot]; exact inv_empty 0
      · simp [FloorHistory]
  all_goals try
    solve
    | intro history hh
      change history = [] at hh
      subst history
      have hb := boot_run _ _ _ (by assumption)
      change FloorInv _ []
      rw [hb]
      change FloorInv (snapshot (Runner.initialWG trace.net trace.bare)) []
      constructor
      · rw [initial_snapshot]; exact inv_empty 0
      · simp [FloorHistory]

/-- Every successful observer run obeys the bound once its concrete syscall
contracts are supplied; the terminal result discharges that premise. -/
theorem executeTraceLogged_floor_of_calls
    (calls : ∀ call, Evolves (syscallLogged call))
    (trace : Trace) (placeholders : Bool) (json : Json) (history : History)
    (hr : (executeTraceLogged trace placeholders).run [] = .ok (json, history)) :
    FloorHistory history :=
  (stateExceptHoare_iff_triple _ _ _).mpr
    (executeTraceLogged_floor_wp calls trace placeholders) [] json history rfl hr

end RunnerProof
end Leanux.Proofs.WG.Keypairs
