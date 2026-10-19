import Leanux.Seccomp.Local
import Leanux.Proofs.WG.Progress.SeccompFiniteSource

/-! The concrete Local translator uses the same source factor as Seccomp.M.
Its branch operations return their supplied Boolean after recording it.
The allocation instance is already structural; only the outer repeat changes. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompLocalFinite
open Leanux Leanux.Seccomp
open SeccompFinite (PassState rank)

theorem run_bind {α β : Type} (a : Local.L α) (f : α → Local.L β) (s : Local.LState) :
    Local.run (a >>= f) s =
      Local.run a s >>= fun (x,t) => Local.run (f x) t := rfl

theorem loop_bounded {β : Type} (step : Unit → β → Local.L (ForInStep β))
    (rank : β → Nat)
    (decreases : ∀ state next s t,
      Local.run (step () state) s = .ok (.yield next,t) → rank next < rank state)
    (fuel : Nat) (state : β) (s : Local.LState)
    (enough : rank state < fuel) :
    Local.run (Lean.Loop.forIn Lean.Loop.mk state step) s =
      Local.run (forIn (List.replicate fuel ()) state step) s := by
  induction fuel generalizing state s with
  | zero => omega
  | succ fuel ih =>
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [List.replicate_succ, List.forIn_cons, run_bind]
    cases first : Local.run (step () state) s with
    | error stop => rfl
    | ok result =>
      obtain ⟨control,t⟩ := result
      cases control with
      | done next => rfl
      | yield next =>
        exact ih next t (by have := decreases state next s t first; omega)

def Returns {α : Type} (action : Local.L α) (P : α → Prop) : Prop :=
  ∀ s result t, Local.run action s = .ok (result,t) → P result

theorem returns_bind {α β : Type} (action : Local.L α) (f : α → Local.L β)
    (P : β → Prop) (tail : ∀ x, Returns (f x) P) : Returns (action >>= f) P := by
  intro s result t hr
  rw [run_bind] at hr
  cases ha : Local.run action s with
  | error stop => rw [ha] at hr; cases hr
  | ok out =>
    obtain ⟨x,s'⟩ := out
    exact tail x s' result t (by rw [ha] at hr; exact hr)

theorem returns_pure {α : Type} (x : α) (P : α → Prop) (hx : P x) :
    Returns (pure x) P := by
  intro s result t hr
  cases hr
  exact hx

theorem returns_branch {α : Type} (d : SDecision) (value : Bool)
    (f : Bool → Local.L α) (P : α → Prop) (tail : Returns (f value) P) :
    Returns (Seccomp.branch d value >>= f) P := by
  intro s result t hr
  exact tail {s with steps := s.steps.push {decision:=d,outcome:=value}} result t hr

theorem returns_compare {α : Type} (d : SDecision) (value : Bool) (left right : Int)
    (f : Bool → Local.L α) (P : α → Prop) (tail : Returns (f value) P) :
    Returns (Seccomp.branchCmp d value left right >>= f) P := by
  intro s result t hr
  exact tail {s with steps := s.steps.push ({decision:=d,outcome:=value,operands:=some (left,right)} : Local.LStep)} result t hr

theorem loop_three (step : Unit → PassState → Local.L (ForInStep PassState))
    (initial : PassState) (zero : initial.2.2.2.2=0)
    (decreases : ∀ state, Returns (step () state) (fun result => match result with
      | .done _=>True | .yield next=>rank next<rank state)) :
    Lean.Loop.forIn Lean.Loop.mk initial step = forIn [(),(),()] initial step := by
  funext s
  apply loop_bounded step rank
    (fun state next s t run=>decreases state s (.yield next) t run) 3
  simp [rank,zero]

theorem returns_ite {α : Type} (c : Prop) [Decidable c] (yes no : Local.L α)
    (P : α → Prop) (hy : c → Returns yes P) (hn : ¬c → Returns no P) :
    Returns (if c then yes else no) P := by
  by_cases h:c
  · simpa only [ite_eq_left h] using hy h
  · simpa only [ite_eq_right h] using hn h

theorem returns_option {α β : Type} (x : Option α) (some : α → Local.L β)
    (none : Local.L β) (P : β → Prop)
    (hs : ∀value, Returns (some value) P) (hn : Returns none P) :
    Returns (match x with | .some v=>some v | .none=>none) P := by
  cases x with
  | none=>exact hn
  | some v=>exact hs v

theorem after_finite (prog : Seccomp.ClassicProg)
    (newProg : Option Nat) (seen : Bool) (newLen : Nat) (has : Bool) (addrs : Array Nat) :
    SeccompPass.afterAllocationWith (m:=Local.L) Lean.Loop.mk prog newProg seen newLen has addrs =
      SeccompPass.afterAllocationWith [(),(),()] prog newProg seen newLen has addrs := by
  unfold SeccompPass.afterAllocationWith
  apply congrArg (fun action : Local.L PassState => action >>= _)
  apply loop_three
  · rfl
  · intro state
    dsimp only
    repeat first
      | (return_first_for Returns Seccomp.branch; apply returns_branch)
      | (return_first_for Returns cmpNe; apply returns_compare)
      | (return_first_for Returns cmpGt; apply returns_compare)
      | (return_head_for Returns Bind.bind; apply returns_bind; intro value)
      | (return_head_for Returns ite; apply returns_ite <;> intro condition)
      | (return_match_for Returns; refine returns_option _ _ _ _ (fun value=>?_) ?_)
      | (return_head_for Returns Pure.pure; apply returns_pure; simp_all [rank] <;> omega)

theorem finite_repeat (allocation : Local.L Bool) (prog : Seccomp.ClassicProg)
    (newProg : Option Nat) (seen : Bool) (newLen : Nat) :
    SeccompPass.withPasses Lean.Loop.mk allocation prog newProg seen newLen =
      SeccompPass.withPasses [(),(),()] allocation prog newProg seen newLen := by
  unfold SeccompPass.withPasses
  simp only [after_finite]

/-- The Local allocation instance records/answers a single allocation and has
no unbounded loop. Original Local refusals and step/record state are retained. -/
def convert (prog : Seccomp.ClassicProg) (newProg : Option Nat)
    (seen : Bool) (newLen : Nat) : Local.L (Except Int ConvertOut) :=
  SeccompPass.withPasses [(),(),()] (Seccomp.alloc .kcallocAddrs)
    prog newProg seen newLen

theorem convert_source (prog : Seccomp.ClassicProg) (newProg : Option Nat)
    (seen : Bool) (newLen : Nat) :
    (bpfConvertFilter prog newProg seen newLen : Local.L _) =
      convert prog newProg seen newLen := by
  rw [SeccompPass.original_source, finite_repeat]
  rfl

end Leanux.Proofs.WG.Progress.SeccompLocalFinite
