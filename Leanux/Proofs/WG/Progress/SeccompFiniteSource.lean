import Lean
import Leanux.Proofs.WG.Progress.SeccompPassSource
import Leanux.Proofs.WG.Progress.AllocationProgressSource
import Init.Internal.Order.While

/-! Exact finite evaluation of the concrete Seccomp.M converter. Every outer
yield increments the original Int pass counter and survives its overflow guard.
The bounded instruction scan is not re-proved or replaced. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SeccompFinite
open Leanux Leanux.Seccomp
def run {α : Type} (action : Seccomp.M α) (s : SeccompWorld) (t : TaskWorld) (a : Ambient) :=
  ((action.run s).run t).run a

theorem run_bind {α β : Type} (a : Seccomp.M α) (f : α → Seccomp.M β)
    (s : SeccompWorld) (t : TaskWorld) (b : Ambient) :
    run (a >>= f) s t b =
      run a s t b >>= fun (((x,u),v),c) => run (f x) u v c := rfl

theorem loop_bounded {β : Type} (step : Unit → β → Seccomp.M (ForInStep β))
    (rank : β → Nat)
    (decreases : ∀ state next s t a u v b,
      run (step () state) s t a = .ok (((.yield next,u),v),b) → rank next < rank state)
    (fuel : Nat) (state : β) (s : SeccompWorld) (t : TaskWorld) (a : Ambient)
    (enough : rank state < fuel) :
    run (Lean.Loop.forIn Lean.Loop.mk state step) s t a =
      run (forIn (List.replicate fuel ()) state step) s t a := by
  induction fuel generalizing state s t a with
  | zero => omega
  | succ fuel ih =>
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [List.replicate_succ, List.forIn_cons, run_bind]
    cases first : run (step () state) s t a with
    | error stop => rfl
    | ok result =>
      obtain ⟨⟨⟨control,u⟩,v⟩,b⟩ := result
      cases control with
      | done next => rfl
      | yield next =>
        exact ih next u v b (by have := decreases state next s t a u v b first; omega)

theorem bind_same {α β : Type} (x y : Seccomp.M α) (f : α → Seccomp.M β)
    (h : x=y) : (x >>= f) = (y >>= f) := by rw [h]

def Returns {α : Type} (action : Seccomp.M α) (P : α → Prop) : Prop :=
  ∀ s t a result u v b, run action s t a = .ok (((result,u),v),b) → P result
theorem returns_bind {α β : Type} (action : Seccomp.M α) (f : α → Seccomp.M β)
    (P : β → Prop) (tail : ∀ x, Returns (f x) P) : Returns (action >>= f) P := by
  intro s t a result u v b hr
  rw [run_bind] at hr
  cases ha : run action s t a with
  | error stop => rw [ha] at hr; cases hr
  | ok out =>
    obtain ⟨⟨⟨x,s'⟩,t'⟩,a'⟩:=out
    exact tail x s' t' a' result u v b (by rw [ha] at hr; exact hr)
theorem returns_pure {α : Type} (x : α) (P : α → Prop) (hx : P x) :
    Returns (pure x) P := by
  intro s t a result u v b hr
  cases hr
  exact hx
theorem returns_branch {α : Type} (d : SDecision) (value : Bool)
    (f : Bool → Seccomp.M α) (P : α → Prop) (tail : Returns (f value) P) :
    Returns (Seccomp.branch d value >>= f) P := by
  change Returns ((do emit d.toDecision value none; pure value) >>= f) P
  simpa only [bind_assoc,pure_bind] using
    returns_bind (emit d.toDecision value none) (fun _=>f value) P (fun _=>tail)
theorem returns_compare {α : Type} (d : SDecision) (value : Bool) (left right : Int)
    (f : Bool → Seccomp.M α) (P : α → Prop) (tail : Returns (f value) P) :
    Returns (Seccomp.branchCmp d value left right >>= f) P := by
  change Returns ((do emit d.toDecision value (some (left,right)); pure value) >>= f) P
  simpa only [bind_assoc,pure_bind] using
    returns_bind (emit d.toDecision value (some (left,right))) (fun _=>f value) P (fun _=>tail)

abbrev PassState := Option (Except Int ConvertOut) × Array Nat × Nat × Int × Int
def rank (state : PassState) : Nat := (2 - state.2.2.2.2).toNat

theorem loop_three (step : Unit → PassState → Seccomp.M (ForInStep PassState))
    (initial : PassState) (zero : initial.2.2.2.2=0)
    (decreases : ∀ state, Returns (step () state) (fun result => match result with
      | .done _=>True | .yield next=>rank next<rank state)) :
    Lean.Loop.forIn Lean.Loop.mk initial step = forIn [(),(),()] initial step := by
  funext s t a
  apply loop_bounded step rank
    (fun state next s t a u v b run=>decreases state s t a (.yield next) u v b run) 3
  simp [rank,zero]

theorem returns_ite {α : Type} (c : Prop) [Decidable c] (yes no : Seccomp.M α)
    (P : α → Prop) (hy : c → Returns yes P) (hn : ¬c → Returns no P) :
    Returns (if c then yes else no) P := by
  by_cases h:c
  · simpa only [ite_eq_left h] using hy h
  · simpa only [ite_eq_right h] using hn h
theorem returns_option {α β : Type} (x : Option α) (some : α → Seccomp.M β)
    (none : Seccomp.M β) (P : β → Prop)
    (hs : ∀value, Returns (some value) P) (hn : Returns none P) :
    Returns (match x with | .some v=>some v | .none=>none) P := by
  cases x with
  | none=>exact hn
  | some v=>exact hs v

open Lean Meta Elab Tactic in
elab "return_head_for " predicate:ident name:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let predicateName ← realizeGlobalConstNoOverloadWithInfo predicate
  unless target.isAppOf predicateName do throwError "not the expected return contract"
  let action := target.getAppArgs[target.getAppArgs.size-2]!.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo name
  unless action.getAppFn.constName? == some expected do throwError "different return action"

open Lean Meta Elab Tactic in
elab "return_match_for " predicate:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let predicateName ← realizeGlobalConstNoOverloadWithInfo predicate
  unless target.isAppOf predicateName do throwError "not the expected return contract"
  let action := target.getAppArgs[target.getAppArgs.size-2]!.consumeMData.headBeta
  unless (← matchMatcherApp? action).isSome do throwError "not a return match"

open Lean Meta Elab Tactic in
elab "return_first_for " predicate:ident name:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let predicateName ← realizeGlobalConstNoOverloadWithInfo predicate
  unless target.isAppOf predicateName do throwError "not the expected return contract"
  let action := target.getAppArgs[target.getAppArgs.size-2]!.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let first := action.getAppArgs[action.getAppArgs.size-2]!.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo name
  unless first.getAppFn.constName? == some expected do throwError "different first action"

macro "return_head " name:ident : tactic => `(tactic| return_head_for Returns $name)
macro "return_match" : tactic => `(tactic| return_match_for Returns)
macro "return_first " name:ident : tactic => `(tactic| return_first_for Returns $name)

theorem after_finite (prog : Seccomp.ClassicProg)
    (newProg : Option Nat) (seen : Bool) (newLen : Nat) (has : Bool) (addrs : Array Nat) :
    afterAllocationWith Lean.Loop.mk prog newProg seen newLen has addrs =
      afterAllocationWith [(),(),()] prog newProg seen newLen has addrs := by
  unfold afterAllocationWith SeccompPass.afterAllocationWith
  apply bind_same
  apply loop_three
  · rfl
  · intro state
    dsimp only
    repeat first
      | (return_first Seccomp.branch; apply returns_branch)
      | (return_first cmpNe; apply returns_compare)
      | (return_first cmpGt; apply returns_compare)
      | (return_head Bind.bind; apply returns_bind; intro value)
      | (return_head ite; apply returns_ite <;> intro condition)
      | (return_match; refine returns_option _ _ _ _ (fun value=>?_) ?_)
      | (return_head Pure.pure; apply returns_pure; simp_all [rank] <;> omega)

/-- The actual allocation callback, including supplied-record and placeholder
modes, with the structural evaluator substituted. -/
def allocate : Seccomp.M Bool :=
  monadLift (hiddenAllocFinite .kcallocAddrs)

theorem allocate_source : (Seccomp.alloc .kcallocAddrs : Seccomp.M Bool) = allocate := by
  change (monadLift (AmbientM.hiddenAlloc .kcallocAddrs) : Seccomp.M Bool) = _
  rw [hiddenAlloc_finite_source]
  rfl

/-- Three outer pass calls suffice. The original instruction loop is still
bounded by the input array; every return, errno and Stop remains unchanged. -/
theorem finite_repeat (allocation : Seccomp.M Bool) (prog : Seccomp.ClassicProg)
    (newProg : Option Nat) (seen : Bool) (newLen : Nat) :
    withPasses Lean.Loop.mk allocation prog newProg seen newLen =
      withPasses [(),(),()] allocation prog newProg seen newLen := by
  have after (has : Bool) (addrs : Array Nat) :
      SeccompPass.afterAllocationWith (m:=Seccomp.M) Lean.Loop.mk prog newProg seen newLen has addrs =
        SeccompPass.afterAllocationWith [(),(),()] prog newProg seen newLen has addrs :=
    after_finite prog newProg seen newLen has addrs
  unfold withPasses SeccompPass.withPasses
  simp only [after]

def convert (prog : Seccomp.ClassicProg) (newProg : Option Nat)
    (seen : Bool) (newLen : Nat) : Seccomp.M (Except Int ConvertOut) :=
  withPasses [(),(),()] allocate prog newProg seen newLen

/-- Complete concrete converter equality. No validation, successful allocation,
translation success or output-agreement premise is supplied. -/
theorem convert_source (prog : Seccomp.ClassicProg) (newProg : Option Nat)
    (seen : Bool) (newLen : Nat) :
    (bpfConvertFilter prog newProg seen newLen : Seccomp.M _) =
      convert prog newProg seen newLen := by
  rw [original_source, finite_repeat, allocate_source]
  rfl


end Leanux.Proofs.WG.Progress.SeccompFinite
