import Leanux.Proofs.Framing.Product
import Leanux.Env.Stack
import Lean

/-! Original stack leaves framed over the original 43 product observations. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.Env Std.Do Leanux.Proofs.WG.Lifetimes

open Lean Meta Elab Tactic

/-- Expose only the leading action; reducing continuation bodies eagerly
duplicates the remaining IPv6 guards before their failing arms are disposed. -/
private def stackHeadBZ : Nat → Expr → Expr
  | 0, e => e
  | n+1, e =>
    let e := e.consumeMData
    match e with
    | .letE _ _ v b _ => stackHeadBZ n (b.instantiate1 v)
    | _ =>
      match e.getAppFn.consumeMData with
      | .letE _ _ v b _ => stackHeadBZ n (mkAppN (b.instantiate1 v) e.getAppArgs)
      | .lam .. =>
        let e' := e.headBeta
        if Expr.equal e e' then e else stackHeadBZ n e'
      | _ => e

elab "stack_head_reduce" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOf ``SameProductStore do throwError "not SameProductStore"
  let .app f a := t | throwError "missing action"
  let a' := stackHeadBZ 64 a
  replaceMainGoal [← g.replaceTargetDefEq (.app f a')]

theorem stackExcluded_failure (row : String) (w : World) :
    ∃ e, (Stack.excluded row).run w = .error e := ⟨_, rfl⟩

/-- IPv6 inspects packet bytes and device scalar fields and may append to the
sender inbox. The complete original store observation remains unchanged. -/
theorem stackReceive6_sameKernel (pkt : List UInt8) :
    SameProductStore (Stack.receive6 pkt) := by
  have stopped (a : Leanux.M Unit) (h : ∀ w, ∃ e, a.run w = .error e)
      (tail : Unit → Leanux.M Unit) : SameProductStore (a >>= tail) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x w' hr
    obtain ⟨e, he⟩ := h w
    simp only [StateT.run_bind, he] at hr
    contradiction
  have excluded (row : String) (tail : Unit → Leanux.M Unit) :=
    stopped (Stack.excluded row) (stackExcluded_failure row) tail
  have invalid (text : String) (tail : Unit → Leanux.M Unit) :=
    stopped (invariant text) (fun _ => ⟨_, rfl⟩) tail
  have read : SameProductStore (getWG : Leanux.M WGWorld) := by
    intro initial
    exact productGetWG_spec (fun s => s = initial)
  have write (f : EnvWorld → EnvWorld) : SameProductStore (modifyEnv f) := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x w' hr
    cases hr
    rfl
  unfold Stack.receive6
  stack_head_reduce
  split
  · exact invalid _ _
  · iterate 18
      (stack_head_reduce
       split
       · exact excluded _ _)
    stack_head_reduce
    split
    · apply SameView.bind read
      intro g
      split <;> exact excluded _ _
    · exact write _

end Leanux.Proofs.Framing
