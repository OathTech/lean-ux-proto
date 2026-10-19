import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointCoverage

/-! Delivery contains no deeper packet-processing child. Its complete fixed
source witness therefore needs no service child contract. This says nothing
about lower interiors of the explicit native subsystem atoms. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Points
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal

def Shape.ChildFree : {α : Type} → {action : PrefixM Event α} → Shape action → Prop
  | _,_,.pure _ => True
  | _,_,.native _ => True
  | _,_,.child _ => False
  | _,_,.bind head tail => head.ChildFree ∧ ∀value,(tail value).ChildFree
  | _,_,.marked _ shape => shape.ChildFree

theorem childFree_cast {action other : PrefixM Event α} (eq : action = other)
    (shape : Shape action) : (eq ▸ shape).ChildFree ↔ shape.ChildFree := by
  cases eq
  rfl

theorem childFree_mpr {action other : PrefixM Event α} (eq : action = other)
    (shape : Shape other) : ((congrArg Shape eq).mpr shape).ChildFree ↔ shape.ChildFree := by
  cases eq
  rfl

theorem list_childFree (xs : List ι) (initial : σ)
    (body : ι → σ → PrefixM Event (ForInStep σ))
    (shapes : ∀value acc,Shape (body value acc))
    (free : ∀value acc,(shapes value acc).ChildFree) :
    (listShape xs initial body shapes).ChildFree := by
  induction xs generalizing initial with
  | nil => trivial
  | cons value rest ih =>
      simp only [listShape,childFree_cast,Shape.ChildFree]
      change (shapes value initial).ChildFree ∧ _
      refine ⟨free _ _,?_⟩
      intro decision
      cases decision with
      | done final => trivial
      | yield next => exact ih next

theorem Point.childFree (free : shape.ChildFree)
    (point : Point inside shape w h site u middle) : Point Boundary shape w h site u middle := by
  induction point with
  | entry shape => exact .entry shape
  | returned shape performed => exact .returned shape performed
  | interior token point => exact False.elim free
  | left tail point ih => exact .left tail (ih free.1)
  | right head tail leading point ih => exact .right head tail leading (ih (free.2 _))
  | marked label point ih => exact .marked label (ih free)

theorem option_childFree (query : Option ι)
    (absent : query = none → Shape action)
    (present : ∀value,query = some value → Shape action)
    (noneFree : ∀eq,(absent eq).ChildFree)
    (someFree : ∀value eq,(present value eq).ChildFree) :
    (Option.rec (motive := fun value => query = value → Shape action) absent present query rfl).ChildFree := by
  cases query with
  | none => exact noneFree rfl
  | some value => exact someFree value rfl

theorem rec_function_childFree (domain : (value : ι) → source = value → Prop)
    (action : (value : ι) → source = value → PrefixM Event α)
    (base : domain source rfl → Shape (action source rfl)) (eq : source = target)
    (witness : domain target eq) (free : ∀value,(base value).ChildFree) :
    ((Eq.rec (motive := fun value proof => domain value proof → Shape (action value proof)) base eq) witness).ChildFree := by
  cases eq
  exact free witness

attribute [local simp] lift_bind lift_pure lift_list Env.deliverSent

elab "delivery_unfold_match" : tactic => do
  let target ← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)
  unless target.isAppOf ``Shape.ChildFree do Lean.throwError "not a child-free source goal"
  let some shape := target.getAppArgs.back? | Lean.throwError "missing source witness"
  let .const name _ := shape.consumeMData.headBeta.getAppFn
    | Lean.throwError "not the delivery matcher"
  unless name.toString.endsWith "Leanux.Env.deliverSent.match_1.splitter" do
    Lean.throwError "different source matcher"
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent name)))

elab "delivery_rec_free" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  unless target.isAppOf ``Shape.ChildFree do Lean.throwError "not a child-free source goal"
  let some shape := target.getAppArgs.back? | Lean.throwError "missing source witness"
  let .app recursor witness := shape.consumeMData.headBeta | Lean.throwError "not an applied transport"
  unless recursor.isAppOf ``Eq.rec do Lean.throwError "not equality transport"
  let args := recursor.getAppArgs
  let (domain,action) ← Lean.Meta.lambdaTelescope args[2]! fun indices body => do
    Lean.Meta.forallTelescope body fun values result => do
      unless values.size == 1 && result.isAppOf ``Shape do Lean.throwError "different transport motive"
      let domain ← Lean.Meta.mkLambdaFVars indices (← Lean.Meta.inferType values[0]!)
      let action ← Lean.Meta.mkLambdaFVars indices result.getAppArgs.back!
      pure (domain,action)
  let proof ← Lean.Meta.mkAppM ``rec_function_childFree #[domain,action,args[3]!,args[5]!,witness]
  Lean.Elab.Tactic.replaceMainGoal (← goal.apply proof)

theorem delivery_childFree : deliveryShape.ChildFree := by
  unfold deliveryShape
  repeat' first
    | apply list_childFree
    | constructor
    | intro value
    | split
    | (apply (childFree_mpr (by simp_all <;> (try split) <;> simp_all <;> grind) _).2)
    | (simp +failIfUnchanged only [id_eq])
    | (simp +failIfUnchanged only [childFree_cast])
  all_goals delivery_unfold_match
  all_goals apply option_childFree
  all_goals first
    | (intro n eq
       rcases n with _ | n
       all_goals try rcases n with _ | n
       all_goals try rcases n with _ | n
       all_goals try rcases n with _ | n
       all_goals try rcases n with _ | n)
    | intro eq
  all_goals repeat' first
    | (dsimp +failIfUnchanged only)
    | contradiction
    | omega
    | delivery_rec_free
    | constructor
    | intro value
    | split
    | (apply (childFree_mpr (by simp_all <;> (try split) <;> simp_all <;> grind) _).2)

/-- Every delivery source point preserves its actual packet account and
history without an assumed source contract for another service family. -/
theorem delivery_carrier (before : CompleteProduct.Carrier h w)
    (point : RootPoints inside .delivery w h u middle) : CompleteProduct.Carrier middle u := by
  obtain ⟨site,point⟩ := point
  exact boundary_carrier before (point.childFree delivery_childFree)

theorem Point.childFree_remaining {action : PrefixM Event α} {shape : Shape action}
    (free : shape.ChildFree)
    (point : Point inside shape w h site u middle) :
    ∃remaining,runPrefix action w h = runPrefix remaining u middle := by
  induction point with
  | entry shape => exact ⟨_,rfl⟩
  | returned shape performed =>
      exact ⟨pure _,performed.trans (runPrefix_pure _ _ _).symm⟩
  | interior token point => exact False.elim free
  | left tail point ih =>
      rename_i body next head
      obtain ⟨remaining,continued⟩ := ih free.1
      exact ⟨remaining >>= next,by simp only [runPrefix_bind,continued]⟩
  | right head tail leading point ih =>
      obtain ⟨remaining,continued⟩ := ih (free.2 _)
      exact ⟨remaining,by rw [runPrefix_bind,leading]; exact continued⟩
  | marked label point ih => exact ih free

noncomputable def deliveryRemainder (w : World) (h : History) (u : World) (middle : History)
    (point : RootPoints inside .delivery w h u middle) : PrefixM Event Unit :=
  Classical.choose ((Classical.choose_spec point).childFree_remaining delivery_childFree)

/-- Delivery preserves the exact continuation even when its enclosing
execution later stops; no callback contract is needed for this source. -/
theorem deliveryRemainder_run (point : RootPoints inside .delivery w h u middle) :
    runPrefix hooks.deliver w h = runPrefix (deliveryRemainder w h u middle point) u middle :=
  Classical.choose_spec ((Classical.choose_spec point).childFree_remaining delivery_childFree)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Points
