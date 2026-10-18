import Leanux.Proofs.WG.AuthenticatedEffects.TransportPublicationIngress
import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayPoll
import Leanux.Proofs.WG.TransmitSecurity.DriverSource

/-! State-dependent carrier contracts at the actual common-driver callbacks.
Native leaves need concrete packet-store frames; event histories alone cannot
supply this invariant. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues
variable {E : Type} {extra : List E → Prop} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay}

abbrev StateSafe (extra : List E → Prop) (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (g : WGPrefix E α) : Prop :=
  StatePrefixPreserves (fun h w _ => TransportPublication.Inv (h.filterMap origin) w ∧
    (TransportReplay.Safe origin replay h ∧ extra h))
    (fun h => TransportReplay.Safe origin replay h ∧ extra h) g

abbrev ProductSafe (extra : List E → Prop) (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (g : PrefixM E α) : Prop :=
  PrefixPreserves (fun h w => TransportPublication.Inv (h.filterMap origin) w.wg ∧
    (TransportReplay.Safe origin replay h ∧ extra h))
    (fun h => TransportReplay.Safe origin replay h ∧ extra h) g

theorem state_pure (x : α) : StateSafe extra origin replay (pure x) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi)

theorem state_native (action : WG.M α)
    (frame : ∀ h, Preserves (TransportPublication.Inv h) action) :
    StateSafe extra origin replay (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.2)
  intro h w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (frame (h.filterMap origin)) w a x v b hi.1 run,hi.2⟩

theorem state_rx (action : WG.M α) (frame : SameView RxDisposition.nativeRxStore action) :
    StateSafe extra origin replay (liftWGPrefix action) :=
  state_native action (TransportPublication.preserves_of_rx action frame)

theorem state_bind {g : WGPrefix E α} {f : α → WGPrefix E β}
    (hg : StateSafe extra origin replay g) (hf : ∀ x, StateSafe extra origin replay (f x)) :
    StateSafe extra origin replay (g >>= f) := StatePrefixEnsures.bind hg hf

theorem state_ite (p : Prop) [Decidable p] {a b : WGPrefix E α}
    (ha : p → StateSafe extra origin replay a) (hb : ¬p → StateSafe extra origin replay b) :
    StateSafe extra origin replay (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

theorem state_forIn (xs : List α) (init : β) (f : α → β → WGPrefix E (ForInStep β))
    (hf : ∀ x b, StateSafe extra origin replay (f x b)) :
    StateSafe extra origin replay (forIn xs init f) := by
  induction xs generalizing init with
  | nil => exact state_pure init
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply state_bind (hf x init)
    intro step
    cases step with
    | done b => exact state_pure b
    | yield b => exact ih b

theorem state_range (r : Std.Legacy.Range) (init : β) (f : Nat → β → WGPrefix E (ForInStep β))
    (hf : ∀ x b, StateSafe extra origin replay (f x b)) : StateSafe extra origin replay (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact state_forIn _ init f hf

/-- Both properties describe the exact same observer execution and history. -/
theorem product_combine (g : PrefixM E α)
    (carrier : TransportReplay.Preserves (origin := origin) (replay := replay) g)
    (order : PrefixPreserves (fun h _ => extra h) extra g) : ProductSafe extra origin replay g := by
  intro w h hi
  obtain ⟨suffix,appended,safe,normal⟩ := carrier w h ⟨hi.1,hi.2.1⟩
  obtain ⟨_,_,ordered,after⟩ := order w h hi.2.2
  refine ⟨suffix,appended,⟨safe,ordered⟩,?_⟩
  cases run : (runPrefix g w h).1 with
  | error err => trivial
  | ok out =>
    simp only [run] at normal after ⊢
    exact ⟨normal.1,normal.2,after⟩


/-- A callback's own native endpoint and actual appended history establish
carrier preservation; histories from a different observer are not joined. -/
theorem state_observed (g : WGPrefix E α) (action : WG.M α)
    (erases : ErasesStatePrefix g action)
    (history : StatePrefixPreserves (fun h _ _ => TransportReplay.Safe origin replay h ∧ extra h)
      (fun h => TransportReplay.Safe origin replay h ∧ extra h) g)
    (frame : ∀ h, Preserves (TransportPublication.Inv h) action) :
    StateSafe extra origin replay g := by
  intro w a h hi
  obtain ⟨suffix,appended,safe,_⟩ := history w a h hi.2
  refine ⟨suffix,appended,safe,?_⟩
  cases run : (runPrefix (g.run w) a h).1 with
  | error err => trivial
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    have native : (action.run w).run a = .ok ((value,v),b) := (erases w a h).symm.trans run
    have kept := (hoare_iff_run_ambient _ _ _).mp (frame (h.filterMap origin)) w a value v b hi.1 native
    have grown : TransportPublication.Inv ((h ++ suffix).filterMap origin) v := by
      rw [List.filterMap_append]
      exact kept.append _
    simpa only [run,appended] using And.intro grown safe


open Lean Meta Elab Tactic in
elab "transport_carrier_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe || target.isAppOf ``ProductSafe do
    throwError "not a carrier contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back!.consumeMData else action
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different source head"

open Lean Meta Elab Tactic in
elab "transport_carrier_native " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a native carrier contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``liftWGPrefix do throwError "not a native WG lift"
  let native := action.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := native.getAppFn | throwError "not a native constant"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different native head"

open Lean Meta Elab Tactic in
elab "transport_carrier_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StateSafe || target.isAppOf ``ProductSafe do
    throwError "not a carrier contract"
  let rec head : Nat → Expr → Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if name.toString.startsWith "__do_jp" then e else head n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE name _ value body _ =>
          if name.toString.startsWith "__do_jp" then e else head n (mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Expr.equal e next then e else head n next
        | _ => e
  let .app f action := target | throwError "missing action"
  let next := if action.isAppOf ``liftWGObserver then
      match action with
      | .app outer inner => mkApp outer (head 64 inner)
      | _ => action
    else head 64 action
  if Expr.equal action next then throwError "head unchanged"
  replaceMainGoal [← goal.replaceTargetDefEq (mkApp f next)]

elab "transport_carrier_join_let" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StateSafe || target.isAppOf ``ProductSafe do Lean.throwError "not a carrier contract"
  let .app front observed := target | Lean.throwError "missing action"
  let isProduct := observed.isAppOf ``liftWGObserver
  let action := if isProduct then observed.getAppArgs.back! else observed
  let wrap (a : Lean.Expr) :=
    if isProduct then
      match observed with
      | .app outer _ => Lean.mkApp outer a
      | _ => a
    else a
  let .letE name ty value body _ := action.consumeMData | Lean.throwError "not a let"
  unless name.toString.startsWith "__do_jp" do Lean.throwError "not a join"
  let property (a : Lean.Expr) := Lean.mkApp front (wrap a)
  let valueContract ← Lean.Meta.forallTelescope ty fun args _ => do
    Lean.Meta.mkForallFVars args (property (Lean.mkAppN value args))
  let valueProof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar valueContract
  let (continuation, next) ← Lean.Meta.withLocalDeclD name ty fun fn => do
    let contract ← Lean.Meta.forallTelescope ty fun args _ => do
      Lean.Meta.mkForallFVars args (property (Lean.mkAppN fn args))
    Lean.Meta.withLocalDeclD `transport_carrier_join contract fun hf => do
      let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (property (body.instantiate1 fn))
      let proof ← Lean.Meta.mkLambdaFVars #[fn, hf] next
      pure (proof, next.mvarId!)
  goal.assign (Lean.mkApp2 continuation value valueProof)
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "transport_carrier_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "missing action"
  let action := args.back!.consumeMData
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back! else action
  unless action.getAppFn.isFVar do Lean.throwError "not a local continuation"
  for decl in ← Lean.getLCtx do
    if decl.userName == `transport_carrier_join then
      let proof := Lean.mkAppN decl.toExpr action.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no continuation contract"


macro "transport_carrier_state_step" : tactic => `(tactic| first
  | (transport_carrier_head Pure.pure; exact state_pure _)
  | (transport_carrier_head ForIn.forIn; first | apply state_forIn | apply state_range)
  | (transport_carrier_head Bind.bind; apply state_bind)
  | (transport_carrier_head ite; apply state_ite)
  | transport_carrier_join_let
  | transport_carrier_join_use
  | maintenance_intro
  | transport_carrier_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
