import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceFrames
import Leanux.Proofs.WG.TransmitSecurity.DriverSource
import Leanux.Proofs.Logged.PrefixOuter
import Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffectsContracts

/-! History-only safety through the shared native driver. State-dependent
ownership invariants remain separate; this interface cannot discharge them. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged

abbrev StateHistorySafe (Safe : List E → Prop) (g : WGPrefix E α) : Prop :=
  StatePrefixPreserves (fun h _ _ => Safe h) Safe g

abbrev ProductHistorySafe (Safe : List E → Prop) (g : PrefixM E α) : Prop :=
  PrefixPreserves (fun h _ => Safe h) Safe g

structure HooksHistorySafe (Safe : List E → Prop) (hooks : Hooks E) : Prop where
  fixtureEnter : ∀ trigger, StateHistorySafe Safe (hooks.fixtureEnter trigger)
  fixtureLeave : ∀ token, StateHistorySafe Safe (hooks.fixtureLeave token)
  handshake : ∀ (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit),
    (∀ pid, StateHistorySafe Safe (session pid)) →
    (∀ pid, StateHistorySafe Safe (keepalive pid)) →
    StateHistorySafe Safe (hooks.handshake session keepalive)
  sendWorker : ProductHistorySafe Safe (sendWorkerObserved hooks)
  flushedSend : ∀ pid, StateHistorySafe Safe (hooks.flushedSend pid)
  armTimer : ∀ pid timer delay caller, StateHistorySafe Safe (hooks.armTimer pid timer delay caller)
  queueSend : ∀ pid, StateHistorySafe Safe (hooks.queueSend pid)
  candidateEnter : ∀ skb pkt, ProductHistorySafe Safe (hooks.candidateEnter skb pkt)
  candidateLeave : ∀ token, ProductHistorySafe Safe (hooks.candidateLeave token)
  stackInput : ∀ entry body, ProductHistorySafe Safe body →
    ProductHistorySafe Safe (hooks.stackInput entry body)
  prepare : ProductHistorySafe Safe hooks.prepare
  counterCheck : ∀ skb pkt, ProductHistorySafe Safe (hooks.counterCheck skb pkt)
  timerSelected : ∀ d j pid t we, ProductHistorySafe Safe (hooks.timerSelected d j pid t we)
  timerFinished : ∀ token, ProductHistorySafe Safe (hooks.timerFinished token)
  selection : ∀ pid, StateHistorySafe Safe (hooks.selection pid)
  confirmation : ∀ pid kid, StateHistorySafe Safe (hooks.confirmation pid kid)
  session : ∀ pid, StateHistorySafe Safe (hooks.session pid)
  reserve : ∀ kid, StateHistorySafe Safe (hooks.reserve kid)
  allocate : ∀ packets, StateHistorySafe Safe (hooks.allocate packets)
  create : ∀ pid item, StateHistorySafe Safe (hooks.create pid item)
  front : ∀ family addr packets mtu, StateHistorySafe Safe (hooks.front family addr packets mtu)
  poll : ProductHistorySafe Safe hooks.poll
  encrypt : ∀ item, ProductHistorySafe Safe (hooks.encrypt item)
  transmit : ∀ pid, ProductHistorySafe Safe (hooks.transmit pid)

/-- Complete staging is the boundary for properties relating reservations to
allocated packets. Requiring arbitrary allocation arguments to preserve such a
property would discard that source relationship. Other callback contracts stay
explicit and the original native driver remains unchanged. -/
structure ActorHistorySafe (Safe : List E → Prop) (hooks : Hooks E) : Prop where
  staging : ∀ pid, StateHistorySafe Safe (stagingObserved hooks pid)
  fixtureEnter : ∀ trigger, StateHistorySafe Safe (hooks.fixtureEnter trigger)
  fixtureLeave : ∀ token, StateHistorySafe Safe (hooks.fixtureLeave token)
  handshake : ∀ (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit),
    (∀ pid, StateHistorySafe Safe (session pid)) →
    (∀ pid, StateHistorySafe Safe (keepalive pid)) →
    StateHistorySafe Safe (hooks.handshake session keepalive)
  sendWorker : ProductHistorySafe Safe (sendWorkerObserved hooks)
  flushedSend : ∀ pid, StateHistorySafe Safe (hooks.flushedSend pid)
  armTimer : ∀ pid timer delay caller, StateHistorySafe Safe (hooks.armTimer pid timer delay caller)
  queueSend : ∀ pid, StateHistorySafe Safe (hooks.queueSend pid)
  candidateEnter : ∀ skb pkt, ProductHistorySafe Safe (hooks.candidateEnter skb pkt)
  candidateLeave : ∀ token, ProductHistorySafe Safe (hooks.candidateLeave token)
  stackInput : ∀ entry body, ProductHistorySafe Safe body →
    ProductHistorySafe Safe (hooks.stackInput entry body)
  prepare : ProductHistorySafe Safe hooks.prepare
  counterCheck : ∀ skb pkt, ProductHistorySafe Safe (hooks.counterCheck skb pkt)
  timerSelected : ∀ d j pid t we, ProductHistorySafe Safe (hooks.timerSelected d j pid t we)
  timerFinished : ∀ token, ProductHistorySafe Safe (hooks.timerFinished token)
  confirmation : ∀ pid kid, StateHistorySafe Safe (hooks.confirmation pid kid)
  session : ∀ pid, StateHistorySafe Safe (hooks.session pid)
  front : ∀ family addr packets mtu, StateHistorySafe Safe (hooks.front family addr packets mtu)
  poll : ProductHistorySafe Safe hooks.poll
  encrypt : ∀ item, ProductHistorySafe Safe (hooks.encrypt item)
  transmit : ∀ pid, ProductHistorySafe Safe (hooks.transmit pid)

namespace History
variable {Safe : List E → Prop}

theorem state_pure (x : α) : StateHistorySafe Safe (pure x) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi) (fun _ _ _ hi => hi)

theorem state_lift (a : WG.M α) : StateHistorySafe Safe (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ hi => hi) (fun _ _ _ _ _ _ hi _ => hi)

theorem state_bind {g : WGPrefix E α} {f : α → WGPrefix E β}
    (hg : StateHistorySafe Safe g) (hf : ∀ x, StateHistorySafe Safe (f x)) :
    StateHistorySafe Safe (g >>= f) := StatePrefixEnsures.bind hg hf

theorem state_ite (p : Prop) [Decidable p] {a b : WGPrefix E α}
    (ha : p → StateHistorySafe Safe a) (hb : ¬p → StateHistorySafe Safe b) :
    StateHistorySafe Safe (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

theorem state_forIn (xs : List α) (init : β) (f : α → β → WGPrefix E (ForInStep β))
    (hf : ∀ x b, StateHistorySafe Safe (f x b)) :
    StateHistorySafe Safe (forIn xs init f) := by
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
    (hf : ∀ x b, StateHistorySafe Safe (f x b)) : StateHistorySafe Safe (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact state_forIn _ init f hf

theorem product_pure (x : α) : ProductHistorySafe Safe (pure x) :=
  PrefixPreserves.pure (fun h (_ : World) (hi : Safe h) => hi) x

theorem product_lift (a : Leanux.M α) : ProductHistorySafe Safe (liftPrefix a) :=
  (PrefixEnsures.lift (P := fun h (_ : World) => Safe h) (S := Safe)
    (Q := fun _ h (_ : World) => Safe h) a (fun _ _ hi => hi) (fun _ _ _ _ hi _ => hi)).preserves

theorem product_state {g : WGPrefix E α} (hg : StateHistorySafe Safe g) :
    ProductHistorySafe Safe (liftWGObserver g) := hg.liftWGObserver

theorem product_bind {g : PrefixM E α} {f : α → PrefixM E β}
    (hg : ProductHistorySafe Safe g) (hf : ∀ x, ProductHistorySafe Safe (f x)) :
    ProductHistorySafe Safe (g >>= f) := PrefixPreserves.bind hg hf

theorem product_ite (p : Prop) [Decidable p] {a b : PrefixM E α}
    (ha : p → ProductHistorySafe Safe a) (hb : ¬p → ProductHistorySafe Safe b) :
    ProductHistorySafe Safe (if p then a else b) := PrefixPreserves.ite p ha hb

theorem product_forIn (xs : List α) (init : β) (f : α → β → PrefixM E (ForInStep β))
    (hf : ∀ x b, ProductHistorySafe Safe (f x b)) :
    ProductHistorySafe Safe (forIn xs init f) :=
  PrefixPreserves.forIn xs init f (fun _ _ hi => hi) hf

theorem product_range (r : Std.Legacy.Range) (init : β) (f : Nat → β → PrefixM E (ForInStep β))
    (hf : ∀ x b, ProductHistorySafe Safe (f x b)) : ProductHistorySafe Safe (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact product_forIn _ init f hf

end History

open Lean Meta Elab Tactic in
elab "driver_history_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateHistorySafe || target.isAppOf ``ProductHistorySafe do
    throwError "not a history-only contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back!.consumeMData else action
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different source head"

open Lean Meta Elab Tactic in
elab "driver_history_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StateHistorySafe || target.isAppOf ``ProductHistorySafe do
    throwError "not a history-only contract"
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

elab "driver_history_join_let" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StateHistorySafe || target.isAppOf ``ProductHistorySafe do Lean.throwError "not a history contract"
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
    Lean.Meta.withLocalDeclD `driver_history_join contract fun hf => do
      let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (property (body.instantiate1 fn))
      let proof ← Lean.Meta.mkLambdaFVars #[fn, hf] next
      pure (proof, next.mvarId!)
  goal.assign (Lean.mkApp2 continuation value valueProof)
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "driver_history_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "missing action"
  let action := args.back!.consumeMData
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back! else action
  unless action.getAppFn.isFVar do Lean.throwError "not a local continuation"
  for decl in ← Lean.getLCtx do
    if decl.userName == `driver_history_join then
      let proof := Lean.mkAppN decl.toExpr action.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no continuation contract"

macro "driver_state_history_step" : tactic => `(tactic| first
  | (driver_history_head liftWGPrefix; exact History.state_lift _)
  | (driver_history_head Pure.pure; exact History.state_pure _)
  | (driver_history_head ForIn.forIn; first | apply History.state_forIn | apply History.state_range)
  | (driver_history_head Bind.bind; apply History.state_bind)
  | (driver_history_head ite; apply History.state_ite)
  | driver_history_join_let
  | driver_history_join_use
  | maintenance_intro
  | driver_history_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

macro "driver_product_history_step" : tactic => `(tactic| first
  | (driver_history_head liftPrefix; exact History.product_lift _)
  | (driver_history_head Pure.pure; exact History.product_pure _)
  | (driver_history_head ForIn.forIn; first | apply History.product_forIn | apply History.product_range)
  | (driver_history_head Bind.bind; apply History.product_bind)
  | (driver_history_head ite; apply History.product_ite)
  | driver_history_join_let
  | driver_history_join_use
  | maintenance_intro
  | driver_history_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem fixture_history {E α : Type} {Safe : List E → Prop} {hooks : Hooks E}
    (h : ActorHistorySafe Safe hooks)
    (trigger : AuthenticatedEffects.FixtureEffects.Trigger) (body : WGPrefix E α)
    (history : StateHistorySafe Safe body) : StateHistorySafe Safe
      (AuthenticatedEffects.FixtureEffects.runWith (fixtureOps hooks) trigger body) :=
  AuthenticatedEffects.FixtureEffects.run_preserves _ _ _
    (fun _ _ _ before => before) (h.fixtureEnter trigger) h.fixtureLeave history

end Leanux.Proofs.WG.TransmitSecurity.Driver
