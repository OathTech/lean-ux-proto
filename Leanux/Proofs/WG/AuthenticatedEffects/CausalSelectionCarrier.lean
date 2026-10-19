import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionActors
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedOuter

/-! Live delayed occurrences and positional selection evidence describe one
observer execution. Native frames are reused; selected receipts are checked at
their actual guarded call, before any subsequent Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity
open Leanux.Proofs.Framing Lifetimes Std.Do

abbrev StateSafe (body : WGPrefix Event α) :=
  StatePrefixPreserves (fun h w _ => Inv h w) Safe body
abbrev ProductSafe (body : PrefixM Event α) :=
  PrefixPreserves (fun h w => Inv h w.wg) Safe body

theorem state_combine (body : WGPrefix Event α) (carrier : Delayed.StateSafe body)
    (history : Driver.StateHistorySafe Safe body) : StateSafe body := by
  intro w a h input
  obtain ⟨suffix,grown,_,output⟩ := carrier w a h input.1
  obtain ⟨_,_,safe,normal⟩ := history w a h input.2
  refine ⟨suffix,grown,safe,?_⟩
  cases run : (runPrefix (body.run w) a h).1 with
  | error _ => trivial
  | ok result =>
    simp only [run] at output normal ⊢
    exact ⟨output,normal⟩

theorem product_combine (body : PrefixM Event α) (carrier : Delayed.ProductSafe body)
    (history : Driver.ProductHistorySafe Safe body) : ProductSafe body := by
  intro w h input
  obtain ⟨suffix,grown,_,output⟩ := carrier w h input.1
  obtain ⟨_,_,safe,normal⟩ := history w h input.2
  refine ⟨suffix,grown,safe,?_⟩
  cases run : (runPrefix body w h).1 with
  | error _ => trivial
  | ok result =>
    simp only [run] at output normal ⊢
    exact ⟨output,normal⟩

theorem state_native (action : WG.M α) (carrier : Delayed.StateSafe (liftWGPrefix action)) :
    StateSafe (liftWGPrefix action) := state_combine _ carrier (Driver.History.state_lift _)

theorem product_native (action : Leanux.M α) (carrier : Delayed.ProductSafe (liftPrefix action)) :
    ProductSafe (liftPrefix action) := product_combine _ carrier (Driver.History.product_lift _)

theorem state_pure (value : α) : StateSafe (pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi)

theorem state_bind {body : WGPrefix Event α} {next : α → WGPrefix Event β}
    (safe : StateSafe body) (tail : ∀ value, StateSafe (next value)) : StateSafe (body >>= next) :=
  StatePrefixEnsures.bind safe tail

theorem state_ite (p : Prop) [Decidable p] {left right : WGPrefix Event α}
    (hl : p → StateSafe left) (hr : ¬p → StateSafe right) : StateSafe (if p then left else right) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact hl hp
  · exact hr hp

theorem state_forIn {α β : Type} (xs : List α) (initial : β)
    (body : α → β → WGPrefix Event (ForInStep β))
    (safe : ∀ value state, StateSafe (body value state)) : StateSafe (forIn xs initial body) :=
  StatePrefixEnsures.forInInvariant xs initial body (fun _ h w _ => Inv h w) Safe
    (fun _ _ _ _ hi => hi.2) safe

theorem product_pure (value : α) : ProductSafe (pure value) :=
  PrefixPreserves.pure (fun _ _ hi => hi.2) value

theorem product_bind {body : PrefixM Event α} {next : α → PrefixM Event β}
    (safe : ProductSafe body) (tail : ∀ value, ProductSafe (next value)) : ProductSafe (body >>= next) :=
  PrefixPreserves.bind safe tail

theorem product_ite (p : Prop) [Decidable p] {left right : PrefixM Event α}
    (hl : p → ProductSafe left) (hr : ¬p → ProductSafe right) : ProductSafe (if p then left else right) :=
  PrefixPreserves.ite p hl hr

theorem product_forIn {α β : Type} (xs : List α) (initial : β)
    (body : α → β → PrefixM Event (ForInStep β))
    (safe : ∀ value state, ProductSafe (body value state)) : ProductSafe (forIn xs initial body) :=
  PrefixPreserves.forIn xs initial body (fun _ _ hi => hi.2) safe

theorem product_range (r : Std.Legacy.Range) (initial : β)
    (body : Nat → β → PrefixM Event (ForInStep β))
    (safe : ∀ value state, ProductSafe (body value state)) : ProductSafe (forIn r initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact product_forIn _ initial body safe

theorem product_state {body : WGPrefix Event α} (safe : StateSafe body) :
    ProductSafe (liftWGObserver body) := safe.liftWGObserver

theorem product_store (h : List Event) (w v : World)
    (same : productStoreView v = productStoreView w) (input : Inv h w.wg) : Inv h v.wg :=
  ⟨Delayed.product_store h w v same input.1,input.2⟩

theorem staging (pid : PeerId) : StateSafe (Driver.stagingObserved hooks pid) :=
  state_combine _ (Delayed.staging pid) (staging_history pid)

theorem keepalive (pid : PeerId) : StateSafe (Driver.keepaliveObserved hooks pid) :=
  state_combine _ (Delayed.keepalive pid) (keepalive_history pid)

theorem handshake : StateSafe (Driver.handshakeObserved hooks) :=
  state_combine _ Delayed.handshake_worker handshake_history

theorem timer_callback (pid : PeerId) (timer : PeerTimer) : StateSafe (Driver.timerObserved hooks pid timer) :=
  state_combine _ (Delayed.timer_callback pid timer) (timer_history pid timer)

theorem device_transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Driver.transmitObserved hooks family addr packets mtu) :=
  state_combine _ (Delayed.device_transmit family addr packets mtu) (transmit_history family addr packets mtu)

theorem softirq : ProductSafe (Driver.softirqObserved hooks) :=
  product_combine _ Delayed.softirq softirq_history

theorem inline_poll : ProductSafe (Driver.inlinePollObserved hooks) :=
  product_combine _ Delayed.inline_poll inline_history

theorem schedule (stack : Option Worker) : ProductSafe (Driver.scheduleObserved hooks stack) :=
  product_combine _ (Delayed.schedule stack) (schedule_history stack)

open Lean Meta Elab Tactic in
elab "selection_carrier_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe || target.isAppOf ``ProductSafe do throwError "not a selector carrier contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back!.consumeMData else action
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different source head"

macro "selection_carrier_step" : tactic => `(tactic| first
  | (selection_carrier_head Pure.pure; exact product_pure _)
  | (selection_carrier_head Bind.bind; apply product_bind)
  | (selection_carrier_head ite; apply product_ite)
  | (selection_carrier_head ForIn.forIn; first | apply product_range | apply product_forIn)
  | maintenance_intro
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

macro "selection_state_step" : tactic => `(tactic| first
  | (selection_carrier_head Pure.pure; exact state_pure _)
  | (selection_carrier_head Bind.bind; apply state_bind)
  | (selection_carrier_head ite; apply state_ite)
  | (selection_carrier_head ForIn.forIn; apply state_forIn)
  | maintenance_intro
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
