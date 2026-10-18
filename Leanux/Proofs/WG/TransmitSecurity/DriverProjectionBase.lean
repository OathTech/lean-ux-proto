import Leanux.Proofs.WG.TransmitSecurity.DriverSource
import Leanux.Proofs.Logged.ProjectsOuter

/-! Exact event projection through the shared TX source driver. These laws
preserve the native result and both states, as well as every failed prefix. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

structure HooksProjects (ρ : E → Option F) (g : Hooks E) (a : Hooks F) : Prop where
  handshake : ∀ (sg : PeerId → WGPrefix E Bool) (sa : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (ka : PeerId → WGPrefix F Unit),
    (∀ pid, StateProjectsPrefix ρ id (sg pid) (sa pid)) →
    (∀ pid, StateProjectsPrefix ρ id (kg pid) (ka pid)) →
    StateProjectsPrefix ρ id (g.handshake sg kg) (a.handshake sa ka)
  sendWorker : ProjectsPrefix ρ id g.sendWorker a.sendWorker
  prepare : ProjectsPrefix ρ id g.prepare a.prepare
  counterCheck : ∀ skb pkt, ProjectsPrefix ρ id (g.counterCheck skb pkt) (a.counterCheck skb pkt)
  timerSelected : ∀ d j pid t we,
    ProjectsPrefix ρ id (g.timerSelected d j pid t we) (a.timerSelected d j pid t we)
  selection : ∀ pid, StateProjectsPrefix ρ id (g.selection pid) (a.selection pid)
  confirmation : ∀ pid kid, StateProjectsPrefix ρ id (g.confirmation pid kid) (a.confirmation pid kid)
  session : ∀ pid, StateProjectsPrefix ρ id (g.session pid) (a.session pid)
  reserve : ∀ slot, StateProjectsPrefix ρ id (g.reserve slot) (a.reserve slot)
  allocate : ∀ packets, StateProjectsPrefix ρ id (g.allocate packets) (a.allocate packets)
  create : ∀ pid item, StateProjectsPrefix ρ id (g.create pid item) (a.create pid item)
  front : ∀ family addr packets mtu,
    StateProjectsPrefix ρ id (g.front family addr packets mtu) (a.front family addr packets mtu)
  poll : ProjectsPrefix ρ id g.poll a.poll
  encrypt : ∀ item, ProjectsPrefix ρ id (g.encrypt item) (a.encrypt item)
  transmit : ∀ pid, ProjectsPrefix ρ id (g.transmit pid) (a.transmit pid)

namespace Projection
variable {E F State Outer Inner α β γ : Type} (ρ : E → Option F)

theorem state_pure (x : α) :
    StateProjectsPrefix (Outer := Outer) (Inner := Inner) ρ id (pure x) (pure x) := by
  intro s t h
  rfl

theorem state_lift (a : StateT Outer (StateT Inner (Except Stop)) α) :
    StateProjectsPrefix ρ id (liftStatePrefix a) (liftStatePrefix a) := by
  intro s t h
  change (a.run s |>.run t, h.filterMap ρ) =
    ((a.run s |>.run t).map (fun ((x, u), v) => ((x, u), v)), h.filterMap ρ)
  cases a.run s |>.run t <;> rfl

theorem state_ite (p : Prop) [Decidable p]
    {gt ge : StatePrefixT E Outer Inner α} {yes no : StatePrefixT F Outer Inner α}
    (ht : p → StateProjectsPrefix ρ id gt yes) (he : ¬p → StateProjectsPrefix ρ id ge no) :
    StateProjectsPrefix ρ id (if p then gt else ge) (if p then yes else no) := by
  by_cases hp : p <;> simp only [hp, ↓reduceIte]
  · exact ht hp
  · exact he hp

theorem state_forIn (xs : List γ) (b : β)
    (g : γ → β → StatePrefixT E Outer Inner (ForInStep β))
    (a : γ → β → StatePrefixT F Outer Inner (ForInStep β))
    (ha : ∀ x b, StateProjectsPrefix ρ id (g x b) (a x b)) :
    StateProjectsPrefix ρ id (forIn xs b g) (forIn xs b a) := by
  induction xs generalizing b with
  | nil => exact state_pure ρ b
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply StateProjectsPrefix.bind ρ id id (ha x b)
    intro step
    cases step with
    | done b => exact state_pure ρ b
    | yield b => exact ih b

theorem state_range (r : Std.Legacy.Range) (b : β)
    (g : Nat → β → StatePrefixT E Outer Inner (ForInStep β))
    (a : Nat → β → StatePrefixT F Outer Inner (ForInStep β))
    (ha : ∀ x b, StateProjectsPrefix ρ id (g x b) (a x b)) :
    StateProjectsPrefix ρ id (forIn r b g) (forIn r b a) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact state_forIn ρ _ b g a ha

theorem prefix_forIn (xs : List γ) (b : β)
    (g : γ → β → PrefixT E State (ForInStep β))
    (a : γ → β → PrefixT F State (ForInStep β))
    (ha : ∀ x b, ProjectsPrefix ρ id (g x b) (a x b)) :
    ProjectsPrefix ρ id (forIn xs b g) (forIn xs b a) := by
  induction xs generalizing b with
  | nil => exact projectsPrefix_pure ρ id b
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply projectsPrefix_bind ρ id id (ha x b)
    intro step
    cases step with
    | done b => exact projectsPrefix_pure ρ id b
    | yield b => exact ih b

theorem prefix_range (r : Std.Legacy.Range) (b : β)
    (g : Nat → β → PrefixT E State (ForInStep β))
    (a : Nat → β → PrefixT F State (ForInStep β))
    (ha : ∀ x b, ProjectsPrefix ρ id (g x b) (a x b)) :
    ProjectsPrefix ρ id (forIn r b g) (forIn r b a) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact prefix_forIn ρ _ b g a ha

end Projection

macro "driver_state_step " rho:ident : tactic => `(tactic| first
  | (maintenance_head liftWGPrefix; exact Projection.state_lift $rho _)
  | (maintenance_head Pure.pure; exact Projection.state_pure $rho _)
  | (maintenance_head ForIn.forIn; first | apply Projection.state_forIn $rho | apply Projection.state_range $rho)
  | (maintenance_head Bind.bind; apply StateProjectsPrefix.bind $rho id id)
  | (maintenance_head ite; apply Projection.state_ite $rho)
  | (maintenance_intro; try dsimp only [id])
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

macro "driver_product_step " rho:ident : tactic => `(tactic| first
  | (maintenance_head liftPrefix; exact projectsPrefix_lift $rho _)
  | (maintenance_head Pure.pure; exact projectsPrefix_pure $rho id _)
  | (maintenance_head ForIn.forIn; first | apply Projection.prefix_forIn $rho | apply Projection.prefix_range $rho)
  | (maintenance_head Bind.bind; apply projectsPrefix_bind $rho id id)
  | (maintenance_head ite; apply projectsPrefix_ite $rho _ id)
  | (maintenance_intro; try dsimp only [id])
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

end Leanux.Proofs.WG.TransmitSecurity.Driver
