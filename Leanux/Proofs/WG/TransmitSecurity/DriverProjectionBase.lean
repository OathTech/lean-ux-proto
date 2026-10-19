import Leanux.Proofs.WG.TransmitSecurity.DriverGroNeutral
import Leanux.Proofs.Logged.ProjectsOuter
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeRemovalProjection
import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsProjection
import Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffectsProjection

/-! Exact event projection through the shared TX source driver. These laws
preserve the native result and both states, as well as every failed prefix. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

structure HooksProjects (ρ : E → Option F) (g : Hooks E) (a : Hooks F) : Prop where
  keepalivePrepare : ∀ pid, StateProjectsPrefix ρ id (g.keepalivePrepare pid) (a.keepalivePrepare pid)
  fixture : ∃ scopeMap : Nat → Nat,
    (∀ trigger, StateProjectsPrefix ρ scopeMap (g.fixtureEnter trigger) (a.fixtureEnter trigger)) ∧
    (∀ token, StateProjectsPrefix ρ id (g.fixtureLeave token) (a.fixtureLeave (scopeMap token)))
  handshake : ∀ (sg : PeerId → WGPrefix E Bool) (sa : PeerId → WGPrefix F Bool)
    (kg : PeerId → WGPrefix E Unit) (ka : PeerId → WGPrefix F Unit),
    (∀ pid, StateProjectsPrefix ρ id (sg pid) (sa pid)) →
    (∀ pid, StateProjectsPrefix ρ id (kg pid) (ka pid)) →
    StateProjectsPrefix ρ id (g.handshake sg kg) (a.handshake sa ka)
  flushedSend : ∀ pid, StateProjectsPrefix ρ id (g.flushedSend pid) (a.flushedSend pid)
  armTimer : ∀ pid timer delay caller,
    StateProjectsPrefix ρ id (g.armTimer pid timer delay caller) (a.armTimer pid timer delay caller)
  queueSend : ∀ pid, StateProjectsPrefix ρ id (g.queueSend pid) (a.queueSend pid)
  candidate : ∃ scopeMap : Nat → Nat,
    (∀ skb pkt, ProjectsPrefix ρ scopeMap (g.candidateEnter skb pkt) (a.candidateEnter skb pkt)) ∧
    (∀ token, ProjectsPrefix ρ id (g.candidateLeave token) (a.candidateLeave (scopeMap token))) ∧
    (∀ entry body targetBody, ProjectsPrefix ρ id body targetBody →
      ProjectsPrefix ρ id (g.stackInput entry body) (a.stackInput (entry.map scopeMap) targetBody))
  prepare : ProjectsPrefix ρ id g.prepare a.prepare
  counterCheck : ∀ skb pkt, ProjectsPrefix ρ id (g.counterCheck skb pkt) (a.counterCheck skb pkt)
  timer : ∃ scopeMap : Nat → Nat,
    (∀ d j pid t we, ProjectsPrefix ρ scopeMap (g.timerSelected d j pid t we) (a.timerSelected d j pid t we)) ∧
    (∀ token, ProjectsPrefix ρ id (g.timerFinished token) (a.timerFinished (scopeMap token)))
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

theorem fixture_projects {E F α : Type} {ρ : E → Option F} {g : Hooks E} {a : Hooks F}
    (h : HooksProjects ρ g a)
    (trigger : AuthenticatedEffects.FixtureEffects.Trigger)
    (body : WGPrefix E α) (target : WGPrefix F α)
    (projects : StateProjectsPrefix ρ id body target) :
    StateProjectsPrefix ρ id
      (AuthenticatedEffects.FixtureEffects.runWith (fixtureOps g) trigger body)
      (AuthenticatedEffects.FixtureEffects.runWith (fixtureOps a) trigger target) := by
  obtain ⟨scopeMap,enter,leave⟩ := h.fixture
  exact AuthenticatedEffects.FixtureEffects.run_projects ρ scopeMap _ _ enter leave trigger body target projects

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

theorem effectOps_projects {ρ : E → Option F} {g : Hooks E} {a : Hooks F}
    (h : HooksProjects ρ g a) :
    AuthenticatedEffects.TimerEffects.Ops.Projects ρ (effectOps g) (effectOps a) where
  step := fun _ => Projection.state_lift ρ _
  arm := h.armTimer
  append := h.queueSend

theorem sendWorker_projects {ρ : E → Option F} {g : Hooks E} {a : Hooks F}
    (h : HooksProjects ρ g a) : ProjectsPrefix ρ id (sendWorkerObserved g) (sendWorkerObserved a) :=
  HandshakeSecurity.SendExchange.one_projects ρ liftPrefix liftPrefix
    (fun _ => projectsPrefix_lift ρ _) _ _ (fun pid => (h.flushedSend pid).liftWGObserver ρ id)

theorem sendDrain_projects {ρ : E → Option F} {g : Hooks E} {a : Hooks F}
    (h : HooksProjects ρ g a) (upTo : Option PeerId) :
    StateProjectsPrefix ρ id (sendDrainObserved g upTo) (sendDrainObserved a upTo) :=
  HandshakeSecurity.SendExchange.drain_projects ρ liftWGPrefix liftWGPrefix
    (fun _ => Projection.state_lift ρ _) _ _ h.flushedSend _ _
    (fun _ => Projection.state_lift ρ _) upTo

theorem remove_projects {ρ : E → Option F} {g : Hooks E} {a : Hooks F}
    (h : HooksProjects ρ g a) (peer : Option PeerId) :
    StateProjectsPrefix ρ id (removeObserved g peer) (removeObserved a peer) :=
  HandshakeSecurity.SendExchange.remove_projects ρ liftWGPrefix liftWGPrefix
    (fun _ => Projection.state_lift ρ _) _ _ (sendDrain_projects h) peer

theorem removeAll_projects {ρ : E → Option F} {g : Hooks E} {a : Hooks F}
    (h : HooksProjects ρ g a) : StateProjectsPrefix ρ id (removeAllObserved g) (removeAllObserved a) :=
  HandshakeSecurity.SendExchange.removeAll_projects ρ liftWGPrefix liftWGPrefix
    (fun _ => Projection.state_lift ρ _) _ _ (sendDrain_projects h)

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
