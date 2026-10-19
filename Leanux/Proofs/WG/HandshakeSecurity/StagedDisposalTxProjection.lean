import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalTxSource

/-! Exact projection contracts for the actual nested TX repayment source.
The complete old lifetime/disposition history is retained through Stop. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.TxSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure Ops.Projects (ρ : E → Option F) (g : Ops E) (t : Ops F) : Prop where
  step : ∀ {α} (action : WG.M α), ProjectsPrefix ρ id (g.step action) (t.step action)
  access : ∀ {α} (action : MixedM α), ProjectsPrefix ρ id (g.access action) (t.access action)
  event : ∀ event, ProjectsPrefix ρ id (g.event event) (t.event event)
  enqueue : ∀ pid item, ProjectsPrefix ρ id (g.enqueue pid item) (t.enqueue pid item)
  release : ∀ peer, ProjectsPrefix ρ id (g.release peer) (t.release peer)

private theorem project_loop (ρ : E → Option F) (xs : List α) (initial : β)
    (g : α → β → PrefixM E (ForInStep β)) (t : α → β → PrefixM F (ForInStep β))
    (h : ∀ x b, ProjectsPrefix ρ id (g x b) (t x b)) :
    ProjectsPrefix ρ id (forIn xs initial g) (forIn xs initial t) := by
  induction xs generalizing initial with
  | nil => exact projectsPrefix_pure ρ id initial
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply projectsPrefix_bind ρ id id (h x initial)
    intro step
    cases step with
    | done b => exact projectsPrefix_pure ρ id b
    | yield b => exact ih b

macro "disposal_tx_project " h:ident rho:ident : tactic => `(tactic| first
  | with_reducible exact Ops.Projects.step $h _
  | with_reducible exact Ops.Projects.access $h _
  | with_reducible exact Ops.Projects.event $h _
  | with_reducible exact Ops.Projects.enqueue $h _ _
  | with_reducible exact Ops.Projects.release $h _
  | (maintenance_head Pure.pure; exact projectsPrefix_pure $rho id _)
  | (maintenance_head Bind.bind; apply projectsPrefix_bind $rho id id)
  | (maintenance_head ite; apply projectsPrefix_ite $rho _ id)
  | (maintenance_head ForIn.forIn; apply project_loop $rho)
  | (maintenance_intro; try dsimp only [id])
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem publish_projects (ρ : E → Option F) {g : Ops E} {t : Ops F} (h : Ops.Projects ρ g t)
    (item : List SkbId) (state : PacketState) :
    ProjectsPrefix ρ id (publish g item state) (publish t item state) := by
  unfold publish
  repeat' disposal_tx_project h ρ

theorem create_projects (ρ : E → Option F) {g : Ops E} {t : Ops F} (h : Ops.Projects ρ g t)
    (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix ρ id (create g pid item) (create t pid item) := by
  unfold create
  repeat' first
    | with_reducible exact publish_projects ρ h _ _
    | disposal_tx_project h ρ

theorem dispose_projects (ρ : E → Option F) {g : Ops E} {t : Ops F} (h : Ops.Projects ρ g t)
    (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    ProjectsPrefix ρ id (dispose g pid item key) (dispose t pid item key) := by
  unfold dispose
  repeat' disposal_tx_project h ρ

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.TxSource
