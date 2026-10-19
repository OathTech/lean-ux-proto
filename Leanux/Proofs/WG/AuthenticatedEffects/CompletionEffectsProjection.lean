import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsSource

/-! Exact old completion journal projection, preserving native packet reads,
socket receipts and every event preceding a later stopped continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure Ops.Projects (ρ : E → Option F) (g : Ops E) (t : Ops F) : Prop where
  step : ∀ {α} (a : WG.M α), ProjectsPrefix ρ id (g.step a) (t.step a)
  peer : ∀ pid, ProjectsPrefix ρ id (g.peer pid) (t.peer pid)
  modifyPeer : ∀ pid f, ProjectsPrefix ρ id (g.modifyPeer pid f) (t.modifyPeer pid f)
  packet : ∀ skb, ProjectsPrefix ρ id (g.packet skb) (t.packet skb)
  completion : ∀ pid item, ProjectsPrefix ρ id (g.completion pid item) (t.completion pid item)
  send : ∀ pid skb packet, ProjectsPrefix ρ id (g.send pid skb packet) (t.send pid skb packet)
  drop : ∀ pid item, ProjectsPrefix ρ id (g.drop pid item) (t.drop pid item)
  dispose : ∀ pid item key, ProjectsPrefix ρ id (g.dispose pid item key) (t.dispose pid item key)
  traversal : ∀ pid, ProjectsPrefix ρ id (g.traversal pid) (t.traversal pid)
  sent : ∀ pid, ProjectsPrefix ρ id (g.sent pid) (t.sent pid)
  dataSent : ∀ pid, ProjectsPrefix ρ id (g.dataSent pid) (t.dataSent pid)
  fresh : ∀ pid, ProjectsPrefix ρ id (g.fresh pid) (t.fresh pid)

private theorem capture_projects (ρ : E → Option F) {g : PrefixM E α} {t : PrefixM F α}
    (h : ProjectsPrefix ρ id g t) : ProjectsPrefix ρ id (captureObserved g) (captureObserved t) := by
  intro w history
  rw [runPrefix_captureObserved,runPrefix_captureObserved,h w history]
  cases runPrefix g w history with
  | mk result events => cases result <;> rfl

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

macro "completion_effects_project " h:ident rho:ident : tactic => `(tactic| first
  | with_reducible exact Ops.Projects.step $h _
  | with_reducible exact Ops.Projects.peer $h _
  | with_reducible exact Ops.Projects.modifyPeer $h _ _
  | with_reducible exact Ops.Projects.packet $h _
  | with_reducible exact Ops.Projects.completion $h _ _
  | with_reducible exact Ops.Projects.send $h _ _ _
  | with_reducible exact Ops.Projects.drop $h _ _
  | with_reducible exact Ops.Projects.dispose $h _ _ _
  | with_reducible exact Ops.Projects.traversal $h _
  | with_reducible exact Ops.Projects.sent $h _
  | with_reducible exact Ops.Projects.dataSent $h _
  | with_reducible exact Ops.Projects.fresh $h _
  | (maintenance_head captureObserved; exact capture_projects $rho (Ops.Projects.packet $h _))
  | (maintenance_head Pure.pure; exact projectsPrefix_pure $rho id _)
  | (maintenance_head Bind.bind; apply projectsPrefix_bind $rho id id)
  | (maintenance_head ite; apply projectsPrefix_ite $rho _ id)
  | (maintenance_head ForIn.forIn; apply project_loop $rho)
  | (maintenance_intro; try dsimp only [id])
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

variable {g : Ops E} {t : Ops F}

theorem complete_projects (ρ : E → Option F) (h : Ops.Projects ρ g t)
    (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix ρ id (completeWith g pid item) (completeWith t pid item) := by
  unfold completeWith TxDisposition.andObs
  repeat' completion_effects_project h ρ

theorem body_projects (ρ : E → Option F) (h : Ops.Projects ρ g t)
    (pid : PeerId) (first : Option (List SkbId)) :
    ProjectsPrefix ρ id (bodyWith g pid first) (bodyWith t pid first) := by
  unfold bodyWith TxDisposition.andObs
  repeat' first
    | with_reducible exact complete_projects ρ h _ _
    | completion_effects_project h ρ

theorem step_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    ProjectsPrefix ρ id (stepWith g pid) (stepWith t pid) := by
  unfold stepWith
  repeat' first
    | with_reducible exact body_projects ρ h _ _
    | completion_effects_project h ρ

end Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects
