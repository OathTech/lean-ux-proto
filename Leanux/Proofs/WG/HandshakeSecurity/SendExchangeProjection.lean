import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeSource
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerSource

/-! Exact journal projection for the shared handshake-send spine. In particular,
work flushed directly by configuration uses the same callback execution. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.SendExchange
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

structure Ops.Projects (ρ : E → Option F) (g : Ops (WGPrefix E)) (t : Ops (WGPrefix F)) : Prop where
  step : ∀ {α} (a : WG.M α), StateProjectsPrefix ρ id (g.step a) (t.step a)
  create : ∀ pid, StateProjectsPrefix ρ id (g.create pid) (t.create pid)
  mac : ∀ pid msg, StateProjectsPrefix ρ id (g.mac pid msg) (t.mac pid msg)
  traversal : ∀ pid, StateProjectsPrefix ρ id (g.traversal pid) (t.traversal pid)
  sent : ∀ pid, StateProjectsPrefix ρ id (g.sent pid) (t.sent pid)
  send : ∀ pid msg, StateProjectsPrefix ρ id (g.send pid msg) (t.send pid msg)
  initiated : ∀ pid, StateProjectsPrefix ρ id (g.initiated pid) (t.initiated pid)
  put : ∀ pid, StateProjectsPrefix ρ id (g.put pid) (t.put pid)

macro "send_exchange_project " h:ident rho:ident : tactic => `(tactic| first
  | exact Ops.Projects.step $h _
  | exact Ops.Projects.create $h _
  | exact Ops.Projects.mac $h _ _
  | exact Ops.Projects.traversal $h _
  | exact Ops.Projects.sent $h _
  | exact Ops.Projects.send $h _ _
  | exact Ops.Projects.initiated $h _
  | exact Ops.Projects.put $h _
  | handshake_worker_project_step $rho)

variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

theorem send_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (sendWith g pid) (sendWith t pid) := by
  unfold sendWith
  repeat' send_exchange_project h ρ

theorem worker_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (workerWith g pid) (workerWith t pid) := by
  unfold workerWith
  exact StateProjectsPrefix.bind ρ id id (send_projects ρ h pid) (fun _ => h.put _)

variable (ρ : E → Option F)
  (sg : {α : Type} → WG.M α → WGPrefix E α)
  (st : {α : Type} → WG.M α → WGPrefix F α)
  (hs : ∀ {α} (a : WG.M α), StateProjectsPrefix ρ id (sg a) (st a))
  (wg : PeerId → WGPrefix E Unit) (wt : PeerId → WGPrefix F Unit)
  (hw : ∀ pid, StateProjectsPrefix ρ id (wg pid) (wt pid))

include hs hw in
theorem afterTake_projects (pid : PeerId) :
    StateProjectsPrefix ρ id (afterTakeWith sg wg pid) (afterTakeWith st wt pid) := by
  unfold afterTakeWith
  repeat' first | exact hs _ | exact hw _ | handshake_worker_project_step ρ

include hs hw in
theorem flushed_projects (pid : PeerId) :
    StateProjectsPrefix ρ id (flushedWith sg wg pid) (flushedWith st wt pid) := by
  unfold flushedWith
  exact StateProjectsPrefix.bind ρ id id (hs _) (fun _ => afterTake_projects ρ sg st hs wg wt hw pid)

theorem loop_projects (xs : List α) (initial : β)
    (g : α → β → WGPrefix E (ForInStep β)) (t : α → β → WGPrefix F (ForInStep β))
    (h : ∀ x b, StateProjectsPrefix ρ id (g x b) (t x b)) :
    StateProjectsPrefix ρ id (forIn xs initial g) (forIn xs initial t) := by
  induction xs generalizing initial with
  | nil => intro w a hist; rfl
  | cons x xs ih =>
    rw [List.forIn_cons,List.forIn_cons]
    apply StateProjectsPrefix.bind ρ id id (h x initial)
    intro step
    cases step with
    | done b => intro w a hist; rfl
    | yield b => exact ih b

include hs hw in
theorem drain_projects
    (cg : PeerId → WGPrefix E Unit) (ct : PeerId → WGPrefix F Unit)
    (hc : ∀ pid, StateProjectsPrefix ρ id (cg pid) (ct pid)) (upTo : Option PeerId) :
    StateProjectsPrefix ρ id (drainWith sg wg cg upTo) (drainWith st wt ct upTo) := by
  unfold drainWith
  rw [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | exact hs _
    | exact hw _
    | exact hc _
    | (maintenance_head ForIn.forIn; apply loop_projects ρ)
    | handshake_worker_project_step ρ

theorem one_projects
    (sg : {α : Type} → Leanux.M α → PrefixM E α)
    (st : {α : Type} → Leanux.M α → PrefixM F α)
    (hs : ∀ {α} (a : Leanux.M α), ProjectsPrefix ρ id (sg a) (st a))
    (wg : PeerId → PrefixM E Unit) (wt : PeerId → PrefixM F Unit)
    (hw : ∀ pid, ProjectsPrefix ρ id (wg pid) (wt pid)) :
    ProjectsPrefix ρ id (oneWith sg wg) (oneWith st wt) := by
  unfold oneWith
  exact projectsPrefix_bind ρ id id (hs _) hw

end Leanux.Proofs.WG.HandshakeSecurity.SendExchange
