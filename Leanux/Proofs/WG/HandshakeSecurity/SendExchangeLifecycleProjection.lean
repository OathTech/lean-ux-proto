import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeLifecycleSource
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeRemovalProjection

/-! Exact callback projection through device shutdown and deletion. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.SendExchange
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

variable (ρ : E → Option F)
  (sg : {α : Type} → WG.M α → WGPrefix E α)
  (st : {α : Type} → WG.M α → WGPrefix F α)
  (hs : ∀ {α} (a : WG.M α), StateProjectsPrefix ρ id (sg a) (st a))
  (dg : Option PeerId → WGPrefix E Unit) (dt : Option PeerId → WGPrefix F Unit)
  (hd : ∀ peer, StateProjectsPrefix ρ id (dg peer) (dt peer))

include hs hd in
theorem stop_projects : StateProjectsPrefix ρ id (stopWith sg dg) (stopWith st dt) := by
  unfold stopWith
  repeat' first
    | exact hs _
    | exact timersStop_projects ρ sg st hs dg dt hd _
    | (maintenance_head ForIn.forIn; apply loop_projects ρ)
    | handshake_worker_project_step ρ

include hs hd in
theorem down_projects : StateProjectsPrefix ρ id (downWith sg dg) (downWith st dt) := by
  unfold downWith
  exact StateProjectsPrefix.bind ρ id id (hs _) (fun _ => stop_projects ρ sg st hs dg dt hd)

include hs hd in
theorem destruct_projects : StateProjectsPrefix ρ id (destructWith sg dg) (destructWith st dt) := by
  unfold destructWith Configuration.destructWith
  repeat' first
    | exact hs _
    | exact removeAll_projects ρ sg st hs dg dt hd
    | handshake_worker_project_step ρ

theorem envDown_projects {down : PrefixM E Unit} {lower : PrefixM F Unit}
    (hd : ProjectsPrefix ρ id down lower) :
    ProjectsPrefix ρ id (envDownWith (fun {_} a => liftPrefix a) down)
      (envDownWith (fun {_} a => liftPrefix a) lower) := by
  unfold envDownWith
  repeat' first
    | exact hd
    | with_reducible exact projectsPrefix_lift ρ _
    | with_reducible exact projectsPrefix_pure ρ id _
    | with_reducible apply projectsPrefix_bind ρ id id
    | (maintenance_intro; try dsimp only [id])
    | (split <;> try contradiction)
  all_goals exact fun _ _ => rfl

theorem envDelete_projects {down destruct : PrefixM E Unit} {lowerDown lowerDestruct : PrefixM F Unit}
    (hd : ProjectsPrefix ρ id down lowerDown) (hx : ProjectsPrefix ρ id destruct lowerDestruct) :
    ProjectsPrefix ρ id (envDeleteWith (fun {_} a => liftPrefix a) down destruct)
      (envDeleteWith (fun {_} a => liftPrefix a) lowerDown lowerDestruct) :=
  Configuration.envDeleteWith_projects ρ (projectsPrefix_lift ρ _) hd hx

end Leanux.Proofs.WG.HandshakeSecurity.SendExchange
