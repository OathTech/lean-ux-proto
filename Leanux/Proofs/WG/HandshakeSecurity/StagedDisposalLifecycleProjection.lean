import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalLifecycleSource
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeLifecycleProjection

/-! Exact lifecycle projection with separately visible drain, final-release
and purge callbacks. A stopped callback retains its actual event prefix. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
variable (ρ : E → Option F)
  (sg : {α : Type} → WG.M α → WGPrefix E α) (st : {α : Type} → WG.M α → WGPrefix F α)
  (hs : ∀ {α} (a : WG.M α), StateProjectsPrefix ρ id (sg a) (st a))
  (dg : Option PeerId → WGPrefix E Unit) (dt : Option PeerId → WGPrefix F Unit)
  (hd : ∀ peer, StateProjectsPrefix ρ id (dg peer) (dt peer))
  (rg : Option PeerId → WGPrefix E Unit) (rt : Option PeerId → WGPrefix F Unit)
  (hr : ∀ peer, StateProjectsPrefix ρ id (rg peer) (rt peer))

include hs hd hr in
theorem afterDead_projects (pid : PeerId) :
    StateProjectsPrefix ρ id (afterDeadWith sg dg rg pid) (afterDeadWith st dt rt pid) := by
  unfold afterDeadWith
  repeat' first
    | exact hs _
    | exact hd _
    | exact hr _
    | exact SendExchange.timersStop_projects ρ sg st hs dg dt hd _
    | handshake_worker_project_step ρ

include hs hd hr in
theorem remove_projects (peer : Option PeerId) :
    StateProjectsPrefix ρ id (removeWith sg dg rg peer) (removeWith st dt rt peer) := by
  unfold removeWith Configuration.peerRemoveWith
  repeat' first
    | exact hs _
    | exact afterDead_projects ρ sg st hs dg dt hd rg rt hr _
    | handshake_worker_project_step ρ

include hs hd hr in
theorem removeAll_projects :
    StateProjectsPrefix ρ id (removeAllWith sg dg rg) (removeAllWith st dt rt) := by
  unfold removeAllWith Configuration.peerRemoveAllWith
  repeat' first
    | exact hs _
    | exact afterDead_projects ρ sg st hs dg dt hd rg rt hr _
    | (maintenance_head ForIn.forIn; apply SendExchange.loop_projects ρ)
    | handshake_worker_project_step ρ

include hs hd in
theorem stop_projects (pg : PeerId → WGPrefix E Unit) (pt : PeerId → WGPrefix F Unit)
    (hp : ∀ pid, StateProjectsPrefix ρ id (pg pid) (pt pid)) :
    StateProjectsPrefix ρ id (stopWith sg dg pg) (stopWith st dt pt) := by
  unfold stopWith
  repeat' first
    | exact hs _
    | exact hp _
    | exact SendExchange.timersStop_projects ρ sg st hs dg dt hd _
    | (maintenance_head ForIn.forIn; apply SendExchange.loop_projects ρ)
    | handshake_worker_project_step ρ

include hs hd in
theorem down_projects (pg : PeerId → WGPrefix E Unit) (pt : PeerId → WGPrefix F Unit)
    (hp : ∀ pid, StateProjectsPrefix ρ id (pg pid) (pt pid)) :
    StateProjectsPrefix ρ id (downWith sg dg pg) (downWith st dt pt) := by
  unfold downWith
  apply StateProjectsPrefix.bind ρ id id (hs _)
  intro ignored
  exact stop_projects ρ sg st hs dg dt hd pg pt hp

include hs hd hr in
theorem destruct_projects :
    StateProjectsPrefix ρ id (destructWith sg dg rg) (destructWith st dt rt) := by
  unfold destructWith Configuration.destructWith
  repeat' first
    | exact hs _
    | exact removeAll_projects ρ sg st hs dg dt hd rg rt hr
    | handshake_worker_project_step ρ

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle
