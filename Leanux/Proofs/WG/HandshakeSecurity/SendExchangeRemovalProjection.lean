import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeRemovalSource
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeProjection

/-! Exact retained journal projection through direct configuration drains. -/
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
theorem afterDead_projects (pid : PeerId) :
    StateProjectsPrefix ρ id (afterDeadWith sg dg pid) (afterDeadWith st dt pid) := by
  unfold afterDeadWith
  repeat' first | exact hs _ | exact hd _ | handshake_worker_project_step ρ

include hs hd in
theorem remove_projects (peer : Option PeerId) :
    StateProjectsPrefix ρ id (removeWith sg dg peer) (removeWith st dt peer) := by
  unfold removeWith Configuration.peerRemoveWith
  repeat' first
    | exact hs _
    | exact afterDead_projects ρ sg st hs dg dt hd _
    | handshake_worker_project_step ρ

include hs hd in
theorem removeAll_projects :
    StateProjectsPrefix ρ id (removeAllWith sg dg) (removeAllWith st dt) := by
  unfold removeAllWith Configuration.peerRemoveAllWith
  repeat' first
    | exact hs _
    | exact afterDead_projects ρ sg st hs dg dt hd _
    | (maintenance_head ForIn.forIn; apply loop_projects ρ)
    | handshake_worker_project_step ρ

end Leanux.Proofs.WG.HandshakeSecurity.SendExchange
