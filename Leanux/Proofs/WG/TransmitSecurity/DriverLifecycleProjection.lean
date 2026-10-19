import Leanux.Proofs.WG.TransmitSecurity.DriverProjectionBase
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeLifecycleProjection

/-! The same send callback projects through device down and deletion, including
shutdown's nested timer drains and destruction's peer-removal drains. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeSecurity
variable {E F : Type} {ρ : E → Option F} {g : Hooks E} {a : Hooks F}

theorem down_projects (h : HooksProjects ρ g a) :
    StateProjectsPrefix ρ id (downObserved g) (downObserved a) :=
  StagedDisposal.Lifecycle.down_projects ρ liftWGPrefix liftWGPrefix
    (fun _ => Projection.state_lift ρ _) _ _ (sendDrain_projects h) _ _ h.stagedPurge

theorem destruct_projects (h : HooksProjects ρ g a) :
    StateProjectsPrefix ρ id (destructObserved g) (destructObserved a) :=
  StagedDisposal.Lifecycle.destruct_projects ρ liftWGPrefix liftWGPrefix
    (fun _ => Projection.state_lift ρ _) _ _ (sendDrain_projects h) _ _ h.peerRelease

theorem envDown_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (envDownObserved g) (envDownObserved a) :=
  SendExchange.envDown_projects ρ ((down_projects h).liftWGObserver ρ id)

theorem envDelete_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (envDeleteObserved g) (envDeleteObserved a) :=
  SendExchange.envDelete_projects ρ ((down_projects h).liftWGObserver ρ id)
    ((destruct_projects h).liftWGObserver ρ id)

end Leanux.Proofs.WG.TransmitSecurity.Driver
