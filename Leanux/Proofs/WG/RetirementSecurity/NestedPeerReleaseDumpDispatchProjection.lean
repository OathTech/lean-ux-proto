import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpDispatchSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpProjection

/-! Exact callback and history projection for all outer dump syscall arms. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged Configuration
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem dumpDispatchWith_projects (ρ : E → Option F)
    (device : DeviceRef → PrefixM E (Except Int Lean.Json))
    (start : Nat → DeviceRef → PrefixM E Unit)
    (receive : Nat → PrefixM E (Option (List NlMessage)))
    (device' : DeviceRef → PrefixM F (Except Int Lean.Json))
    (start' : Nat → DeviceRef → PrefixM F Unit)
    (receive' : Nat → PrefixM F (Option (List NlMessage)))
    (hd : ∀ ref, ProjectsPrefix ρ id (device ref) (device' ref))
    (hs : ∀ fd ref, ProjectsPrefix ρ id (start fd ref) (start' fd ref))
    (hr : ∀ fd, ProjectsPrefix ρ id (receive fd) (receive' fd)) (call : Syscall) :
    ProjectsPrefix ρ id (dumpDispatchWith liftPrefix device start receive call)
      (dumpDispatchWith liftPrefix device' start' receive' call) := by
  cases call <;> simp only [dumpDispatchWith]
  all_goals repeat' first
    | with_reducible exact hd _
    | with_reducible exact hs _ _
    | with_reducible exact hr _
    | with_reducible apply netlinkRequestWith_projects ρ
    | with_reducible apply socketCallOnWith_projects ρ
    | with_reducible exact projectsPrefix_lift ρ _
    | with_reducible exact projectsPrefix_pure ρ id _
    | with_reducible apply projectsPrefix_bind ρ id id
    | split
    | contradiction
    | rfl
    | (intro x; try dsimp only [id])

theorem dumpDispatch_projects (ρ : E → Option F)
    {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)} (h : Ops.Projects ρ g t) (call : Syscall) :
    ProjectsPrefix ρ id (dumpDispatch g call) (dumpDispatch t call) :=
  dumpDispatchWith_projects ρ _ _ _ _ _ _
    (fun ref => StateProjectsPrefix.liftWGObserver ρ id (dumpDevice_projects ρ h ref))
    (fun fd ref => StateProjectsPrefix.liftWGObserver ρ id (dumpStart_projects ρ h fd ref))
    (fun fd => StateProjectsPrefix.liftWGObserver ρ id (dumpReceive_projects ρ h fd)) call

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
