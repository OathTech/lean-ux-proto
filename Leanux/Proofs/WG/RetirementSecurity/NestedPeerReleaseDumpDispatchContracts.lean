import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpDispatchErasure
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpDispatchProjection
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpDispatchFrames
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseObservedFrames

/-! The outer dump wrapper specializes to the exact old native dispatch. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeSecurity

/-- Native callbacks recover the original syscall dispatch with every socket,
allocation, autobind and output cut at its original position, including Stop. -/
theorem dumpDispatch_lifted (call : Syscall) :
    (dumpDispatch lifted call : PrefixM E Int) = liftPrefix (Leanux.dispatch call) := by
  funext w h
  have history := dumpDispatch_frame some (lifted_frames some) call w h
  simp only [List.filterMap_some] at history
  exact Prod.ext (dumpDispatch_erases lifted_erases call w h) history

/-- Hiding only nested disposal events recovers the complete old dump dispatch
history; no cursor-funding or successful enclosing-syscall premise is needed. -/
theorem dumpDispatch_old (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (call : Syscall) :
    ProjectsPrefix ρ id (dumpDispatch (observedOps release decode) call)
      (liftPrefix (Leanux.dispatch call)) := by
  rw [←dumpDispatch_lifted]
  exact dumpDispatch_projects ρ (observedOps_projects release decode ρ quiet) call

theorem dumpDispatchObserved_erases (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (call : Syscall) :
    ErasesPrefix (dumpDispatch (observedOps release decode) call) (Leanux.dispatch call) :=
  dumpDispatch_erases (observedOps_erases release decode) call

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
