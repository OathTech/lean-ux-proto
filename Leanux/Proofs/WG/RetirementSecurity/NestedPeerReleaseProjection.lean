import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseSource
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerParametric

/-! Callback contracts for the original nested peer-release paths, including Stop prefixes. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

structure Ops.Projects (ρ : E → Option F) (g : Ops (WGPrefix E)) (t : Ops (WGPrefix F)) : Prop where
  step : ∀ {α} (a : WG.M α), StateProjectsPrefix ρ id (g.step a) (t.step a)
  release : ∀ peer, StateProjectsPrefix ρ id (g.release peer) (t.release peer)

macro "nested_release_project " h:ident rho:ident : tactic => `(tactic| first
  | with_reducible exact Ops.Projects.step $h _
  | with_reducible exact Ops.Projects.release $h _
  | handshake_worker_project_step $rho)

variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

theorem initiationOut_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (peer ret : Option PeerId) :
    StateProjectsPrefix ρ id (initiationOutWith g peer ret) (initiationOutWith t peer ret) := by
  unfold initiationOutWith
  repeat' first
    | nested_release_project h ρ

theorem initiationTail_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (msg e ck hash : Key) (peer : Option PeerId) (pid : PeerId) :
    StateProjectsPrefix ρ id (initiationTailWith g msg e ck hash peer pid) (initiationTailWith t msg e ck hash peer pid) := by
  unfold initiationTailWith
  repeat' first
    | with_reducible exact initiationOut_projects ρ h _ _
    | nested_release_project h ρ

theorem initiationCheck_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (msg : Key) :
    StateProjectsPrefix ρ id (initiationCheckWith g msg) (initiationCheckWith t msg) := by
  unfold initiationCheckWith
  repeat' first
    | with_reducible exact initiationOut_projects ρ h _ _
    | with_reducible exact initiationTail_projects ρ h _ _ _ _ _ _
    | nested_release_project h ρ

theorem responseTail_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (msg : Key) (identity : StaticIdentity) (pid : PeerId) :
    StateProjectsPrefix ρ id (responseTailWith g msg identity pid) (responseTailWith t msg identity pid) := by
  unfold responseTailWith
  repeat' first
    | nested_release_project h ρ

theorem responseCheck_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (msg : Key) :
    StateProjectsPrefix ρ id (responseCheckWith g msg) (responseCheckWith t msg) := by
  unfold responseCheckWith
  repeat' first
    | with_reducible exact responseTail_projects ρ h _ _ _
    | nested_release_project h ρ

theorem cookieAfter_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) (cookie : Option Key) :
    StateProjectsPrefix ρ id (cookieAfterWith g pid cookie) (cookieAfterWith t pid cookie) := by
  unfold cookieAfterWith
  repeat' first
    | nested_release_project h ρ

theorem cookie_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (msg : Key) :
    StateProjectsPrefix ρ id (cookieWith g msg) (cookieWith t msg) := by
  unfold cookieWith
  repeat' first
    | with_reducible exact cookieAfter_projects ρ h _ _
    | nested_release_project h ρ

theorem clear_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (clearWith g pid) (clearWith t pid) := by
  unfold clearWith
  repeat' first
    | nested_release_project h ρ

theorem flushedClear_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) :
    StateProjectsPrefix ρ id (flushedClearWith g pid) (flushedClearWith t pid) := by
  unfold flushedClearWith
  repeat' first
    | with_reducible exact clear_projects ρ h _
    | nested_release_project h ρ

theorem cleanup_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (skb : SkbId) (pkt : RxPacket) (flag : Bool) :
    StateProjectsPrefix ρ id (cleanupWith g skb pkt flag) (cleanupWith t skb pkt flag) := by
  unfold cleanupWith
  repeat' first
    | nested_release_project h ρ

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
