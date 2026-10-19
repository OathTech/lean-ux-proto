import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalPeerSource
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeErasure
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeProjection

/-! Exact projection of the counted peer-release cut, retaining the original
access observations rather than comparing separately erased executions. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.PeerSource
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure Ops.Erases (g : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (action : WG.M α), ErasesStatePrefix (g.step action) action
  read : ∀ pid, ErasesStatePrefix (g.read pid) (getPeer pid)
  write : ∀ pid p, ErasesStatePrefix (g.write pid p) (setPeer pid p)
  erase : ∀ pid dropped, ErasesStatePrefix (g.erase pid dropped)
    (modifyDev fun d => {d with txDropped := d.txDropped + dropped, peers := d.peers.erase pid})

macro "disposal_peer_erase " h:ident : tactic => `(tactic| first
  | exact Ops.Erases.step $h _
  | exact Ops.Erases.read $h _
  | exact Ops.Erases.write $h _ _
  | exact Ops.Erases.erase $h _ _
  | work_root_erasure_step)

theorem cut_erases {g : Ops (WGPrefix E)} (h : Ops.Erases g) (peer : Option PeerId) :
    ErasesStatePrefix (cutWith g peer) (releaseCut peer) := by
  cases peer <;> simp only [cutWith, releaseCut]
  all_goals repeat' disposal_peer_erase h

theorem put_erases {g : Ops (WGPrefix E)} (h : Ops.Erases g) (peer : Option PeerId) :
    ErasesStatePrefix (putWith g peer) (peerPut peer) := by
  rw [release_factor]
  unfold putWith
  apply erasesStatePrefix_bind (cut_erases h peer)
  intro result
  cases result with
  | none => exact erasesStatePrefix_pure _
  | some out => exact h.step _

theorem peers_erases : Ops.Erases peers where
  step := fun _ => erasesStatePrefix_lift _
  read := Peers.getPeerPrefix_erases
  write := Peers.setPeerPrefix_erases
  erase := Peers.erasePeerPrefix_erases

structure Ops.Projects (ρ : E → Option F) (g : Ops (WGPrefix E))
    (t : Ops (WGPrefix F)) : Prop where
  step : ∀ {α} (action : WG.M α), StateProjectsPrefix ρ id (g.step action) (t.step action)
  read : ∀ pid, StateProjectsPrefix ρ id (g.read pid) (t.read pid)
  write : ∀ pid p, StateProjectsPrefix ρ id (g.write pid p) (t.write pid p)
  erase : ∀ pid dropped, StateProjectsPrefix ρ id (g.erase pid dropped) (t.erase pid dropped)

macro "disposal_peer_project " h:ident rho:ident : tactic => `(tactic| first
  | exact Ops.Projects.step $h _
  | exact Ops.Projects.read $h _
  | exact Ops.Projects.write $h _ _
  | exact Ops.Projects.erase $h _ _
  | handshake_worker_project_step $rho)

theorem cut_projects {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}
    (ρ : E → Option F) (h : Ops.Projects ρ g t) (peer : Option PeerId) :
    StateProjectsPrefix ρ id (cutWith g peer) (cutWith t peer) := by
  unfold cutWith
  repeat' disposal_peer_project h ρ

theorem put_projects {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}
    (ρ : E → Option F) (h : Ops.Projects ρ g t) (peer : Option PeerId) :
    StateProjectsPrefix ρ id (putWith g peer) (putWith t peer) := by
  unfold putWith
  repeat' first
    | exact cut_projects ρ h peer
    | disposal_peer_project h ρ

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.PeerSource
