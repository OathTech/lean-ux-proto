import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationFrontSource
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeErasure
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeProjection

/-! Exact native erasure and callback projection for the transmit front.
The source witnesses and reached first Stop are retained, not joined by
comparing independently erased executions. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Packets
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure Ops.Erases (g : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (action : WG.M α), ErasesStatePrefix (g.step action) action
  put : ∀ peer, ErasesStatePrefix (g.put peer) (peerPut peer)
  trim : ∀ pid, ErasesStatePrefix (g.trim pid) (xmitTrim pid)
  splice : ∀ pid packets, ErasesStatePrefix (g.splice pid packets) (xmitSplice pid packets)

macro "conservation_front_erase " h:ident : tactic => `(tactic| first
  | exact Ops.Erases.step $h _
  | exact Ops.Erases.put $h _
  | exact Ops.Erases.trim $h _
  | exact Ops.Erases.splice $h _ _
  | work_root_erasure_step)

theorem select_erases {g : Ops (WGPrefix E)} (h : Ops.Erases g)
    (family : Nat) (pkts : List Packet) (mtu : Nat) (peer : Option PeerId) :
    ErasesStatePrefix (selectWith g family pkts mtu peer) (txSelect family pkts mtu peer) := by
  cases peer <;> simp only [selectWith,txSelect]
  all_goals repeat' conservation_front_erase h
  all_goals simp_all only [Option.some.injEq]
  all_goals first | exact h.step _ | exact h.trim _ | exact erasesStatePrefix_pure _ | contradiction

theorem front_erases {g : Ops (WGPrefix E)} (h : Ops.Erases g)
    (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    ErasesStatePrefix (frontWith g family addr pkts mtu) (txFront family addr pkts mtu) := by
  unfold frontWith txFront
  repeat' first
    | exact select_erases h _ _ _ _
    | conservation_front_erase h

structure Ops.Projects (ρ : E → Option F) (g : Ops (WGPrefix E)) (t : Ops (WGPrefix F)) : Prop where
  step : ∀ {α} (action : WG.M α), StateProjectsPrefix ρ id (g.step action) (t.step action)
  put : ∀ peer, StateProjectsPrefix ρ id (g.put peer) (t.put peer)
  trim : ∀ pid, StateProjectsPrefix ρ id (g.trim pid) (t.trim pid)
  splice : ∀ pid packets, StateProjectsPrefix ρ id (g.splice pid packets) (t.splice pid packets)

macro "conservation_front_project " h:ident rho:ident : tactic => `(tactic| first
  | exact Ops.Projects.step $h _
  | exact Ops.Projects.put $h _
  | exact Ops.Projects.trim $h _
  | exact Ops.Projects.splice $h _ _
  | handshake_worker_project_step $rho)

theorem select_projects {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}
    (ρ : E → Option F) (h : Ops.Projects ρ g t)
    (family : Nat) (pkts : List Packet) (mtu : Nat) (peer : Option PeerId) :
    StateProjectsPrefix ρ id (selectWith g family pkts mtu peer) (selectWith t family pkts mtu peer) := by
  unfold selectWith
  repeat' conservation_front_project h ρ

theorem front_projects {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}
    (ρ : E → Option F) (h : Ops.Projects ρ g t)
    (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    StateProjectsPrefix ρ id (frontWith g family addr pkts mtu) (frontWith t family addr pkts mtu) := by
  unfold frontWith
  repeat' first
    | exact select_projects ρ h _ _ _ _
    | conservation_front_project h ρ

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
