import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationFrontProjection

/-! History frames for the same callback-parametric transmit front. These are
separate from native erasure: deleting an observation cannot create an exact
history connection between two independent executions. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Packets
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure Ops.HistoryFrame (ρ : E → Option F) (g : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (action : WG.M α), StateHistoryFrame ρ (g.step action)
  put : ∀ peer, StateHistoryFrame ρ (g.put peer)
  trim : ∀ pid, StateHistoryFrame ρ (g.trim pid)
  splice : ∀ pid packets, StateHistoryFrame ρ (g.splice pid packets)

macro "conservation_front_frame " h:ident : tactic => `(tactic| first
  | exact Ops.HistoryFrame.step $h _
  | exact Ops.HistoryFrame.put $h _
  | exact Ops.HistoryFrame.trim $h _
  | exact Ops.HistoryFrame.splice $h _ _
  | exact fun _ _ _ => rfl
  | apply StateHistoryFrame.bind
  | (maintenance_intro; try dsimp only)
  | dsimp (config := {failIfUnchanged := true}) only
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem select_frame {g : Ops (WGPrefix E)} (h : Ops.HistoryFrame ρ g)
    (family : Nat) (pkts : List Packet) (mtu : Nat) (peer : Option PeerId) :
    StateHistoryFrame ρ (selectWith g family pkts mtu peer) := by
  unfold selectWith
  repeat' conservation_front_frame h

theorem front_frame {g : Ops (WGPrefix E)} (h : Ops.HistoryFrame ρ g)
    (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    StateHistoryFrame ρ (frontWith g family addr pkts mtu) := by
  unfold frontWith
  repeat' first
    | exact select_frame h _ _ _ _
    | conservation_front_frame h

structure Ops.Appends (g : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (action : WG.M α), StateAppends (g.step action)
  put : ∀ peer, StateAppends (g.put peer)
  trim : ∀ pid, StateAppends (g.trim pid)
  splice : ∀ pid packets, StateAppends (g.splice pid packets)

macro "conservation_front_appends " h:ident : tactic => `(tactic| first
  | exact Ops.Appends.step $h _
  | exact Ops.Appends.put $h _
  | exact Ops.Appends.trim $h _
  | exact Ops.Appends.splice $h _ _
  | exact StateAppends.pure _
  | apply StateAppends.bind
  | (maintenance_intro; try dsimp only)
  | dsimp (config := {failIfUnchanged := true}) only
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem select_appends {g : Ops (WGPrefix E)} (h : Ops.Appends g)
    (family : Nat) (pkts : List Packet) (mtu : Nat) (peer : Option PeerId) :
    StateAppends (selectWith g family pkts mtu peer) := by
  unfold selectWith
  repeat' conservation_front_appends h

theorem front_appends {g : Ops (WGPrefix E)} (h : Ops.Appends g)
    (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    StateAppends (frontWith g family addr pkts mtu) := by
  unfold frontWith
  repeat' first
    | exact select_appends h _ _ _ _
    | conservation_front_appends h

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
