import Leanux.Proofs.WG.RetirementSecurity.TxWorkControls

/-! Actual fixture routing requests and post-up route installation retain
pending TX service and suspended actors. Saved routing writes and native FIB
callbacks stay on their original execution path. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem deladdr_actor (family : Nat) :
    Preserves (At (Covered locals crypt) crypt active) (Env.wgDeladdr family) := by
  unfold Env.wgDeladdr
  repeat' actor_control_step

theorem delroute_actor (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    Preserves (At (Covered locals crypt) crypt active)
      (Env.wgDelroute family named dst plen oif typeCode metric) := by
  unfold Env.wgDelroute
  repeat' first
    | (allocation_release_lift_from Net.M; exact actor_routing TxSuspension.Fib.delroute)
    | actor_control_step

theorem addroute_actor (dst plen oif typeCode metric mtu flags : Nat) :
    Preserves (At (Covered locals crypt) crypt active)
      (Env.wgAddroute dst plen oif typeCode metric mtu flags) := by
  unfold Env.wgAddroute
  repeat' actor_control_step

theorem addaddr_actor (addr plen : Nat) :
    Preserves (At (Covered locals crypt) crypt active) (Env.wgAddaddr addr plen) := by
  unfold Env.wgAddaddr
  repeat' actor_control_step

theorem outside_actor (body : Leanux.M α) (keeps : Preserves (At P crypt active) body) :
    Preserves (At P crypt active) (Env.outsideWindow body) := by
  unfold Env.outsideWindow
  repeat' first | exact keeps | actor_neutral_step

theorem route_into_actor :
    Preserves (At (Covered locals crypt) crypt active) Env.routeIntoWg0 := by
  unfold Env.routeIntoWg0
  repeat' first
    | (rx_retention_head Env.outsideWindow; apply outside_actor)
    | (allocation_release_lift_from Net.M; exact actor_routing (TxSuspension.Fib.route_into _ _ _))
    | actor_control_step

end Leanux.Proofs.WG.RetirementSecurity.TxWork
