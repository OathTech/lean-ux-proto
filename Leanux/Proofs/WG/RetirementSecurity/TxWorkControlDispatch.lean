import Leanux.Proofs.WG.RetirementSecurity.TxWorkNamespaceClose

/-! Actual dispatch wrappers for native configuration, routing and lifecycle
controls retain pending allocated-TX service at empty-local boundaries. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem dispatch_configure_actor (attrs : DeviceAttrs) :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgSet attrs)) :=
  netlink_actor _ (set_device_actor attrs)

theorem dispatch_create_actor  :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgCreate)) :=
  rtnetlink_actor _ create_actor

theorem dispatch_up_actor  :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgUp)) :=
  socket_actor _ _ env_up_actor

theorem dispatch_down_actor  :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgDown)) :=
  socket_actor _ _ env_down_actor

theorem dispatch_delete_actor  :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgDelete)) :=
  rtnetlink_actor _ env_delete_actor

theorem dispatch_mtu_actor (mtu : Nat) :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgSetMtu mtu)) :=
  socket_actor _ _ (env_mtu_actor mtu)

theorem dispatch_deladdr_actor (family : Nat) :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgDeladdr family)) :=
  rtnetlink_actor _ (deladdr_actor family)

theorem dispatch_delroute_actor (family : Nat) (named : Bool) (dst plen oif kind metric : Nat) :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgDelroute family named dst plen oif kind metric)) :=
  rtnetlink_actor _ (delroute_actor family named dst plen oif kind metric)

theorem dispatch_addroute_actor (dst plen oif kind metric mtu flags : Nat) :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgAddroute dst plen oif kind metric mtu flags)) :=
  rtnetlink_actor _ (addroute_actor dst plen oif kind metric mtu flags)

theorem dispatch_addaddr_actor (addr plen : Nat) :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgAddaddr addr plen)) :=
  rtnetlink_actor _ (addaddr_actor addr plen)

theorem dispatch_namespace_actor  :
    Preserves (At (Covered [] []) [] active) (dispatch (.wgNetnsClose)) :=
  namespace_close_actor

end Leanux.Proofs.WG.RetirementSecurity.TxWork
