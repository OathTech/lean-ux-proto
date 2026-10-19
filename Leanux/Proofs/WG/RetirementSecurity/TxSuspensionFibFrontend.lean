import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionFibTable

/-! The actual address/device notifiers and namespace boot retain suspended
worker records. These frames cover native routing effects rather than only the
WG projection, which is insufficient for initialized service transport. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Fib
open Leanux Leanux.Net Leanux.Net.Fib
open Leanux.Proofs.Framing Lifetimes Queues

theorem sync_device (dev : Nat) (down force : Bool) : Keeps (syncDownDev dev down force) := by
  unfold syncDownDev
  simp (config := {zeta := false}) only [Std.TreeMap.forIn_eq_forIn_toList]
  suspension_source [] using [table,table_modify]

theorem flush  : Keeps (fibFlush) := by
  unfold fibFlush
  suspension_source [] using [table_flush,cache_flush]

theorem arp_down (dev : Nat) : Keeps (arpIfdown dev) := by
  unfold arpIfdown
  suspension_source [] using []

theorem disable_ip (dev : Nat) (force : Bool) : Keeps (disableIp dev force) := by
  unfold disableIp
  suspension_source [] using [sync_device,flush,cache_flush,arp_down]

theorem magic (add : Bool) (type : RouteType) (dst len src dev priority : Nat) : Keeps (fibMagic add type dst len src dev priority) := by
  unfold fibMagic
  suspension_source [] using [table_insert,table_delete]

theorem add_addr (dev addr plen : Nat) (up : Bool) : Keeps (addIfaddr dev addr plen up) := by
  unfold addIfaddr
  suspension_source [] using [magic]

theorem sync_addr (dev addr : Nat) : Keeps (syncDownAddr dev addr) := by
  unfold syncDownAddr
  simp (config := {zeta := false}) only [Std.TreeMap.forIn_eq_forIn_toList]
  suspension_source [] using [table,modify_info]

theorem del_addr (dev addr plen : Nat) (dead : Bool) : Keeps (delIfaddr dev addr plen dead) := by
  unfold delIfaddr
  suspension_source [] using [magic,device_addrs,unsupported,inet_type,sync_addr,flush]

theorem addr_up (dev addr plen : Nat) : Keeps (inetaddrUp dev addr plen) := by
  unfold inetaddrUp
  suspension_source [] using [add_addr,device_up,addr_gen,cache_flush]

theorem addr_down (dev addr plen : Nat) (last dead : Bool) : Keeps (inetaddrDown dev addr plen last dead) := by
  unfold inetaddrDown
  suspension_source [] using [del_addr,addr_gen,disable_ip,cache_flush]

theorem netdev_up (dev : Nat) : Keeps (netdevUp dev) := by
  unfold netdevUp
  suspension_source [] using [device_addrs,add_addr,device_plen,addr_gen,cache_flush]

theorem netdev_down (dev : Nat) : Keeps (netdevDown dev) := by
  unfold netdevDown
  suspension_source [] using [disable_ip]

theorem netdev_unregister (dev : Nat) : Keeps (netdevUnregister dev) := by
  unfold netdevUnregister
  suspension_source [] using [disable_ip]

theorem netdev_mtu  : Keeps (netdevChangeMtu) := by
  unfold netdevChangeMtu
  suspension_source [] using [cache_flush]

theorem route_into (already : Bool) (addr : Nat) (routes : List (Nat×Nat)) : Keeps (routeIntoWg0 already addr routes) := by
  unfold routeIntoWg0
  suspension_source [] using [addr_up,table_insert]

theorem delroute  : Keeps (delrouteWg0) := by
  unfold delrouteWg0
  suspension_source [] using [table_delete]

theorem boot  : Keeps (bootTables) := by
  unfold bootTables
  suspension_source [] using [addr_up]

theorem creator_namespace (action : Net.M α) (keeps : Keeps action) : Keeps (inCreatorNs action) := by
  unfold inCreatorNs
  repeat' first | exact keeps | suspension_step

theorem product_routing {action : Net.M α} (keeps : Keeps action) :
    SameView suspended (monadLift action : Leanux.M α) := product (routing_call keeps)

theorem boot_product (foreign : Bool) : SameView suspended
    (do bootTables; if foreign then inCreatorNs bootTables : Leanux.M Unit) := by
  apply (product_routing boot).bind
  intro _
  cases foreign
  · exact SameView.pure _ _
  · exact product_routing (creator_namespace bootTables boot)

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Fib
