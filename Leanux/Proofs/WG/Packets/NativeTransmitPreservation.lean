import Leanux.Proofs.WG.Packets.NativeTransmit
import Leanux.Proofs.WG.Packets.TransmitPreservation
import Leanux.Proofs.WG.AllowedIps.RoutingTxFrames

/-! Actual transmit execution preserves strict-position handoff checks. The
normal endpoint transports routing through the existing deletion-permitting
relation; a Stop retains the checked journal without inventing a final state. -/
namespace Leanux.Proofs.WG.TransmitJoint
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Packets AllowedIps

/-- The concrete access observer emits no routing completions, including in
its error arms and its possibly stopped send/payment suffix. -/
theorem transmit_routes (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w : WGWorld) (ambient : Ambient) (h : List Event) :
    routes (runWGPrefix (transmit family addr packets mtu) w ambient h).2 = routes h := by
  have projected := congrArg Prod.snd (transmit_projects family addr packets mtu w ambient h)
  change (runWGPrefix (RoutingJoint.access (wgXmitPrefix family addr packets mtu))
    w ambient (h.filterMap oldEvent)).2 =
    (runWGPrefix (transmit family addr packets mtu) w ambient h).2.filterMap oldEvent at projected
  unfold routes
  rw [← projected]
  exact RoutingJoint.access_routing _ w ambient (h.filterMap oldEvent)

/-- Each new receipt uses this actual front entry and its strict routing
prefix. All earlier checks retain their own original positions. -/
theorem transmit_checks (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w : WGWorld) (ambient : Ambient) (h : List Event)
    (routing : GlobalCompletionState initial (routes h) w) (checked : Checks initial h) :
    Checks initial (runWGPrefix (transmit family addr packets mtu) w ambient h).2 :=
  transmitWith_checks family addr packets mtu _ _
    (RoutingJoint.access_appends _) (RoutingJoint.access_routing _)
    (RoutingJoint.access_erases (txFrontPrefix_erases family addr packets mtu))
    w ambient h routing checked

/-- Actual native transmission preserves routing and checked handoffs over
arbitrary incoming histories; failed executions retain their safe prefixes. -/
theorem transmit_preserves (initial : FlatTable × FlatTable)
    (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StatePrefixPreserves
      (fun h w _ => GlobalCompletionState initial (routes h) w ∧ Checks initial h)
      (Safe initial) (transmit family addr packets mtu) :=
  native_preserves initial _ _ (transmit_appends family addr packets mtu)
    (transmit_erases family addr packets mtu) (wgXmit_routing family addr packets mtu)
    (transmit_routes family addr packets mtu) (transmit_checks family addr packets mtu)

/-- The canonical product lift supplies the same invariant for callers. -/
theorem transmit_product (initial : FlatTable × FlatTable)
    (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    PrefixPreserves (Inv initial) (Safe initial)
      (liftWGObserver (transmit family addr packets mtu)) :=
  (transmit_preserves initial family addr packets mtu).liftWGObserver

end Leanux.Proofs.WG.TransmitJoint
