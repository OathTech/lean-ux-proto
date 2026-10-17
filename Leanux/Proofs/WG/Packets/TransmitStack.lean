import Leanux.Proofs.WG.Lifetimes.StackSource
import Leanux.Proofs.WG.Packets.TransmitChecks

/-! The existing Stack source preserves the transmit journal invariant under
an explicit contract for its actual TX callback. All other source leaves use
the already checked StackSource composition and canonical product adapters. -/
namespace Leanux.Proofs.WG.TransmitJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes AllowedIps

/-- Saved handoff certificates depend on their own strict prefixes. Only the
current routing observation is transported to a new product endpoint. -/
theorem Inv.store (h : List Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : Inv initial h w) :
    Inv initial h v := by
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev same
  exact ⟨by simpa only [GlobalCompletionState,routingView,device] using hi.1,hi.2⟩

theorem Inv.productStore (h : List Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : Inv initial h w) :
    Inv initial h v :=
  hi.store h w v (congrArg (fun s : ProductStore43 => s.2.2.2) same)

/-- The arbitrary product callback is the only transmit implementation used.
Every original route, classification, reply guard and failed prefix is retained. -/
theorem stack_preserves (initial : FlatTable × FlatTable)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM Event Int)
    (hx : ∀ family addr packets mtu, PrefixPreserves (Inv initial) (Safe initial)
      (xmit family addr packets mtu)) (packet : List UInt8) :
    PrefixPreserves (Inv initial) (Safe initial)
      (stackReceiveWith (receive4With (reply4With xmit)) packet) :=
  stackReceiveWith_preserves (fun _ _ hi => hi.safe) Inv.productStore _
    (fun bytes => receive4With_preserves (fun _ _ hi => hi.safe) Inv.productStore _
      (fun dst reply => reply4With_preserves (fun _ _ hi => hi.safe) Inv.productStore
        xmit hx dst reply) bytes) packet

/-- A native WG/Ambient transmit contract is lifted only at the actual Stack
product boundary; the caller does not assume a post-run initialized invariant. -/
theorem stack_native_preserves (initial : FlatTable × FlatTable)
    (xmit : Nat → Nat → List Packet → Nat → WGPrefix Event Int)
    (hx : ∀ family addr packets mtu,
      StatePrefixPreserves
        (fun h w _ => GlobalCompletionState initial (routes h) w ∧ Checks initial h)
        (Safe initial) (xmit family addr packets mtu)) (packet : List UInt8) :
    PrefixPreserves (Inv initial) (Safe initial)
      (stackReceiveWith (receive4With (reply4With
        (fun family addr packets mtu => liftWGObserver (xmit family addr packets mtu)))) packet) :=
  stack_preserves initial _ (fun family addr packets mtu =>
    (hx family addr packets mtu).liftWGObserver) packet

end Leanux.Proofs.WG.TransmitJoint
