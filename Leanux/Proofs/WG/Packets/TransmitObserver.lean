import Leanux.Proofs.WG.Packets.TransmitReceipts

/-! The handoff is emitted between the actual completed front and its original
tail. The tail receives the reached journal; its Stop retains that handoff. -/
namespace Leanux.Proofs.WG.TransmitJoint
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Packets

def transmitWith (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId))
    (tail : PeerId → WGPrefix RoutingJoint.Event Int) : WGPrefix Event Int := do
  let result ← observeFront family addr packets mtu front
  match result with
  | .error err => pure err
  | .ok pid => old (tail pid)

/-- Both supplied observers run on their actual previous output, including
arbitrary older journal entries. The result mapping is the identity. -/
theorem transmitWith_projects (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId))
    (tail : PeerId → WGPrefix RoutingJoint.Event Int)
    (hf : StateAppends front) (ht : ∀ pid, StateAppends (tail pid)) :
    StateProjectsPrefix oldEvent id (transmitWith family addr packets mtu front tail)
      (do match ← front with
          | .error err => pure err
          | .ok pid => tail pid) := by
  unfold transmitWith
  apply StateProjectsPrefix.bind oldEvent id id (observeFront_projects family addr packets mtu front hf)
  intro result
  cases result with
  | error err => intro w; exact projectsPrefix_pure oldEvent (Prod.map id id) (err,w)
  | ok pid => exact old_projects (tail pid) (ht pid)

theorem transmitWith_appends (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId))
    (tail : PeerId → WGPrefix RoutingJoint.Event Int) :
    StateAppends (transmitWith family addr packets mtu front tail) := by
  unfold transmitWith
  apply StateAppends.bind (observeFront_appends family addr packets mtu front)
  intro result
  cases result with
  | error err => exact StateAppends.pure err
  | ok pid => exact old_appends (tail pid)

/-- Tail execution introduces no additional handoffs in this leaf observer;
any receipt emitted by the front survives every tail outcome, including Stop. -/
theorem transmitWith_receipts (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId))
    (tail : PeerId → WGPrefix RoutingJoint.Event Int)
    (w : WGWorld) (ambient : Ambient) (h : List Event) :
    (runWGPrefix (transmitWith family addr packets mtu front tail) w ambient h).2.filterMap receiptEvent =
      (runWGPrefix (observeFront family addr packets mtu front) w ambient h).2.filterMap receiptEvent := by
  change (runStatePrefix (transmitWith family addr packets mtu front tail) w ambient h).2.filterMap receiptEvent = _
  rw [transmitWith,runStatePrefix_bind]
  simp only [runWGPrefix]
  cases run : runStatePrefix (observeFront family addr packets mtu front) w ambient h with
  | mk result hist =>
    cases result with
    | error stop => rfl
    | ok out =>
      rcases out with ⟨⟨result,v⟩,after⟩
      cases result with
      | error err => rfl
      | ok pid => exact old_receipts (tail pid) v after hist

theorem transmitWith_valid (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (front : WGPrefix RoutingJoint.Event (Except Int PeerId))
    (tail : PeerId → WGPrefix RoutingJoint.Event Int)
    (source : ErasesStatePrefix front (txFront family addr packets mtu))
    (w : WGWorld) (ambient : Ambient) (h : List Event) (valid : ReceiptsValid h) :
    ReceiptsValid (runWGPrefix (transmitWith family addr packets mtu front tail) w ambient h).2 := by
  intro r member
  rw [transmitWith_receipts] at member
  exact observeFront_valid family addr packets mtu front source w ambient h valid r member

end Leanux.Proofs.WG.TransmitJoint
