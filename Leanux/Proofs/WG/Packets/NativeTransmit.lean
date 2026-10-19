import Leanux.Proofs.WG.Packets.TxObservedFront
import Leanux.Proofs.WG.Packets.TransmitObserver

/-! The concrete transmit observer executes the original lifetime front once,
records its successful completed splice, and runs the original send/payment
suffix. Erasing new transmit receipts retains the complete old joint journal. -/
namespace Leanux.Proofs.WG.TransmitJoint
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Packets

private theorem access_bind {α β : Type} (g : MixedM α) (f : α → MixedM β)
    (hg : StateAppends g) (hf : ∀ x, StateAppends (f x)) :
    (RoutingJoint.access g >>= fun x => RoutingJoint.access (f x)) =
      RoutingJoint.access (g >>= f) := by
  have compose {E F δ ε : Type} (encode : E → F) (decode : F → Option E)
      (inverse : ∀ e, decode (encode e) = some e)
      (a : WGPrefix E δ) (b : δ → WGPrefix E ε)
      (ha : StateAppends a) (hb : ∀ x, StateAppends (b x)) :
      (focusStatePrefix encode decode a >>= fun x => focusStatePrefix encode decode (b x)) =
        focusStatePrefix encode decode (a >>= b) :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind)
      encode decode inverse ⟨ha,rfl⟩ (fun x => ⟨hb x,rfl⟩) |>.2
  unfold RoutingJoint.access RoutingJoint.nativeRx
  rw [compose RoutingJoint.Event.rx RoutingJoint.rxEvent (fun _ => rfl)
    _ _ (StateAppends.focus _ _ _) (fun _ => StateAppends.focus _ _ _)]
  congr 1
  rw [compose RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    _ _ (StateAppends.focus _ _ _) (fun _ => StateAppends.focus _ _ _)]
  congr 1
  exact compose AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl) g f hg hf

private theorem access_pure {α : Type} (x : α) :
    RoutingJoint.access (pure x) = (pure x : WGPrefix RoutingJoint.Event α) := by
  unfold RoutingJoint.access RoutingJoint.nativeRx
  rw [← (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_pure)
    AuditEvent.lifetime AuditEvent.lifetime? x |>.2]
  rw [← (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_pure)
    RxHistory.Event.audit RxHistory.auditEvent x |>.2]
  rw [← (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_pure)
    RoutingJoint.Event.rx RoutingJoint.rxEvent x |>.2]

private theorem access_front_factor (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    (do match ← RoutingJoint.access (txFrontPrefix family addr packets mtu) with
        | .error err => pure err
        | .ok pid => RoutingJoint.access (txTailPrefix pid)) =
      RoutingJoint.access (wgXmitPrefix family addr packets mtu) := by
  rw [wgXmitPrefix_front_factor]
  have tail (result : Except Int PeerId) :
      (match result with
        | .error err => pure err
        | .ok pid => RoutingJoint.access (txTailPrefix pid)) =
      RoutingJoint.access (match result with
        | .error err => pure err
        | .ok pid => txTailPrefix pid) := by
    cases result with
    | error err => exact (access_pure err).symm
    | ok pid => rfl
  rw [show (fun result : Except Int PeerId => match result with
      | .error err => pure err
      | .ok pid => RoutingJoint.access (txTailPrefix pid)) =
      (fun result => RoutingJoint.access (match result with
        | .error err => pure err
        | .ok pid => txTailPrefix pid)) from funext tail]
  apply access_bind _ _ (txFrontPrefix_appends family addr packets mtu)
  intro result
  cases result with
  | error err => exact StateAppends.pure err
  | ok pid => exact txTailPrefix_appends pid

/-- The captured native front and its original focused lifetime tail. -/
def transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) : WGPrefix Event Int :=
  transmitWith family addr packets mtu
    (RoutingJoint.access (txFrontPrefix family addr packets mtu))
    (fun pid => RoutingJoint.access (txTailPrefix pid))

/-- Removing only the new handoff receipts gives the existing observer,
including all prior probe/lifetime nesting and every failed prefix. -/
theorem transmit_projects (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateProjectsPrefix oldEvent id (transmit family addr packets mtu)
      (RoutingJoint.access (wgXmitPrefix family addr packets mtu)) := by
  rw [← access_front_factor]
  exact transmitWith_projects family addr packets mtu _ _
    (RoutingJoint.access_appends _) (fun _ => RoutingJoint.access_appends _)

/-- The concrete observer has the actual WG/Ambient execution result. -/
theorem transmit_erases (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ErasesStatePrefix (transmit family addr packets mtu) (wgXmit family addr packets mtu) := by
  intro w ambient h
  have projection := congrArg Prod.fst (transmit_projects family addr packets mtu w ambient h)
  have erasure := RoutingJoint.access_erases (wgXmitPrefix_erases family addr packets mtu)
    w ambient (h.filterMap oldEvent)
  change (runWGPrefix (RoutingJoint.access (wgXmitPrefix family addr packets mtu))
    w ambient (h.filterMap oldEvent)).1 =
    (runWGPrefix (transmit family addr packets mtu) w ambient h).1.map
      (fun ((x,v),a) => ((x,v),a)) at projection
  have identity : (runWGPrefix (transmit family addr packets mtu) w ambient h).1.map
      (fun ((x,v),a) => ((x,v),a)) =
      (runWGPrefix (transmit family addr packets mtu) w ambient h).1 := by
    cases (runWGPrefix (transmit family addr packets mtu) w ambient h).1 <;> rfl
  exact identity.symm.trans (projection.symm.trans erasure)

/-- New and old records append on both normal and stopped executions. -/
theorem transmit_appends (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateAppends (transmit family addr packets mtu) :=
  transmitWith_appends family addr packets mtu _ _

/-- Arbitrary valid incoming receipts stay valid. A fresh receipt is backed by
this actual completed native front, regardless of the tail's outcome. -/
theorem transmit_valid (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (w : WGWorld) (ambient : Ambient) (h : List Event) (valid : ReceiptsValid h) :
    ReceiptsValid (runWGPrefix (transmit family addr packets mtu) w ambient h).2 :=
  transmitWith_valid family addr packets mtu _ _
    (RoutingJoint.access_erases (txFrontPrefix_erases family addr packets mtu)) w ambient h valid

end Leanux.Proofs.WG.TransmitJoint
