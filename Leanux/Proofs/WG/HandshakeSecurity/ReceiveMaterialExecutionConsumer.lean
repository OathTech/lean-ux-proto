import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialExecutionPoll
import Leanux.Proofs.WG.TransmitSecurity.DriverGroNeutral

/-! The shared consumer certifies its actual confirmation event using this
poll's accepted packet. Its tail and stack callbacks have explicit carrier
contracts; no unconditional confirmation premise enters the caller. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues RxJoint AuthenticatedEffects TransmitSecurity

theorem base_of_product {g : PrefixM Journal.Event α} (safe : ProductSafe g) :
    PrefixPreserves Base Safe g :=
  PrefixEnsures.consequence (P := fun h (w : World) => Carrier h w.wg) (Q := fun _ h (w : World) => Carrier h w.wg)
    safe (fun _ _ hi => hi.carrier) (fun _ _ _ hi => hi.base)

theorem product_of_base {g : PrefixM Journal.Event α} (safe : PrefixPreserves Base Safe g) :
    ProductSafe g := PrefixEnsures.consequence safe (fun _ _ hi => hi.base) (fun _ _ _ hi => hi.carrier)

theorem shared_consumer
    (tail : ∀ pid pkt value, ProductSafe
      (liftWGObserver (Driver.receiveTailObserved Journal.hooks pid pkt value)))
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) (peer : pkt.peer = pid) :
    PrefixEnsures (AtCounter pkt true) Safe
      (liftWGObserver (Driver.consumeObserved Journal.hooks pid pkt ep)) (fun _ => Base) := by
  unfold Driver.consumeObserved
  simp only [liftWGObserver_bind,liftWGObserver_lift]
  apply PrefixEnsures.bind (atCounter_native (setPeerEndpoint pid ep)
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.endpoint_geometry) pid ep).factor Prod.snd)
    (fun _ => ReceiveMaterial.endpoint pid ep) (key_bounds_endpoint pid ep))
  intro _
  apply PrefixEnsures.bind ((confirmation_product pid pkt.keypair).consequence
    (fun _ _ hi => ⟨⟨pkt,peer,rfl,hi.1⟩,hi.2⟩) (fun _ _ _ hi => hi))
  intro value
  exact PrefixEnsures.consequence (P := fun h (w : World) => Carrier h w.wg) (Q := fun _ h (w : World) => Carrier h w.wg)
    (tail pid pkt value) (fun _ _ hi => hi) (fun _ _ _ hi => hi.base)

theorem shared_poll
    (tail : ∀ pid pkt value, ProductSafe
      (liftWGObserver (Driver.receiveTailObserved Journal.hooks pid pkt value)))
    (toStack : List (List UInt8) → PrefixM Journal.Event Unit)
    (receive : ∀ gro bytes, ProductSafe (napiGroReceivePrefix toStack gro bytes))
    (flush : ∀ gro, ProductSafe (napiGroFlushAllPrefix toStack gro))
    (pid : PeerId) (budget : Nat) :
    ProductSafe (Driver.pollObserved Journal.hooks pid budget toStack) := by
  apply product_of_base
  unfold Driver.pollObserved
  simp only [Journal.hooks,liftWGObserver_lift,CandidatePoll.neutral]
  exact poll_authorized _ _ _ (shared_consumer tail)
    (fun gro bytes => base_of_product (receive gro bytes))
    (fun gro => base_of_product (flush gro)) pid budget

theorem native_poll
    (tail : ∀ pid pkt value, ProductSafe
      (liftWGObserver (Driver.receiveTailObserved Journal.hooks pid pkt value)))
    (receive : ∀ gro bytes, ProductSafe
      (napiGroReceivePrefix (Driver.stackFlushObserved Journal.hooks) gro bytes))
    (flush : ∀ gro, ProductSafe
      (napiGroFlushAllPrefix (Driver.stackFlushObserved Journal.hooks) gro))
    (pid : PeerId) (budget : Nat) :
    ProductSafe (Driver.nativePollObserved Journal.hooks pid budget) := by
  rw [Driver.nativePoll_neutral _ rfl rfl]
  exact shared_poll tail _ receive flush pid budget

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
