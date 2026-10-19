import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionPollFrames
import Leanux.Proofs.WG.TransmitSecurity.NoncePoll

/-! Source poll transport with its real GRO callback left explicit. This is the
shared driver, so receive-triggered staging and callback-triggered transmission
use the same ordered responder journal. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity Confirmation.Poll
open Responder.DriverCuts (hooks)

def ProductInv (h : List Event) (w : World) : Prop := StateInv h w.wg
abbrev ProductPreserves (action : PrefixM Event α) :=
  PrefixPreserves ProductInv Safe action

theorem product_safe {g : WGPrefix Event α} (safe : Observed g) :
    ProductPreserves (liftWGObserver g) := safe.liftWGObserver

theorem product_pure (x : α) : ProductPreserves (Pure.pure x) :=
  PrefixPreserves.pure (fun _ _ hi => hi.2.2.distinct) x

theorem product_loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → PrefixM Event (ForInStep β))
    (hg : ∀ x b, ProductPreserves (g x b)) : ProductPreserves (forIn xs b g) :=
  PrefixEnsures.forInInvariant xs b g (fun _ h w => ProductInv h w) Safe
    (fun _ _ _ hi => hi.2.2.distinct) hg

theorem poll (edges : H1PendingPromotionEdges) (quiet : H1PendingQuietFrames)
    (frames : H1PendingPollFrames) (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM Event Unit)
    (callbacks : ∀ packets, ProductPreserves (callback packets)) :
    ProductPreserves (Driver.pollObserved hooks pid budget callback) := by
  change PrefixPreserves ProductInv Safe _
  unfold Driver.pollObserved
  change PrefixPreserves ProductInv Safe
    (AuthenticatedEffects.CandidatePoll.sourceWith _ (fun _ _ => Pure.pure 0) (fun _ => Pure.pure ()) _ _ _ _ _ _)
  rw [AuthenticatedEffects.CandidatePoll.neutral]
  change PrefixPreserves ProductInv Safe
    (sourceWith (fun a => liftWGObserver (liftWGPrefix a))
      (fun pkt => liftWGObserver (liftWGPrefix (counterValidate pkt.keypair pkt.nonce)))
      (fun peer pkt ep => liftWGObserver (Driver.consumeObserved hooks peer pkt ep))
      (napiGroReceivePrefix callback) (napiGroFlushAllPrefix callback) pid budget)
  unfold sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (nonce_product_head napiGroReceivePrefix
       exact napiGroReceivePrefix_preserves callback (fun _ _ hi => hi.2.2.distinct) callbacks _ _)
    | (nonce_product_head napiGroFlushAllPrefix
       exact napiGroFlushAllPrefix_preserves callback (fun _ _ hi => hi.2.2.distinct) callbacks _)
    | (nonce_product_head liftWGObserver
       apply product_safe
       change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
       first
         | (nonce_source_head Driver.consumeObserved; exact consume edges quiet _ _ _)
         | (apply native; intro confirmed
            try rw [getPeer_twice]
            try unfold WG.andM
            try simp (config := {zeta := false}) only [branch,invariant,unsupported]
            repeat' pending_carrier_poll_step frames, confirmed
            done))
    | (first | nonce_product_head Pure.pure | nonce_product_head pure
       exact product_pure _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ForIn.forIn
       apply product_loop
       intro x b
       change PrefixPreserves ProductInv Safe _)
    | split
    | (session_origin_intro_forall; try dsimp only)

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
