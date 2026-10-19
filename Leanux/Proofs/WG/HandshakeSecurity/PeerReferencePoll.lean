import Leanux.Proofs.WG.HandshakeSecurity.PeerReferencePollFrames
import Leanux.Proofs.WG.TransmitSecurity.NoncePoll

/-! Actual poll and native GRO callbacks transport positive-reference entries. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity Confirmation.Poll

def ProductInv (h : List E) (w : World) : Prop := StateInv (E := E) h w.wg
abbrev ProductPreserves (action : PrefixM E α) :=
  PrefixPreserves (ProductInv (E := E)) (Safe (E := E)) action

theorem product_safe {g : WGPrefix E α} (safe : Observed (E := E) g) :
    ProductPreserves (E := E) (liftWGObserver g) := safe.liftWGObserver

theorem product_pure (x : α) : ProductPreserves (E := E) (Pure.pure x) :=
  PrefixPreserves.pure (fun _ _ hi => hi.1) x

theorem product_loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → PrefixM E (ForInStep β))
    (hg : ∀ x b, ProductPreserves (E := E) (g x b)) : ProductPreserves (E := E) (forIn xs b g) :=
  PrefixEnsures.forInInvariant xs b g (fun _ h w => (ProductInv (E := E)) h w) (Safe (E := E))
    (fun _ _ _ hi => hi.1) hg

theorem poll (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM E Unit)
    (callbacks : ∀ packets, ProductPreserves (E := E) (callback packets)) :
    ProductPreserves (E := E) (Driver.pollObserved EntrySource.hooks (E := E) pid budget callback) := by
  change PrefixPreserves (ProductInv (E := E)) (Safe (E := E)) _
  unfold Driver.pollObserved
  change PrefixPreserves (ProductInv (E := E)) (Safe (E := E))
    (AuthenticatedEffects.CandidatePoll.sourceWith _ (fun _ _ => Pure.pure 0) (fun _ => Pure.pure ()) _ _ _ _ _ _)
  rw [AuthenticatedEffects.CandidatePoll.neutral]
  change PrefixPreserves (ProductInv (E := E)) (Safe (E := E))
    (sourceWith (fun a => liftWGObserver (liftWGPrefix a))
      (fun pkt => liftWGObserver (liftWGPrefix (counterValidate pkt.keypair pkt.nonce)))
      (fun peer pkt ep => liftWGObserver (Driver.consumeObserved EntrySource.hooks (E := E) peer pkt ep))
      (napiGroReceivePrefix callback) (napiGroFlushAllPrefix callback) pid budget)
  unfold sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (nonce_product_head napiGroReceivePrefix
       exact napiGroReceivePrefix_preserves callback (fun _ _ hi => hi.1) callbacks _ _)
    | (nonce_product_head napiGroFlushAllPrefix
       exact napiGroFlushAllPrefix_preserves callback (fun _ _ hi => hi.1) callbacks _)
    | (nonce_product_head liftWGObserver
       apply product_safe
       change StatePrefixPreserves (fun h w _ => StateInv (E := E) h w) (Safe (E := E)) _
       first
         | (nonce_source_head Driver.consumeObserved; exact consume_data _ _ _)
         | (apply lift
            try rw [getPeer_twice]
            try unfold WG.andM
            try simp (config := {zeta := false}) only [branch,invariant,unsupported]
            repeat' peer_reference_poll_step
            done))
    | (first | nonce_product_head Pure.pure | nonce_product_head pure
       exact product_pure _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ForIn.forIn
       apply product_loop
       intro x b
       change PrefixPreserves (ProductInv (E := E)) (Safe (E := E)) _)
    | split
    | (session_origin_intro_forall; try dsimp only)

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
