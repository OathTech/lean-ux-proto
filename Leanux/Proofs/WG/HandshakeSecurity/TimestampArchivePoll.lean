import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchivePollFrames
import Leanux.Proofs.WG.TransmitSecurity.NoncePoll

/-! Native RX poll transport of the timestamp archive. The actual GRO callback
remains explicit until the source stack reply contract is supplied. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity Confirmation.Poll
set_option maxHeartbeats 600000

def ProductInv (h : List TimestampReceipt) (w : World) : Prop := StateInv h w.wg
abbrev ProductPreserves (action : PrefixM TimestampReceipt α) :=
  PrefixPreserves ProductInv History action

theorem product_safe {g : WGPrefix TimestampReceipt α} (safe : Preserves g) :
    ProductPreserves (liftWGObserver g) := safe.liftWGObserver

theorem product_pure (x : α) : ProductPreserves (Pure.pure x) :=
  PrefixPreserves.pure (fun _ _ hi => hi.1) x

theorem product_loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → PrefixM TimestampReceipt (ForInStep β))
    (hg : ∀ x b, ProductPreserves (g x b)) : ProductPreserves (forIn xs b g) :=
  PrefixEnsures.forInInvariant xs b g (fun _ h w => ProductInv h w) History
    (fun _ _ _ hi => hi.1) hg

theorem poll (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM TimestampReceipt Unit)
    (callbacks : ∀ packets, ProductPreserves (callback packets)) :
    ProductPreserves (Driver.pollObserved TimestampDriver.hooks pid budget callback) := by
  change PrefixPreserves ProductInv History _
  unfold Driver.pollObserved
  change PrefixPreserves ProductInv History
    (AuthenticatedEffects.CandidatePoll.sourceWith _ (fun _ _ => Pure.pure 0) (fun _ => Pure.pure ()) _ _ _ _ _ _)
  rw [AuthenticatedEffects.CandidatePoll.neutral]
  change PrefixPreserves ProductInv History
    (sourceWith (fun a => liftWGObserver (liftWGPrefix a))
      (fun pkt => liftWGObserver (liftWGPrefix (counterValidate pkt.keypair pkt.nonce)))
      (fun peer pkt ep => liftWGObserver (Driver.consumeObserved TimestampDriver.hooks peer pkt ep))
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
       change StatePrefixPreserves (fun h w _ => StateInv h w) History _
       first
         | (nonce_source_head Driver.consumeObserved; exact consume_data _ _ _)
         | (apply lift; intro history
            try rw [getPeer_twice]
            try unfold WG.andM
            try simp (config := {zeta := false}) only [branch,invariant,unsupported]
            repeat' archive_poll_step history
            done))
    | (first | nonce_product_head Pure.pure | nonce_product_head pure
       exact product_pure _)
    | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
    | (nonce_product_head ForIn.forIn
       apply product_loop
       intro x b
       change PrefixPreserves ProductInv History _)
    | split
    | (session_origin_intro_forall; try dsimp only)

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
