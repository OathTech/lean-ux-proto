import Leanux.Proofs.WG.TransmitSecurity.StagedProductFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedPacketFrames

/-! Replay checking records its actual native call without creating staged
origins. Product receipts retain every prior staged-selection certificate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

theorem product_receipt {action : PrefixM Event α} (safe : ProductSafe action)
    (record : RunWitness α → Event) (quiet : ∀ r, Quiet (record r)) :
    ProductSafe (receiptObserved action record) :=
  product_bind (product_capture _ safe) (fun r =>
    product_bind (product_emit (record r) (quiet r)) (fun _ => product_pure r.value))

theorem focused_product_receipt (encode : E → F) (decode : F → Option E)
    (action : Leanux.M α) (record : RunWitness α → E) :
    focusPrefix encode decode (receiptObserved (liftPrefix action) record) =
      receiptObserved (liftPrefix action) (encode ∘ record) := by
  funext w h
  change runPrefix (focusPrefix encode decode _) w h = runPrefix _ w h
  have inner := runPrefix_receiptObserved (liftPrefix action) record w (h.filterMap decode)
  rw [runPrefix_lift] at inner
  have outer := runPrefix_receiptObserved (liftPrefix action) (encode ∘ record) w h
  rw [runPrefix_lift] at outer
  apply Eq.trans ?_ outer.symm
  change ((runPrefix (receiptObserved (liftPrefix action) record) w (h.filterMap decode)).1,
    h ++ ((runPrefix (receiptObserved (liftPrefix action) record) w (h.filterMap decode)).2.drop
      (h.filterMap decode).length).map encode) = _
  rw [inner]
  cases run : action.run w with
  | error stop => simp
  | ok out =>
    obtain ⟨value,v⟩ := out
    simp

theorem counter_observed (skb : SkbId) (packet : RxPacket) : ProductSafe (hooks.counterCheck skb packet) := by
  change ProductSafe (focusPrefix Event.old old? (TransportDriver.counter Journal.Event.replay skb packet))
  unfold TransportDriver.counter
  rw [focused_product_receipt]
  exact product_receipt (product_wg _ (state_lift _ (fun _ => Native.counter packet.keypair packet.nonce))) _ (fun _ => True.intro)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
