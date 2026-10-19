import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedFront
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedProduct

/-! Original decrypt publication, replay checking and encryption-ring consume
do not invent timer/work occurrences. Receipts extend the same callback's
history; a failed callback retains its prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TransmitSecurity TimerSlots Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem old_product (body : PrefixM Journal.Event α) (native : WG.M α)
    (erases : ErasesPrefix body (liftWG native)) (safe : StateSafe (liftWGPrefix native)) :
    ProductSafe (product body) :=
  product_observed _ native (focusPrefix_erases Event.old old? erases)
    (Appends.focus _ _ _) safe

theorem poll_native : StateSafe (liftWGPrefix TxRing.pollSource) := by
  unfold TxRing.pollSource
  causal_delayed_native

theorem poll : ProductSafe hooks.poll := by
  apply old_product Journal.poll TxRing.pollSource
  · intro w h
    have projected := congrArg Prod.fst (Journal.poll_projects w h)
    have maps : (fun x : Option (List SkbId) × World => (id x.1,x.2)) = id := by
      funext ⟨value,v⟩
      rfl
    rw [maps,Except.map_id] at projected
    exact projected.symm
  · exact poll_native

theorem counter_native (kid : KeypairId) (nonce : Nat) :
    StateSafe (liftWGPrefix (counterValidate kid nonce)) := by
  apply state_framed
  · intro initial
    unfold counterValidate
    simp (config := {zeta := false}) only [WG.orM,branch,branchCmp,invariant,Std.Legacy.Range.forIn_eq_forIn_range']
    repeat' timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => WorkQueueFrames.view w = initial) _
    unfold counterValidate
    simp (config := {zeta := false}) only [WG.orM,branch,branchCmp,invariant,Std.Legacy.Range.forIn_eq_forIn_range']
    repeat' send_work_frame_step initial

theorem counter (skb : SkbId) (packet : RxPacket) : ProductSafe (hooks.counterCheck skb packet) :=
  old_product _ _ (TransportDriver.counter_erases _ skb packet) (counter_native packet.keypair packet.nonce)

private theorem decrypt (packet : RxPacket) : StateSafe (liftWGPrefix (decryptPacket packet)) := by
  unfold decryptPacket
  causal_delayed_native

private theorem publish (skb : SkbId) (state : PacketState) :
    StateSafe (liftWGPrefix (RxWorkers.publishSource skb state)) := by
  apply state_framed
  · intro initial
    unfold RxWorkers.publishSource getRxSkb setRxSkb
    simp only [invariant]
    repeat' timer_data_step initial
  · apply DelayedEffects.queue_of_frame
    intro initial
    change Preserves (fun w => WorkQueueFrames.view w = initial) _
    unfold RxWorkers.publishSource getRxSkb setRxSkb
    simp only [invariant]
    repeat' send_work_frame_step initial

theorem prepare_native : StateSafe (liftWGPrefix RxWorkers.prepareSource) := by
  apply state_native
  intro h
  unfold RxWorkers.prepareSource
  repeat' first
    | (rx_retention_head decryptPacket; exact native_contract _ (decrypt _) h)
    | (rx_retention_head RxWorkers.publishSource; exact native_contract _ (publish _ _) h)
    | (rx_retention_head getRxSkb; exact native_contract _ (by
        unfold getRxSkb
        exact state_framed _ (skb_retained _) (SendWorkCauses.skb_frame _)) h)
    | (rx_retention_head setRxSkb; exact native_contract _ (by
        unfold setRxSkb
        exact state_framed _ (skb_retained _) (SendWorkCauses.skb_frame _)) h)
    | (rx_retention_head getDev; exact native_contract _ (native_store _ getDev_sameWGStore) h)
    | (rx_retention_head modifyDev; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head branch; exact native_contract _ (by causal_delayed_native) h)
    | (rx_retention_head invariant; exact native_contract _ (by causal_delayed_native) h)
    | rx_retention_step

theorem decrypt_prepare : ProductSafe hooks.prepare :=
  old_product _ _ (TransportDriver.prepare_erases _ _) prepare_native

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
