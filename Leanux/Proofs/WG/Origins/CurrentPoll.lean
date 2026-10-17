import Leanux.Proofs.WG.Origins.CurrentRx
import Leanux.Proofs.WG.Origins.CurrentSensitive

/-! Current identity through the actual poll, with unrestricted product
callbacks and their explicit normal-state preservation contracts. -/
namespace Leanux.Proofs.WG.CurrentPoll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues ConfiguredHandshake CurrentLifecycle CurrentTraffic
open Origins.HistorySupport (sessions sessionEvent sensitive)

private theorem erased_preserves (P : World → Prop) (g : PrefixM Unit α) (a : Leanux.M α)
    (erase : ErasesPrefix g a)
    (keep : PrefixPreserves (fun _ => P) (fun _ => True) g) : Preserves P a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  have post := (keep w [] hi).choose_spec.2.2
  rw [erase,hr] at post
  exact post

private theorem lift_preserves (P : World → Prop) (a : Leanux.M α)
    (keep : Preserves P a) :
    PrefixPreserves (Event := Unit) (fun _ => P) (fun _ => True) (liftPrefix a) :=
  (PrefixEnsures.lift a (fun _ _ _ => True.intro)
    (fun _ w x v hi hr => (hoare_iff_run _ _ _).mp keep w x v hi hr)).preserves

private theorem groReceive_preserves (P : World → Prop)
    (cb : List (List UInt8) → Leanux.M Unit) (hc : ∀ xs, Preserves P (cb xs))
    (gro : GroState) (bytes : List UInt8) : Preserves P (napiGroReceive cb gro bytes) :=
  erased_preserves P _ _
    (napiGroReceivePrefix_erases (fun xs => liftPrefix (cb xs)) cb
      (fun _ => erasesPrefix_lift _) gro bytes)
    (napiGroReceivePrefix_preserves _ (fun _ _ _ => True.intro)
      (fun xs => lift_preserves P _ (hc xs)) gro bytes)

private theorem groFlush_preserves (P : World → Prop)
    (cb : List (List UInt8) → Leanux.M Unit) (hc : ∀ xs, Preserves P (cb xs))
    (gro : GroState) : Preserves P (napiGroFlushAll cb gro) :=
  erased_preserves P _ _
    (napiGroFlushAllPrefix_erases (fun xs => liftPrefix (cb xs)) cb
      (fun _ => erasesPrefix_lift _) gro)
    (napiGroFlushAllPrefix_preserves _ (fun _ _ _ => True.intro)
      (fun xs => lift_preserves P _ (hc xs)) gro)

private theorem peek_view (pid : PeerId) : SameView ConfiguredIdentity.view (peekRxQueue pid) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold peekRxQueue
  repeat' first
    | (rx_retention_head PrevQueue.peek
       exact (ConfiguredIdentity.sameWG (project := id) (prevQueuePeek_sameWGStore _)).wp (fun s => s = initial))
    | configured_step initial

private theorem drop_view (pid : PeerId) : SameView ConfiguredIdentity.view (dropRxQueue pid) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold dropRxQueue
  repeat' configured_step initial

private theorem complete_view (pid : PeerId) : SameView ConfiguredIdentity.view (completeRxQueue pid) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold completeRxQueue
  repeat' configured_step initial


private theorem peek_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (peekRxQueue pid) :=
  current_preserves _ (peek_view pid)
    (Origins.Retaining.of_view ((pinned_const _private.Leanux.Proofs.WG.Origins.RetainingTraffic.«0».Leanux.Proofs.WG.Origins.Retaining.peekRxQueue_material) pid)) history

private theorem drop_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (dropRxQueue pid) :=
  current_preserves _ (drop_view pid)
    (Origins.Retaining.of_view ((pinned_const _private.Leanux.Proofs.WG.Origins.RetainingTraffic.«0».Leanux.Proofs.WG.Origins.Retaining.dropRxQueue_material) pid)) history

private theorem complete_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (completeRxQueue pid) :=
  current_preserves _ (complete_view pid)
    (Origins.Retaining.of_view ((pinned_const _private.Leanux.Proofs.WG.Origins.RetainingTraffic.«0».Leanux.Proofs.WG.Origins.Retaining.completeRxQueue_material) pid)) history

macro "current_poll_native " history:term : tactic => `(tactic| first
  | (rx_retention_head peekRxQueue; exact peek_preserves _ $history)
  | (rx_retention_head dropRxQueue; exact drop_preserves _ $history)
  | (rx_retention_head completeRxQueue; exact complete_preserves _ $history)
  | (rx_retention_head counterValidate; exact CurrentRx.counterValidate_preserves _ _ $history)
  | (rx_retention_head consumeDataDone; exact CurrentRx.consumeDataDone_preserves _ _ _ $history)
  | (rx_retention_head endpointFromSkb
     exact current_preserves _
       (ConfiguredIdentity.sameWG (project := id) (endpointFromSkb_sameWGStore _))
       (Origins.Retaining.of_view (Origins.sameView_of_sameWG (project := id) (endpointFromSkb_sameWGStore _))) $history)
  | (rx_retention_head getRxSkb; unfold getRxSkb)
  | (rx_retention_head freeRxSkb; unfold freeRxSkb)
  | current_skb_step $history
  | current_traffic_step $history)

/-- The callback remains an arbitrary action on the product World. -/
theorem poll (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs history, Preserves (fun w : World => Inv history w.wg) (callback xs))
    (history : List SessionOrigin.Receipt) :
    Preserves (fun w : World => Inv history w.wg) (rxPoll pid budget callback) := by
  rw [← rxPollGrouped_eq]
  unfold rxPollGrouped
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,invariant,unsupported,WG.andM]
  repeat' first
    | (rx_retention_head napiGroReceive; exact groReceive_preserves _ callback (fun xs => hc xs history) _ _)
    | (rx_retention_head napiGroFlushAll; exact groFlush_preserves _ callback (fun xs => hc xs history) _)
    | (allocation_release_lift_from WG.M
       apply CurrentHistory.native_product
       intro nativeHistory
       simp only [monadLift_self]
       repeat' current_poll_native nativeHistory)
    | (allocation_release_lift_from AmbientM
       exact productAmbient_spec _ _ (fun _ _ hi => hi))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => Inv history w.wg)
       intro x b
       change Preserves (fun w : World => Inv history w.wg) _)
    | rx_retention_step

end Leanux.Proofs.WG.CurrentPoll
