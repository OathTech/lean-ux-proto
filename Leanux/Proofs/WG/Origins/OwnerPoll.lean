import Leanux.Proofs.WG.Origins.OwnerControls
import Leanux.Proofs.WG.Origins.OwnerCompletion
import Leanux.Proofs.WG.Origins.CurrentPoll
import Leanux.Proofs.WG.Queues.RxPollCarrier

/-! The actual poll retains the receiving-owner carrier under an explicit
contract on its arbitrary product callback. RX-allocating concrete callbacks
must separately supply the allocation invariant at their actual entry. -/
namespace Leanux.Proofs.WG.OwnerPoll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Queues.RxCredits OwnerBounds OwnerCompletion

private theorem counter_geometry (kp : KeypairId) (nonce : Nat) :
    SameView geometry (counterValidate kp nonce) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,
    Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' completion_step initial

theorem counterValidate_preserves (kp : KeypairId) (nonce : Nat) :
    Preserves OwnerBounds.Carrier (counterValidate kp nonce) :=
  preserves_of_frames _ (Origins.Retaining.counterValidate_material kp nonce)
    (counter_geometry kp nonce)
    (keyEffects_view (allowed := NoPromotion)
      ((counter_carrierView kp nonce).factor (fun v => v.2.2)))

private theorem store {α : Type} (a : WG.M α) (frame : SameWGStore a) :
    Preserves OwnerBounds.Carrier a := OwnerControls.store a frame

private theorem peek_preserves (pid : PeerId) : Preserves OwnerBounds.Carrier (peekRxQueue pid) := by
  unfold peekRxQueue
  apply preserves_bind ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.read_preserves) pid)
  intro p
  apply preserves_bind (store _ (prevQueuePeek_sameWGStore p.rxQueue))
  intro peek
  apply preserves_bind ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.read_preserves) pid)
  intro q
  apply preserves_bind ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.write_preserves) pid _)
  intro _
  exact preserves_pure _

private theorem drop_preserves (pid : PeerId) : Preserves OwnerBounds.Carrier (dropRxQueue pid) := by
  unfold dropRxQueue
  apply preserves_bind ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.read_preserves) pid)
  intro p
  apply preserves_bind ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.read_preserves) pid)
  intro q
  exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.write_preserves) pid _

private theorem complete_preserves (pid : PeerId) : Preserves OwnerBounds.Carrier (completeRxQueue pid) := by
  unfold completeRxQueue
  apply preserves_bind ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.read_preserves) pid)
  intro p
  exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCreation.«0».Leanux.Proofs.WG.OwnerCreation.write_preserves) pid _

private theorem readRx_preserves (id : SkbId) : Preserves OwnerBounds.Carrier (getRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a pkt v b hi hr
  exact (Packets.getRxSkb_current id w v pkt a b hr).1 ▸ hi

private theorem native_product {α : Type} (a : WG.M α) (ha : Preserves OwnerBounds.Carrier a) :
    Preserves (fun w : World => OwnerBounds.Carrier w.wg) (liftWG a) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi hr
  rw [liftWG_run] at hr
  cases native : (a.run w.wg).run w.ambient with
  | error e => simp [native,Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨x,u⟩,ambient⟩
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,rfl⟩ := hr
    exact (hoare_iff_run_ambient _ _ _).mp ha w.wg w.ambient x u ambient hi native

macro "owner_poll_native" : tactic => `(tactic| first
  | (rx_retention_head peekRxQueue; exact peek_preserves _)
  | (rx_retention_head dropRxQueue; exact drop_preserves _)
  | (rx_retention_head completeRxQueue; exact complete_preserves _)
  | (rx_retention_head counterValidate; exact counterValidate_preserves _ _)
  | (rx_retention_head consumeDataDone; exact OwnerCompletion.consumeDataDone_preserves _ _ _)
  | (rx_retention_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _))
  | (rx_retention_head getRxSkb; exact readRx_preserves _)
  | (rx_retention_head freeRxSkb; exact OwnerConsume.freeRxSkb_preserves _)
  | (rx_retention_head keypairPut; exact OwnerCreation.keypairPut_preserves _ _)
  | (rx_retention_head peerPut; exact OwnerConsume.peerPut_preserves _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ OwnerBounds.Carrier)
  | rx_retention_step)

/-- Product callbacks remain arbitrary; the contract is their actual normal
carrier preservation, with no ownership or totality requirement. -/
theorem poll (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, Preserves (fun w : World => OwnerBounds.Carrier w.wg) (callback xs)) :
    Preserves (fun w : World => OwnerBounds.Carrier w.wg) (rxPoll pid budget callback) := by
  rw [← rxPollGrouped_eq]
  unfold rxPollGrouped
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,invariant,unsupported,WG.andM]
  repeat' first
    | (rx_retention_head napiGroReceive
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groReceive_preserves)
         _ callback hc _ _)
    | (rx_retention_head napiGroFlushAll
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groFlush_preserves)
         _ callback hc _)
    | (allocation_release_lift_from WG.M
       apply native_product
       simp only [monadLift_self]
       repeat' owner_poll_native)
    | (allocation_release_lift_from AmbientM
       exact productAmbient_spec _ _ (fun _ _ hi => hi))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => OwnerBounds.Carrier w.wg)
       intro x b
       change Preserves (fun w : World => OwnerBounds.Carrier w.wg) _)
    | rx_retention_step

end Leanux.Proofs.WG.OwnerPoll
