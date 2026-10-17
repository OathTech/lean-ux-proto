import Leanux.Proofs.WG.Packets.PublicationCompletion
import Leanux.Proofs.WG.Packets.PublicationFrontierLifecycle
import Leanux.Proofs.WG.Origins.OwnerPoll

/-! Normal packet-publication retention through the actual receive poll.
The callback is an arbitrary product action under its explicit preservation
contract. This does not assert that the concrete Stack callback meets it. -/
namespace Leanux.Proofs.WG.PublicationPoll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues PublicationCompletion

private theorem configured {α : Type} (a : WG.M α)
    (rx : SameView RxDisposition.nativeRxStore a)
    (peers : SameView ConfiguredIdentity.view a) (history : List RxHistory.Event) :
    Preserves (PublicationHistory.Inv history) a :=
  preserves_of_frames a rx (fun initial =>
    (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured) peers initial) history

private theorem store {α : Type} (a : WG.M α) (frame : SameWGStore a)
    (history : List RxHistory.Event) : Preserves (PublicationHistory.Inv history) a := by
  apply configured a _ (ConfiguredIdentity.sameWG (project := id) frame) history
  exact frame.factor (fun s : WGStoreView =>
    (s.dev.map (·.ifindex),fun id : SkbId => s.dev.bind fun d => d.rxSkbs[id]?))

private theorem peek_geometry (pid : PeerId) : SameView OwnerCompletion.geometry (peekRxQueue pid) := by
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold peekRxQueue
  repeat' first
    | (allocation_release_head PrevQueue.peek
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.store)
         (prevQueuePeek_sameWGStore _)).wp (fun s => s = initial))
    | completion_step initial

private theorem drop_geometry (pid : PeerId) : SameView OwnerCompletion.geometry (dropRxQueue pid) := by
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  unfold dropRxQueue
  repeat' completion_step initial

theorem peek_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (PublicationHistory.Inv history) (peekRxQueue pid) :=
  configured _ ((peek_geometry pid).factor Prod.snd)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.peek_view) pid) history

theorem drop_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (PublicationHistory.Inv history) (dropRxQueue pid) :=
  configured _ ((drop_geometry pid).factor Prod.snd)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.drop_view) pid) history

theorem complete_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (PublicationHistory.Inv history) (completeRxQueue pid) :=
  configured _ ((RxCredits.complete_carrierView pid).factor (fun s => s.2.1))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.complete_view) pid) history

theorem counterValidate_preserves (kid : KeypairId) (nonce : Nat) (history : List RxHistory.Event) :
    Preserves (PublicationHistory.Inv history) (counterValidate kid nonce) :=
  configured _ ((RxCredits.counter_carrierView kid nonce).factor (fun s => s.2.1))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.counterValidate_view) kid nonce) history

theorem keypairPut_preserves (kid : Option KeypairId) (now : Bool) (history : List RxHistory.Event) :
    Preserves (PublicationHistory.Inv history) (keypairPut kid now) :=
  configured _ (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.keyPay) kid now).factor Prod.snd)
    (ConfiguredIdentity.keypairPut_view kid now) history

theorem peerPut_preserves (pid : Option PeerId) (history : List RxHistory.Event) :
    Preserves (PublicationHistory.Inv history) (peerPut pid) :=
  preserves_of_frames _ (RxCredits.peerPut_rxView pid) (peerPut_peers pid) history

private theorem readRx_preserves (id : SkbId) (history : List RxHistory.Event) :
    Preserves (PublicationHistory.Inv history) (getRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a pkt v b hi hr
  exact (Packets.getRxSkb_current id w v pkt a b hr).1 ▸ hi

/-- Canonical native execution supplies both actual WG and Ambient endpoints;
the product's other fields remain the adapter's exact fields. -/
theorem native_product {α : Type} (P : WGWorld → Prop) (a : WG.M α) (ha : Preserves P a) :
    Preserves (fun w : World => P w.wg) (liftWG a) := by
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

macro "publication_poll_native " history:term : tactic => `(tactic| first
  | (rx_retention_head peekRxQueue; exact peek_preserves _ $history)
  | (rx_retention_head dropRxQueue; exact drop_preserves _ $history)
  | (rx_retention_head completeRxQueue; exact complete_preserves _ $history)
  | (rx_retention_head counterValidate; exact counterValidate_preserves _ _ $history)
  | (rx_retention_head consumeDataDone; exact PublicationCompletion.consumeDataDone_preserves _ _ _ $history)
  | (rx_retention_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _) $history)
  | (rx_retention_head getRxSkb; exact readRx_preserves _ $history)
  | (rx_retention_head freeRxSkb; exact PublicationHistory.freeRxSkb_preserves _ $history)
  | (rx_retention_head keypairPut; exact keypairPut_preserves _ _ $history)
  | (rx_retention_head peerPut; exact peerPut_preserves _ $history)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (PublicationHistory.Inv $history))
  | rx_retention_step)

/-- Callback scope stays the actual arbitrary product monad. The fixed
outer publication history is retained at each native normal poll boundary. -/
theorem poll (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit) (history : List RxHistory.Event)
    (hc : ∀ xs, Preserves (fun w : World => PublicationHistory.Inv history w.wg) (callback xs)) :
    Preserves (fun w : World => PublicationHistory.Inv history w.wg) (rxPoll pid budget callback) := by
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
       repeat' publication_poll_native history)
    | (allocation_release_lift_from AmbientM
       exact productAmbient_spec _ _ (fun _ _ hi => hi))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => PublicationHistory.Inv history w.wg)
       intro x b
       change Preserves (fun w : World => PublicationHistory.Inv history w.wg) _)
    | rx_retention_step

end Leanux.Proofs.WG.PublicationPoll
