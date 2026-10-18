import Leanux.Proofs.WG.Index.ReceiverCoreFrames
import Leanux.Proofs.WG.Index.CookieCoreClaims
import Leanux.Proofs.WG.Index.IncomingCallerSource
import Leanux.Proofs.WG.Index.ReceiveFrames
import Leanux.Proofs.WG.Queues.HandshakeCookiePayment

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

namespace Incoming
theorem store_cut {α : Type} (cs : Ledger) (loans : Reservations) (action : WG.M α)
    (same : SameWGStore action) :
    Ensures action (Cut cs loans) (fun _ => Cut cs loans) := by
  apply cut_join cs loans action (liftWGPrefix action) (erasesStatePrefix_lift action)
    (allocation_state_store action same)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReception.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReception.store) same)
    (BaseCoherence.store_view same)
  intro w a result v b pre run
  have fields : SameView ConfigurationIndex.fields action :=
    same.of_factor (fun s : WGStoreView => s.dev.map ConfigurationIndex.deviceFields)
      ConfigurationIndex.fields (fun _ => rfl)
  exact (hoare_iff_run_ambient _ _ _).mp (ConfigurationIndex.frame_core fields)
    w a result v b pre.2.2.2 run

theorem cookie_cut {α : Type} (cs : Ledger) (loans : Reservations) (action : WG.M α)
    (same : SameCookie action) :
    Ensures action (Cut cs loans) (fun _ => Cut cs loans) := by
  apply cut_join cs loans action (liftWGPrefix action) (erasesStatePrefix_lift action)
    (AmbientContracts.drop (cookieLift_spec allocationAmbient allocationCookieStable
      (fun _ => True) action (same.factor WGOwnedView.toWGStoreView)))
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReception.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReception.cookie) same)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceHandshake.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.cookie_structure) same)
  intro w a result v b pre run
  exact (hoare_iff_run_ambient _ _ _).mp (ConfigurationIndex.frame_core (cookie_fields same))
    w a result v b pre.2.2.2 run

theorem cookieConsume_cut (cs : Ledger) (loans : Reservations) (msg : List UInt8) :
    Ensures (cookieMessageConsume msg) (Cut cs loans) (fun _ => Cut cs loans) := by
  apply cut_join cs loans _ (CookieCall.consume msg).observed
    (CookieCall.consume msg).erases (CookieCall.consume msg).allocation
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join) _
      (HandshakeCookiePayment.consume msg) (HandshakeEntry.cookie msg))
    (BaseCoherence.cookieConsume_view msg)
  intro w a result v b pre run
  exact cookieMessageConsume_indexCore msg w a result v b pre.2.2.2 run

theorem sendCookie_cut (cs : Ledger) (loans : Reservations) (msg : List UInt8) (src : SkbSource) :
    Ensures (sendHandshakeCookie msg src) (Cut cs loans) (fun _ => Cut cs loans) := by
  apply cut_join cs loans _ (HandshakeReceiveCall.cookie msg src).observed
    (HandshakeReceiveCall.cookie msg src).erases (HandshakeReceiveCall.cookie msg src).allocation
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join) _
      (HandshakeAfterMac.cookie msg src)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.sendCookie) msg src))
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceHandshake.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.cookieReply_structure) msg src)
  have core : Ensures (sendHandshakeCookie msg src) Reached.Core (fun _ => Reached.Core) := by
    unfold sendHandshakeCookie
    refine ensures_bind _ _
      ((hoare_iff_run_ambient _ _ _).mp
        (ConfigurationIndex.frame_core (cookie_fields (cookieMessageCreate_sameCookie _ _ _)))) ?_
    intro bytes
    exact core_sender _ (reply_sender_fields src bytes)
      ((ensures_iff _ _ _).mpr (sendBufferAsReplyToSkb_tables src bytes))
  intro w a result v b pre run
  exact core w a result v b pre.2.2.2 run

theorem afterMac_preserves_source (P : WGWorld → Prop) (msg : List UInt8)
    (src : SkbSource) (loaded : Bool) (mac : MacState)
    (cookie : Preserves P (sendHandshakeCookie msg src))
    (initiation : Preserves P (HandshakeArms.initiation msg src))
    (response : Preserves P (HandshakeArms.response msg src)) :
    Preserves P (Cookies.afterMac msg src loaded mac) := by
  rw [HandshakeAfterMac.source_factor]
  unfold HandshakeAfterMac.source WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head sendHandshakeCookie; exact cookie)
    | (rx_retention_head HandshakeArms.initiation; exact initiation)
    | (rx_retention_head HandshakeArms.response; exact response)
    | (rx_retention_head HandshakeReceive.finishSelected
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a result v b pre run
       simp [HandshakeReceive.finishSelected,branch,invariant,AmbientM.invariant] at run
       cases run)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ P)
    | rx_retention_step

theorem afterMac_cut (cs : Ledger) (loans : Reservations) (msg : List UInt8)
    (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Ensures (Cookies.afterMac msg src loaded mac) (Cut cs loans) (fun _ => Cut cs loans) :=
  (hoare_iff_run_ambient _ _ _).mp (afterMac_preserves_source (Cut cs loans) msg src loaded mac
    ((hoare_iff_run_ambient _ _ _).mpr (sendCookie_cut cs loans msg src))
    ((hoare_iff_run_ambient _ _ _).mpr (initiation_arm cs loans msg src))
    ((hoare_iff_run_ambient _ _ _).mpr (response_arm cs loans msg src)))

theorem receivePacket_cut (cs : Ledger) (loans : Reservations) (msg : List UInt8) (src : SkbSource) :
    Ensures (receiveHandshakePacket msg src) (Cut cs loans) (fun _ => Cut cs loans) := by
  rw [Cookies.receive_factor]
  refine ensures_bind _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
      (AmbientM.branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE)) (Cut cs loans))) ?_
  intro isCookie
  cases isCookie with
  | true =>
    refine ensures_bind _ _ (cookieConsume_cut cs loans msg) ?_
    intro _ w a result v b pre run
    cases run
    exact pre
  | false =>
    refine ensures_bind _ _ (store_cut cs loans Cookies.loadPhase Cookies.loadPhase_sameStore) ?_
    intro loaded
    refine ensures_bind _ _ (cookie_cut cs loans _ (cookieValidatePacket_sameCookie msg src loaded)) ?_
    intro mac
    exact afterMac_cut cs loans msg src loaded mac

theorem queuePop_cut (cs : Ledger) (loans : Reservations) (ring : PtrRing (List UInt8 × SkbSource)) :
    Ensures (modifyDev (popHandshakeQueue ring)) (Cut cs loans) (fun _ => Cut cs loans) := by
  apply cut_join cs loans _ (liftWGPrefix (modifyDev (popHandshakeQueue ring)))
    (erasesStatePrefix_lift _) (allocationReceiveQueue.pop ring)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeWorker.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeWorker.install) ring)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_update)
      (popHandshakeQueue ring) (fun _ => rfl) (fun _ => rfl))
  intro w a result v b pre run
  exact (hoare_iff_run_ambient _ _ _).mp
    (ConfigurationIndex.frame_core (ConfigurationIndex.modifyDev_fields (popHandshakeQueue ring) (fun _ => rfl)))
    w a result v b pre.2.2.2 run

theorem queueDecrement_cut (cs : Ledger) (loans : Reservations) :
    Ensures (modifyDev decHandshakeQueue) (Cut cs loans) (fun _ => Cut cs loans) := by
  have account : Preserves (HandshakeResponse.Input cs loans) (modifyDev decHandshakeQueue) := by
    apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join)
    · exact (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeWorker.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeWorker.decrement)
    · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceiveSlots.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots.modifyDevice)
      all_goals intro d; rfl
  apply cut_join cs loans _ (liftWGPrefix (modifyDev decHandshakeQueue))
    (erasesStatePrefix_lift _) allocationReceiveQueue.decrement account
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_update)
      decHandshakeQueue (fun _ => rfl) (fun _ => rfl))
  intro w a result v b pre run
  exact (hoare_iff_run_ambient _ _ _).mp
    (ConfigurationIndex.frame_core (ConfigurationIndex.modifyDev_fields decHandshakeQueue (fun _ => rfl)))
    w a result v b pre.2.2.2 run

theorem receiveStep_cut (cs : Ledger) (loans : Reservations) :
    Ensures receiveStep (Cut cs loans) (fun _ => Cut cs loans) := by
  unfold receiveStep
  refine ensures_bind _ _ (store_cut cs loans getDev getDev_sameWGStore) ?_
  intro d
  cases outcome : d.handshakeQueue.consume with
  | mk packet ring =>
    cases packet with
    | none =>
      refine ensures_bind _ _
        ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
          (AmbientM.branch .workerConsumed false) (Cut cs loans))) ?_
      intro _ w a result v b pre run
      cases run
      exact pre
    | some item =>
      obtain ⟨msg,src⟩ := item
      refine ensures_bind _ _
        ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
          (AmbientM.branch .workerConsumed true) (Cut cs loans))) ?_
      intro _
      refine ensures_bind _ _ (queuePop_cut cs loans ring) ?_
      intro _
      refine ensures_bind _ _ (receivePacket_cut cs loans msg src) ?_
      intro _
      refine ensures_bind _ _ (queueDecrement_cut cs loans) ?_
      intro _ w a result v b pre run
      cases run
      exact pre

end Incoming

end Leanux.Proofs.WG.Index
