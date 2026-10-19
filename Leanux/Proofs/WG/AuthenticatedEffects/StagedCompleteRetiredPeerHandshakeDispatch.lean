import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeArms

/-! Exact reference accounts follow the unchanged cookie/type dispatcher.
Malformed guards, normal refusals and native Stop arms remain in the source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
set_option maxHeartbeats 600000

theorem cookie_frame {action : WG.M α} (same : SameCookie action) :
    Preserves (Account holders cs loans) action := by
  apply Account.native_fields
  apply same.of_factor (fun k : WGOwnedView => HolderEncrypt.fields {dev:=k.dev,nlSock7:=k.nlSock7,nlSock8:=k.nlSock8})
  intro w
  unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  unfold cookieView cookieDevice wgOwnedView wgStoreView
  cases hd : w.dev <;> simp [hd,rxView]

private theorem socket4 e bytes : Preserves (Account holders cs loans) (send4 e none bytes 0 false) :=
  control _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send4_frame) e none bytes 0 false)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.send4_view) e none bytes 0 false)

private theorem socket6 e bytes : Preserves (Account holders cs loans) (send6 e none bytes 0 false) :=
  control _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send6_frame) e none bytes 0 false)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.send6_view) e none bytes 0 false)

private theorem reply (src : SkbSource) (bytes : List UInt8) :
    Preserves (Account holders cs loans) (sendBufferAsReplyToSkb src bytes) := by
  unfold sendBufferAsReplyToSkb
  simp (config := {zeta := false}) only [branch,hiddenAlloc,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact store (endpointFromSkb_sameWGStore _))
    | (rx_retention_head send4; exact socket4 _ _)
    | (rx_retention_head send6; exact socket6 _ _)
    | (rx_retention_head getDev; exact store getDev_sameWGStore)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem send_cookie (msg : List UInt8) (src : SkbSource) :
    Preserves (ExactBoundary cs loans) (sendHandshakeCookie msg src) := by
  apply boundary
  intro holders
  unfold sendHandshakeCookie
  apply preserves_bind (cookie_frame (cookieMessageCreate_sameCookie _ _ _))
  intro bytes
  exact reply src bytes

theorem after_mac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Hoare (Cookies.afterMac msg src loaded mac) (Input cs loans) (fun _ => ExactBoundary cs loans) := by
  have cookieCase : Hoare (do sendHandshakeCookie msg src; pure () : WG.M Unit)
      (Input cs loans) (fun _ => ExactBoundary cs loans) := by
    apply hoare_consequence (preserves_bind (send_cookie msg src) (fun _ => preserves_pure ()))
    · exact fun _ hi => hi.1
    · exact fun _ _ hi => hi
  have choose (needsCookie : Bool) : Hoare (do
      if ← branch .hsSwitchInitiation (messageType msg == MESSAGE_HANDSHAKE_INITIATION) then
        if ← branch .hsInitNeedsCookie needsCookie then
          sendHandshakeCookie msg src
          return
        HandshakeArms.initiation msg src
      else if ← branch .hsSwitchResponse (messageType msg == MESSAGE_HANDSHAKE_RESPONSE) then
        if ← branch .hsRespNeedsCookie needsCookie then
          sendHandshakeCookie msg src
          return
        HandshakeArms.response msg src
      else HandshakeReceive.finishSelected none msg : WG.M Unit)
      (Input cs loans) (fun _ => ExactBoundary cs loans) := by
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .hsSwitchInitiation _) (Input cs loans))
    intro init
    cases init with
    | true =>
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .hsInitNeedsCookie needsCookie) (Input cs loans))
      intro needed
      cases needed with
      | true => exact cookieCase
      | false => exact initiation_arm msg src
    | false =>
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .hsSwitchResponse _) (Input cs loans))
      intro resp
      cases resp with
      | true =>
        apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .hsRespNeedsCookie needsCookie) (Input cs loans))
        intro needed
        cases needed with
        | true => exact cookieCase
        | false => exact response_arm msg src
      | false => exact hoare_consequence (selected_finish none msg) (fun _ hi => hi.1) (fun _ _ hi => hi)
  have proceed : Preserves (Input cs loans)
      (WG.orM (WG.andM (branch .hsLoadedOperand loaded) (branch .hsLoadedCookieOk (mac == .withCookie)))
        (WG.andM (branch .hsNotLoaded (!loaded)) (branch .hsMacNoCookie (mac == .noCookie)))) := by
    unfold WG.orM WG.andM
    simp only [branch]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step
  have needs : Preserves (Input cs loans)
      (WG.andM (branch .hsNeedsCookieLoaded loaded) (branch .hsNeedsCookieMac (mac == .noCookie))) := by
    unfold WG.andM
    simp only [branch]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step
  rw [HandshakeAfterMac.source_factor]
  unfold HandshakeAfterMac.source
  apply hoare_bind _ _ proceed
  intro ok
  cases ok with
  | true => exact choose false
  | false =>
    apply hoare_bind _ _ needs
    intro needed
    cases needed with
    | true => exact choose true
    | false => exact hoare_consequence (preserves_pure ()) (fun _ hi => hi.1) (fun _ _ hi => hi)
theorem input_cookie {action : WG.M α} (same : SameCookie action) : Preserves (Input cs loans) action := by
  apply join
  · exact boundary (fun _ => cookie_frame same)
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine)
    · exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.cookie) action same
    · apply CurrentSlots.fields_preserves (project := id)
      apply same.of_factor (fun k : WGOwnedView => CurrentSlots.fields {dev:=k.dev})
      intro w
      unfold CurrentSlots.fields Queues.RxCredits.keyWords cookieView cookieDevice wgOwnedView wgStoreView
      cases hd : w.dev <;> simp [hd]


theorem receive (msg : List UInt8) (src : SkbSource) :
    Hoare (receiveHandshakePacket msg src) (Input cs loans) (fun _ => ExactBoundary cs loans) := by
  rw [Cookies.receive_factor]
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .hsCookie _) (Input cs loans))
  intro isCookie
  cases isCookie with
  | true =>
    apply hoare_bind _ _ (hoare_consequence (cookie_boundary msg)
      (fun _ hi => hi.1) (fun _ _ hi => hi))
    intro _
    exact preserves_pure ()
  | false =>
    apply hoare_bind _ _ (input_store Cookies.loadPhase_sameStore)
    intro loaded
    apply hoare_bind _ _ (input_cookie (cookieValidatePacket_sameCookie msg src loaded))
    intro mac
    exact after_mac msg src loaded mac

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
