import Leanux.Proofs.WG.Queues.HandshakeArms

/-! The actual after-MAC dispatcher retains normal cookie/drop returns and
charges only the source-acquired peer passed to a Noise arm. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeAfterMac
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders HandshakeResponse

theorem cookie_boundary {action : WG.M α} (same : SameCookie action) :
    Preserves (Boundary cs loans) action := by
  apply HolderEncrypt.native_boundary
  apply same.of_factor (fun k : WGOwnedView => HolderEncrypt.fields {dev:=k.dev,nlSock7:=k.nlSock7,nlSock8:=k.nlSock8})
  intro w
  unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  unfold cookieView cookieDevice wgOwnedView wgStoreView
  cases hd : w.dev <;> simp [hd,rxView]

private theorem send4_boundary e bytes : Preserves (Boundary cs loans) (send4 e none bytes 0 false) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.frame_boundary)
    _ ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send4_frame) e none bytes 0 false)
    (fun _ _ => (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.control_keeps)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.send4_view) e none bytes 0 false))

private theorem send6_boundary e bytes : Preserves (Boundary cs loans) (send6 e none bytes 0 false) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.frame_boundary)
    _ ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send6_frame) e none bytes 0 false)
    (fun _ _ => (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.control_keeps)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.send6_view) e none bytes 0 false))

private theorem reply (src : SkbSource) (bytes : List UInt8) :
    Preserves (Boundary cs loans) (sendBufferAsReplyToSkb src bytes) := by
  unfold sendBufferAsReplyToSkb
  simp (config := {zeta := false}) only [branch,hiddenAlloc,invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb
       exact HolderEncrypt.native_boundary (HolderEncrypt.store_fields (endpointFromSkb_sameWGStore _)))
    | (rx_retention_head send4; exact send4_boundary _ _)
    | (rx_retention_head send6; exact send6_boundary _ _)
    | handshake_boundary_step

theorem cookie (msg : List UInt8) (src : SkbSource) :
    Preserves (Boundary cs loans) (sendHandshakeCookie msg src) := by
  unfold sendHandshakeCookie
  apply preserves_bind (cookie_boundary (cookieMessageCreate_sameCookie _ _ _))
  intro bytes
  exact reply src bytes

def source (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) : WG.M Unit := do
  let proceed ← WG.orM (WG.andM (branch .hsLoadedOperand underLoad) (branch .hsLoadedCookieOk (macState == .withCookie)))
                    (WG.andM (branch .hsNotLoaded (!underLoad)) (branch .hsMacNoCookie (macState == .noCookie)))
  let needsCookie ← do
    if proceed then pure false
    else if ← WG.andM (branch .hsNeedsCookieLoaded underLoad) (branch .hsNeedsCookieMac (macState == .noCookie)) then pure true
    else return
  let t := messageType msg
  if ← branch .hsSwitchInitiation (t == MESSAGE_HANDSHAKE_INITIATION) then
    if ← branch .hsInitNeedsCookie needsCookie then
      sendHandshakeCookie msg src
      return
    HandshakeArms.initiation msg src
  else if ← branch .hsSwitchResponse (t == MESSAGE_HANDSHAKE_RESPONSE) then
    if ← branch .hsRespNeedsCookie needsCookie then
      sendHandshakeCookie msg src
      return
    HandshakeArms.response msg src
  else HandshakeReceive.finishSelected none msg

theorem source_factor (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Cookies.afterMac msg src loaded mac = source msg src loaded mac := by
  have stopped {α β : Type} (why : String) (next : α → WG.M β) :
      ((invariant why : WG.M α) >>= next) = (invariant why : WG.M β) := rfl
  rw [HandshakeReceive.afterMac_factor]
  simp only [source,HandshakeArms.initiation,HandshakeArms.response,
    HandshakeReceive.responseSession,bind_assoc,bind_if_source,pure_bind,stopped]
  rfl

theorem afterMac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Hoare (Cookies.afterMac msg src loaded mac) (Input cs loans) (fun _ => Boundary cs loans) := by
  have cookieCase : Hoare (do sendHandshakeCookie msg src; pure () : WG.M Unit)
      (Input cs loans) (fun _ => Boundary cs loans) := by
    apply hoare_consequence (preserves_bind (cookie msg src) (fun _ => preserves_pure ()))
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
      (Input cs loans) (fun _ => Boundary cs loans) := by
    apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .hsSwitchInitiation _) (Input cs loans))
    intro init
    cases init with
    | true =>
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .hsInitNeedsCookie needsCookie) (Input cs loans))
      intro needed
      cases needed with
      | true => exact cookieCase
      | false => exact HandshakeArms.initiation_spec msg src
    | false =>
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .hsSwitchResponse _) (Input cs loans))
      intro resp
      cases resp with
      | true =>
        apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .hsRespNeedsCookie needsCookie) (Input cs loans))
        intro needed
        cases needed with
        | true => exact cookieCase
        | false => exact HandshakeArms.response_spec msg src
      | false => exact hoare_consequence (HandshakeResponse.finish none msg) (fun _ hi => hi.1) (fun _ _ hi => hi)
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
  rw [source_factor]
  unfold source
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

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeAfterMac
