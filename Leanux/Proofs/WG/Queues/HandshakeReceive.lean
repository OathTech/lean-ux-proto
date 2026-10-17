import Leanux.Proofs.WG.Queues.HandshakeLoans
import Leanux.Proofs.WG.Queues.HolderTimerCallbacks
import Leanux.Proofs.WG.Queues.SessionCarrier

/-! Charged handshake receive tails keep the actual session and keepalive
execution, then pay the source-acquired peer reference at the final call. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceive
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

private theorem read (pid : PeerId) : Preserves (Boundary cs loans) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  exact (getPeer_normal pid w v p a b run).1 ▸ hi

private theorem update (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀p,(f p).internalId=p.internalId) (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue) (napi : ∀p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀p kid,(f p).keypairCurrent=some kid → p.keypairCurrent=some kid)
    (tx : ∀p,(f p).txQueue.all=p.txQueue.all) :
    Preserves (Boundary cs loans) (getPeer pid >>= fun p => setPeer pid (f p)) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.modify_boundary)
    pid f stamp count rx napi current tx

private theorem update_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (stamp : ∀p,(f p).internalId=p.internalId) (count : ∀p,(f p).refcount=p.refcount)
    (rx : ∀p,(f p).rxQueue=p.rxQueue) (napi : ∀p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀p kid,(f p).keypairCurrent=some kid → p.keypairCurrent=some kid)
    (tx : ∀p,(f p).txQueue.all=p.txQueue.all)
    (next : ∀x, Preserves (Boundary cs loans) (tail x)) :
    Preserves (Boundary cs loans) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (update pid f stamp count rx napi current tx) next

private theorem store (action : WG.M α) (same : SameWGStore action) :
    Preserves (Boundary cs loans) action :=
  HolderEncrypt.native_boundary (HolderEncrypt.store_fields same)

private theorem modifyDevice (f : Device → Device)
    (same : ∀ w, HolderEncrypt.fields {w with dev := w.dev.map f}=HolderEncrypt.fields w) :
    Preserves (Boundary cs loans) (modifyDev f) := by
  apply HolderEncrypt.native_boundary
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases run
  exact same w

macro "handshake_boundary_step" : tactic => `(tactic| first
  | (receive_update_head setPeer
     apply update _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
       (fun _ _ h => h) (fun _ => rfl))
  | (receive_update_head Bind.bind
     apply update_bind _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
       (fun _ _ h => h) (fun _ => rfl)
     intro x)
  | (rx_retention_head getPeer; exact read _)
  | (rx_retention_head getDev; exact store _ getDev_sameWGStore)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head Functor.discard
     apply discard_view_spec id (Boundary _ _)
     change Preserves (Boundary _ _) _)
  | rx_retention_step)

theorem traversal (pid : PeerId) : Preserves (Boundary cs loans) (timersTraversal pid) := by
  unfold timersTraversal
  simp (config := {zeta := false}) only [branchCmp]
  repeat' first
    | (rx_retention_head modPeerTimer; exact HolderTimers.modTimer_boundary _ _ _ _)
    | handshake_boundary_step

theorem sessionDerived (pid : PeerId) : Preserves (Boundary cs loans) (timersSessionDerived pid) := by
  unfold timersSessionDerived
  apply discard_view_spec id (Boundary cs loans)
  exact HolderTimers.modTimer_boundary _ _ _ _

theorem handshakeComplete (pid : PeerId) (site : HiddenSite) :
    Preserves (Boundary cs loans) (timersHandshakeComplete pid site) := by
  unfold timersHandshakeComplete
  apply preserves_bind (HolderTimers.delTimer_boundary pid .retransmitHandshake)
  intro _
  have first : Preserves (Boundary cs loans) (getPeer pid >>= fun p =>
      setPeer pid {p with timerHandshakeAttempts:=0,sentLastminuteHandshake:=false}) :=
    update pid _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ _ h => h) (fun _ => rfl)
  have last (now : List UInt8) : Preserves (Boundary cs loans) (getPeer pid >>= fun p =>
      setPeer pid {p with walltimeLastHandshake:=now}) :=
    update pid _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ _ h => h) (fun _ => rfl)
  have clock : Preserves (Boundary cs loans) (hidden site : WG.M (List UInt8)) := by
    unfold hidden
    exact hoare_liftAmbient (AmbientM.hidden site) (Boundary cs loans)
  simpa only [bind_assoc] using preserves_bind first (fun _ => preserves_bind clock last)

theorem pay (o : Owner) : Hoare (peerPut (some o.slot))
    (Boundary cs (o::loans)) (fun _ => Boundary cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  cases x
  obtain ⟨h,funded,stable⟩ := hi
  have before : CarrierState cs (o::(h.owners ++ loans)) w :=
    WorkReservations.carrier_loans_perm funded.carriers List.perm_middle
  have after := reservation_payment_stable before stable a b run
  have frame := (hoare_iff_run_ambient _ _ _).mp (HolderWorkFrames.peerPut_frame (some o.slot) w)
    w a () v b (Frame.refl w) run
  exact ⟨h,⟨funded.aligned.frame frame,after.1⟩,after.2⟩

/-- The literal final receive tail starts after the selected peer and its
reference have been returned by the handshake arm. -/
def finish (peer : Option PeerId) (pid : PeerId) (msg : List UInt8) : WG.M Unit := do
  let p ← getPeer pid
  setPeer pid {p with rxBytes := p.rxBytes + msg.length}
  modifyDev fun d => {d with rxPackets := d.rxPackets+1,rxBytes:=d.rxBytes+msg.length}
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  peerPut peer

theorem finish_spec (o : Owner) (msg : List UInt8) : Hoare (finish (some o.slot) o.slot msg)
    (Boundary cs (o::loans)) (fun _ => Boundary cs loans) := by
  have stats : Preserves (Boundary cs (o::loans))
      (modifyDev fun d => {d with rxPackets := d.rxPackets+1,rxBytes:=d.rxBytes+msg.length}) := by
    apply modifyDevice
    intro w
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    cases hd : w.dev <;> simp [hd,rxView]
  unfold finish timersAnyAuthenticatedPacketReceived
  rw [← bind_assoc]
  apply hoare_bind _ _ (update o.slot (fun p => {p with rxBytes:=p.rxBytes+msg.length})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl))
  intro _
  apply hoare_bind _ _ stats
  intro _
  apply hoare_bind _ _ (HolderTimers.delTimer_boundary _ _)
  intro _
  apply hoare_bind _ _ (traversal _)
  intro _
  exact pay o

/-- The actual shared continuation records its wrong-packet guard before
resolving the selected optional peer and performing the final payment. -/
def finishSelected (peer : Option PeerId) (msg : List UInt8) : WG.M Unit := do
  if ← branch .hsWrongPacket peer.isNone then invariant "a wrong type of packet in the handshake queue"
  let some pid := peer | invariant "unreachable"
  finish peer pid msg

theorem finishSelected_spec (o : Owner) (msg : List UInt8) :
    Hoare (finishSelected (some o.slot) msg) (Boundary cs (o::loans)) (fun _ => Boundary cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  change ((finish (some o.slot) o.slot msg).run w).run
    (CounterWindow.record a .hsWrongPacket false)=.ok ((x,v),b) at run
  exact (hoare_iff_run_ambient _ _ _).mp (finish_spec o msg) w _ x v b hi run

/-- The response arm's real post-acquisition session and keepalive calls. -/
def responseSession (pid : PeerId) : WG.M Unit := do
  if ← branch .hsRespSessionBegun (← beginSession pid) then
    timersSessionDerived pid
    timersHandshakeComplete pid
    sendKeepalive pid

theorem responseSession_spec (pid : PeerId) : Hoare (responseSession pid)
    (fun w => Boundary cs loans w ∧ ConfiguredIdentity.Inv w ∧ OwnerBounds.Carrier w ∧ CurrentSlots.Inv w)
    (fun _ => Boundary cs loans) := by
  have session : Hoare (beginSession pid)
      (fun w => Boundary cs loans w ∧ ConfiguredIdentity.Inv w ∧ OwnerBounds.Carrier w ∧ CurrentSlots.Inv w)
      (fun _ => Boundary cs loans) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b hi run
    obtain ⟨⟨h,funded,stable⟩,configured,owners,slots⟩ := hi
    have after := SessionCarrier.beginSession_funded pid funded stable configured owners slots a b run
    exact ⟨h,after.1,after.2.1⟩
  unfold responseSession
  apply hoare_bind _ _ session
  intro result
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .hsRespSessionBegun result) (Boundary cs loans))
  intro begun
  cases begun with
  | false => exact preserves_pure _
  | true =>
    apply preserves_bind (sessionDerived pid)
    intro _
    apply preserves_bind (handshakeComplete pid .walltimeLastHandshake)
    intro _
    exact HolderTimers.keepalive_boundary pid

/-- This is the exact existing after-MAC source with its final shared
continuation named; all cookie, type and acquisition guards remain. -/
theorem afterMac_factor (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) :
    Cookies.afterMac msg src underLoad macState = (do
  -- packet_needs_cookie (receive.c:123-132):
  -- `(under_load && mac == WITH_COOKIE) || (!under_load && mac == NO_COOKIE)`
  let proceed ← WG.orM (WG.andM (branch .hsLoadedOperand underLoad) (branch .hsLoadedCookieOk (macState == .withCookie)))
                    (WG.andM (branch .hsNotLoaded (!underLoad)) (branch .hsMacNoCookie (macState == .noCookie)))
  let needsCookie ← do
    if proceed then pure false
    -- `else if (under_load && mac == VALID_MAC_BUT_NO_COOKIE)`
    else if ← WG.andM (branch .hsNeedsCookieLoaded underLoad) (branch .hsNeedsCookieMac (macState == .noCookie)) then
      pure true
    else return   -- invalid MAC: the packet is dropped
  let t := messageType msg
  let peer ← do
    if ← branch .hsSwitchInitiation (t == MESSAGE_HANDSHAKE_INITIATION) then
      if ← branch .hsInitNeedsCookie needsCookie then
        sendHandshakeCookie msg src
        return
      let peer ← consumeInitiation msg
      if ← branch .hsInitNoPeer peer.isNone then return
      let some pid := peer | invariant "unreachable"
      setPeerEndpointFromSkb pid src
      sendHandshakeResponse pid
      pure peer
    else if ← branch .hsSwitchResponse (t == MESSAGE_HANDSHAKE_RESPONSE) then
      if ← branch .hsRespNeedsCookie needsCookie then
        sendHandshakeCookie msg src
        return
      let peer ← consumeResponse msg
      if ← branch .hsRespNoPeer peer.isNone then return
      let some pid := peer | invariant "unreachable"
      setPeerEndpointFromSkb pid src
      if ← branch .hsRespSessionBegun (← beginSession pid) then
        timersSessionDerived pid
        timersHandshakeComplete pid
        sendKeepalive pid
      pure peer
    else pure none
  finishSelected peer msg) := by
  rfl

theorem responseSession_continuation (pid : PeerId) (next : WG.M α) :
    (do
      if ← branch .hsRespSessionBegun (← beginSession pid) then
        timersSessionDerived pid
        timersHandshakeComplete pid
        sendKeepalive pid
      next) = (responseSession pid >>= fun _ => next) := by
  simp only [responseSession,bind_assoc,bind_if_source,pure_bind]

/-- The caller's one acquired reference remains charged across any actual
session/keepalive delta, then the unchanged final payment discharges it. -/
theorem response_paid (o : Owner) (msg : List UInt8) :
    Hoare (responseSession o.slot >>= fun _ => finishSelected (some o.slot) msg)
      (fun w => Boundary cs (o::loans) w ∧ ConfiguredIdentity.Inv w ∧
        OwnerBounds.Carrier w ∧ CurrentSlots.Inv w)
      (fun _ => Boundary cs loans) :=
  hoare_bind _ _ (responseSession_spec o.slot) (fun _ => finishSelected_spec o msg)

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceive
