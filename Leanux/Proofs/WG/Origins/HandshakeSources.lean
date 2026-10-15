import Leanux.Proofs.WG.Lifetimes.HandshakeReceive
import Leanux.Proofs.WG.Lifetimes.ReceiveWorker

/-! Callback-parametric factors of the original handshake source. The original
and existing lifetime observer instantiate the same branches and continuations;
only the session callback will gain a receipt in the persistent history. -/
namespace Leanux.Proofs.WG.Origins.HandshakeSources
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

structure Ops (m : Type → Type) where
  step : {α : Type} → M α → m α
  session : PeerId → m Bool
  modifyPeer : PeerId → (Peer → Peer) → m Unit
  create : PeerId → m (Option (List UInt8))
  mac : PeerId → List UInt8 → m (List UInt8)
  send : PeerId → List UInt8 → m Unit
  derived : PeerId → m Unit
  traversal : PeerId → m Unit
  sent : PeerId → m Unit
  cookie : List UInt8 → SkbSource → m Unit
  initiation : List UInt8 → m (Option PeerId)
  response : List UInt8 → m (Option PeerId)
  endpoint : PeerId → SkbSource → m Unit
  complete : PeerId → m Unit
  keepalive : PeerId → m Unit
  received : PeerId → m Unit
  put : Option PeerId → m Unit
  cookieConsume : List UInt8 → m Unit

def responseWith {m : Type → Type} [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  let now ← o.step (hiddenClock64 .respLastSent)
  o.modifyPeer pid fun p => {p with lastSentHandshake := now}
  let created ← o.create pid
  if ← o.step (branch .respCreated created.isSome) then
    let some msg := created | o.step (invariant "unreachable")
    let msg ← o.mac pid msg
    if ← o.step (branch .respSessionBegun (← o.session pid)) then
      o.derived pid
      o.traversal pid
      o.sent pid
      let now ← o.step (hiddenClock64 .respLastSentAgain)
      o.modifyPeer pid fun p => {p with lastSentHandshake := now}
      o.send pid msg

def afterMacWith {m : Type → Type} [Monad m] (o : Ops m)
    (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) : m Unit := do
  let proceed ← o.step <| WG.orM (WG.andM (branch .hsLoadedOperand underLoad) (branch .hsLoadedCookieOk (macState == .withCookie)))
                    (WG.andM (branch .hsNotLoaded (!underLoad)) (branch .hsMacNoCookie (macState == .noCookie)))
  let needsCookie ← do
    if proceed then pure false
    else if ← o.step (WG.andM (branch .hsNeedsCookieLoaded underLoad) (branch .hsNeedsCookieMac (macState == .noCookie))) then
      pure true
    else return
  let t := messageType msg
  let peer ← do
    if ← o.step (branch .hsSwitchInitiation (t == MESSAGE_HANDSHAKE_INITIATION)) then
      if ← o.step (branch .hsInitNeedsCookie needsCookie) then
        o.cookie msg src
        return
      let peer ← o.initiation msg
      if ← o.step (branch .hsInitNoPeer peer.isNone) then return
      let some pid := peer | o.step (invariant "unreachable")
      o.endpoint pid src
      responseWith o pid
      pure peer
    else if ← o.step (branch .hsSwitchResponse (t == MESSAGE_HANDSHAKE_RESPONSE)) then
      if ← o.step (branch .hsRespNeedsCookie needsCookie) then
        o.cookie msg src
        return
      let peer ← o.response msg
      if ← o.step (branch .hsRespNoPeer peer.isNone) then return
      let some pid := peer | o.step (invariant "unreachable")
      o.endpoint pid src
      if ← o.step (branch .hsRespSessionBegun (← o.session pid)) then
        o.derived pid
        o.complete pid
        o.keepalive pid
      pure peer
    else pure none
  if ← o.step (branch .hsWrongPacket peer.isNone) then o.step (invariant "a wrong type of packet in the handshake queue")
  let some pid := peer | o.step (invariant "unreachable")
  o.modifyPeer pid fun p => {p with rxBytes := p.rxBytes + msg.length}
  o.step (modifyDev (rxStatsUpdate msg.length))
  o.received pid
  o.traversal pid
  o.put peer

def receptionWith {m : Type → Type} [Monad m] (o : Ops m)
    (msg : List UInt8) (src : SkbSource) : m Unit := do
  if ← o.step (branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE)) then
    o.cookieConsume msg
    return
  let loaded ← o.step Cookies.loadPhase
  let mac ← o.step (cookieValidatePacket msg src loaded)
  afterMacWith o msg src loaded mac

def stepWith {m : Type → Type} [Monad m] (o : Ops m) : m Bool := do
  match (← o.step getDev).handshakeQueue.consume with
  | (none, _) =>
    _ ← o.step (branch .workerConsumed false)
    return false
  | (some (msg, src), ring) =>
    _ ← o.step (branch .workerConsumed true)
    o.step (modifyDev fun d => {d with handshakeQueue := ring})
    receptionWith o msg src
    o.step (modifyDev fun d => {d with handshakeQueueLen := d.handshakeQueueLen - 1})
    return true

def original : Ops M where
  step := fun a => a
  session := beginSession
  modifyPeer := fun pid f => do setPeer pid (f (← getPeer pid))
  create := createResponse
  mac := addMacToPacket
  send := sendBufferToPeer
  derived := timersSessionDerived
  traversal := timersTraversal
  sent := timersAnyAuthenticatedPacketSent
  cookie := sendHandshakeCookie
  initiation := consumeInitiation
  response := consumeResponse
  endpoint := setPeerEndpointFromSkb
  complete := timersHandshakeComplete
  keepalive := sendKeepalive
  received := timersAnyAuthenticatedPacketReceived
  put := WG.peerPut
  cookieConsume := cookieMessageConsume

def prefixOps : Ops MixedM where
  step := liftPrefix
  session := beginSessionPrefix
  modifyPeer := modifyPeerKeysPrefix
  create := createResponsePrefix
  mac := addMacToPacketPrefix
  send := sendBufferToPeerPrefix
  derived := timersSessionDerivedPrefix
  traversal := timersTraversalPrefix
  sent := timersAnyAuthenticatedPacketSentPrefix
  cookie := sendHandshakeCookiePrefix
  initiation := consumeInitiationPrefix
  response := consumeResponsePrefix
  endpoint := setPeerEndpointFromSkbPrefix
  complete := timersHandshakeCompletePrefix
  keepalive := sendKeepalivePrefix
  received := timersAnyAuthenticatedPacketReceivedPrefix
  put := peerPutMixed
  cookieConsume := cookieMessageConsumePrefix

theorem response_original (pid : PeerId) : responseWith original pid = sendHandshakeResponse pid := by
  simp only [responseWith, original, sendHandshakeResponse, bind_assoc]
  rfl

theorem response_prefix (pid : PeerId) : responseWith prefixOps pid = sendHandshakeResponsePrefix pid := rfl

theorem afterMac_original (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    afterMacWith original msg src loaded mac = Cookies.afterMac msg src loaded mac := by
  unfold afterMacWith Cookies.afterMac
  simp only [response_original]
  simp only [original, bind_assoc]
  rfl

theorem afterMac_prefix (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    afterMacWith prefixOps msg src loaded mac = afterMacPrefix msg src loaded mac := by
  unfold afterMacWith afterMacPrefix
  simp only [response_prefix]
  rfl

theorem reception_original (msg : List UInt8) (src : SkbSource) :
    receptionWith original msg src = receiveHandshakePacket msg src := by
  rw [Cookies.receive_factor]
  unfold receptionWith
  simp only [afterMac_original]
  rfl

theorem reception_prefix (msg : List UInt8) (src : SkbSource) :
    receptionWith prefixOps msg src = receiveHandshakePacketPrefix msg src := by
  unfold receptionWith receiveHandshakePacketPrefix
  simp only [afterMac_prefix]
  rfl

theorem step_original : stepWith original = receiveStep := by
  unfold stepWith receiveStep
  simp only [reception_original]
  rfl

theorem step_prefix : stepWith prefixOps = receiveStepPrefix := by
  unfold stepWith receiveStepPrefix
  simp only [reception_prefix]
  rfl

end Leanux.Proofs.WG.Origins.HandshakeSources
