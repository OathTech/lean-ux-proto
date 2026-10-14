import Leanux.Proofs.WG.Lifetimes.HandshakeSend
import Leanux.Proofs.WG.Lifetimes.CookieAccess
import Leanux.Proofs.WG.Lifetimes.ReceivePoll
import Leanux.Proofs.WG.Cookies.Gate
import Leanux.Proofs.Logged.PrefixWorkers

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Original handshake receive paths, including cookie replies and normal
rejection. Each resident access is observed at its source operation; a Stop
retains the preceding history and skips later cleanup. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def setPeerEndpointFromSkbPrefix (pid : PeerId) (src : SkbSource) : MixedM Unit := do
  let endpoint ← liftPrefix (endpointFromSkb src)
  if ← liftPrefix (branch .epFromSkbOk endpoint.isSome) then
    let some e := endpoint | liftPrefix (invariant "unreachable")
    setPeerEndpointPrefix pid e

def sendBufferAsReplyToSkbPrefix (src : SkbSource) (buffer : List UInt8) : MixedM Unit := do
  if ← liftPrefix (branch .replyInSkbNull false) then
    liftPrefix (invariant "a cookie reply without an skb")
  let endpoint ← liftPrefix (endpointFromSkb src)
  if ← liftPrefix (branch .replyEndpointErr endpoint.isNone) then
    liftPrefix (invariant "a cookie reply to an skb that is neither IPv4 nor IPv6")
  let some e := endpoint | liftPrefix (invariant "unreachable")
  if ← liftPrefix (branch .replyNoMem !(← liftPrefix (hiddenAlloc .replySkb))) then return
  if ← liftPrefix (branch .replyInet (e.family == AF_INET)) then
    _ ← send4Prefix e none buffer 0 false
  else if ← liftPrefix (branch .replyInet6 (e.family == AF_INET6)) then
    _ ← send6Prefix e none buffer 0 false

def sendHandshakeCookiePrefix (msg : List UInt8) (src : SkbSource) : MixedM Unit := do
  let index := u32le msg 4
  let mac1 := (msg.drop (msg.length - 32)).take 16
  sendBufferAsReplyToSkbPrefix src (← liftPrefix (cookieMessageCreate index src mac1))

def afterMacPrefix (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) : MixedM Unit := do
  -- packet_needs_cookie (receive.c:123-132):
  -- `(under_load && mac == WITH_COOKIE) || (!under_load && mac == NO_COOKIE)`
  let proceed ← liftPrefix <| WG.orM (WG.andM (branch .hsLoadedOperand underLoad) (branch .hsLoadedCookieOk (macState == .withCookie)))
                    (WG.andM (branch .hsNotLoaded (!underLoad)) (branch .hsMacNoCookie (macState == .noCookie)))
  let needsCookie ← do
    if proceed then pure false
    -- `else if (under_load && mac == VALID_MAC_BUT_NO_COOKIE)`
    else if ← liftPrefix (WG.andM (branch .hsNeedsCookieLoaded underLoad) (branch .hsNeedsCookieMac (macState == .noCookie))) then
      pure true
    else return   -- invalid MAC: the packet is dropped
  let t := messageType msg
  let peer ← do
    if ← liftPrefix (branch .hsSwitchInitiation (t == MESSAGE_HANDSHAKE_INITIATION)) then
      if ← liftPrefix (branch .hsInitNeedsCookie needsCookie) then
        sendHandshakeCookiePrefix msg src
        return
      let peer ← consumeInitiationPrefix msg
      if ← liftPrefix (branch .hsInitNoPeer peer.isNone) then return
      let some pid := peer | liftPrefix (invariant "unreachable")
      setPeerEndpointFromSkbPrefix pid src
      sendHandshakeResponsePrefix pid
      pure peer
    else if ← liftPrefix (branch .hsSwitchResponse (t == MESSAGE_HANDSHAKE_RESPONSE)) then
      if ← liftPrefix (branch .hsRespNeedsCookie needsCookie) then
        sendHandshakeCookiePrefix msg src
        return
      let peer ← consumeResponsePrefix msg
      if ← liftPrefix (branch .hsRespNoPeer peer.isNone) then return
      let some pid := peer | liftPrefix (invariant "unreachable")
      setPeerEndpointFromSkbPrefix pid src
      if ← liftPrefix (branch .hsRespSessionBegun (← beginSessionPrefix pid)) then
        timersSessionDerivedPrefix pid
        timersHandshakeCompletePrefix pid
        -- either sends the staged packets or stages a keepalive and sends it
        sendKeepalivePrefix pid
      pure peer
    else pure none
  if ← liftPrefix (branch .hsWrongPacket peer.isNone) then liftPrefix (invariant "a wrong type of packet in the handshake queue")
  let some pid := peer | liftPrefix (invariant "unreachable")
  -- Preserve the original peer update before device statistics.
  modifyPeerKeysPrefix pid fun p => { p with rxBytes := p.rxBytes + msg.length }
  liftPrefix (modifyDev (rxStatsUpdate msg.length))
  timersAnyAuthenticatedPacketReceivedPrefix pid
  timersTraversalPrefix pid
  peerPutMixed peer


def receiveHandshakePacketPrefix (msg : List UInt8) (src : SkbSource) : MixedM Unit := do
  if ← liftPrefix (branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE)) then
    cookieMessageConsumePrefix msg
    return
  let loaded ← liftPrefix Cookies.loadPhase
  let mac ← liftPrefix (cookieValidatePacket msg src loaded)
  afterMacPrefix msg src loaded mac

theorem setPeerEndpointFromSkbPrefix_erases (pid : PeerId) (src : SkbSource) :
    ErasesPrefix (setPeerEndpointFromSkbPrefix pid src) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkbPrefix setPeerEndpointFromSkb
  repeat' first
    | with_reducible exact setPeerEndpointPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals exact erasesPrefix_lift _

theorem sendBufferAsReplyToSkbPrefix_erases (src : SkbSource) (buffer : List UInt8) :
    ErasesPrefix (sendBufferAsReplyToSkbPrefix src buffer) (sendBufferAsReplyToSkb src buffer) := by
  unfold sendBufferAsReplyToSkbPrefix sendBufferAsReplyToSkb
  repeat' first
    | with_reducible exact send4Prefix_erases _ _ _ _ _
    | with_reducible exact send6Prefix_erases _ _ _ _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals exact erasesPrefix_lift _

theorem sendHandshakeCookiePrefix_erases (msg : List UInt8) (src : SkbSource) :
    ErasesPrefix (sendHandshakeCookiePrefix msg src) (sendHandshakeCookie msg src) := by
  unfold sendHandshakeCookiePrefix sendHandshakeCookie
  repeat' first
    | with_reducible exact sendBufferAsReplyToSkbPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals exact erasesPrefix_lift _

theorem afterMacPrefix_erases (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) :
    ErasesPrefix (afterMacPrefix msg src underLoad macState) (Cookies.afterMac msg src underLoad macState) := by
  unfold afterMacPrefix Cookies.afterMac
  unfold modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact sendHandshakeCookiePrefix_erases _ _
    | with_reducible exact consumeInitiationPrefix_erases _
    | with_reducible exact consumeResponsePrefix_erases _
    | with_reducible exact setPeerEndpointFromSkbPrefix_erases _ _
    | with_reducible exact sendHandshakeResponsePrefix_erases _
    | with_reducible exact beginSessionPrefix_erases _
    | with_reducible exact timersSessionDerivedPrefix_erases _
    | with_reducible exact timersHandshakeCompletePrefix_erases _ _
    | with_reducible exact sendKeepalivePrefix_erases _
    | with_reducible exact timersAnyAuthenticatedPacketReceivedPrefix_erases _
    | with_reducible exact timersTraversalPrefix_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals exact erasesPrefix_lift _

theorem receiveHandshakePacketPrefix_erases (msg : List UInt8) (src : SkbSource) :
    ErasesPrefix (receiveHandshakePacketPrefix msg src) (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  unfold receiveHandshakePacketPrefix
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro yes
  split
  · exact erasesPrefix_bind (cookieMessageConsumePrefix_erases msg) (fun _ => erasesPrefix_pure _)
  · exact erasesPrefix_bind (erasesPrefix_lift _) (fun loaded =>
      erasesPrefix_bind (erasesPrefix_lift _) (fun mac => afterMacPrefix_erases msg src loaded mac))


/-- Short-circuit Boolean actions inspect no resident stores when their
constituents do not; the frame composes only their normal endpoints. -/
theorem andM_sameKernel (ha : SameKernel a) (hb : SameKernel b) : SameKernel (WG.andM a b) := by
  unfold WG.andM
  apply sameKernel_bind ha
  intro yes
  split
  · exact hb
  · exact sameKernel_pure _

/-- Named lower-level mutation contracts, independent of the receive observer.
In particular arbitrary ambient invariants must permit cookie and device-stat
updates; identity equality alone would not justify these premises. -/
structure HandshakeReceiveContracts (I : List LifetimeEvent → World → Prop) : Prop where
  socket : SocketContracts I
  cookie : CookieStable I
  tx : TxContracts I
  stats : ∀ len, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (modifyDev (rxStatsUpdate len)))
  index : ∀ pid kind, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexInsert pid kind))
  create : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (keypairCreatePrefix pid)
  put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (keypairPutPrefix kp now)
  replace : ∀ pid kp, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexReplaceHandshake pid kp))

theorem allocationHandshakeReceive : HandshakeReceiveContracts AllocationInv where
  socket := allocationSocket
  cookie := allocationCookieStable
  tx := allocationTx
  stats := allocationRx.stats
  index := indexInsert_allocation
  create := keypairCreatePrefix_preserves
  put := keypairPutPrefix_allocation
  replace := indexReplaceHandshake_allocation

theorem setPeerEndpointFromSkbPrefix_preserves (c : AmbientContracts I) (pid : PeerId) (src : SkbSource) :
    PrefixPreserves I LifetimeEvent.Safe (setPeerEndpointFromSkbPrefix pid src) := by
  unfold setPeerEndpointFromSkbPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (endpointFromSkb_sameKernel _))
    | with_reducible exact AmbientContracts.drop (setPeerEndpointPrefix_spec c (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem sendBufferAsReplyToSkbPrefix_preserves (c : AmbientContracts I) (sc : SocketContracts I)
    (src : SkbSource) (buffer : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (sendBufferAsReplyToSkbPrefix src buffer) := by
  unfold sendBufferAsReplyToSkbPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (endpointFromSkb_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (hiddenAlloc_sameKernel _))
    | with_reducible exact AmbientContracts.drop (send4Prefix_spec c sc (fun _ => True) _ _ _ _ _)
    | with_reducible exact AmbientContracts.drop (send6Prefix_spec c sc (fun _ => True) _ _ _ _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem sendHandshakeCookiePrefix_preserves (c : AmbientContracts I) (r : HandshakeReceiveContracts I)
    (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves I LifetimeEvent.Safe (sendHandshakeCookiePrefix msg src) :=
  PrefixPreserves.bind (AmbientContracts.drop
    (cookieLift_spec c r.cookie (fun _ => True) _ (cookieMessageCreate_sameCookieKernel _ _ _)))
    (fun _ => sendBufferAsReplyToSkbPrefix_preserves c r.socket src _)

theorem afterMacPrefix_preserves (c : AmbientContracts I) (r : HandshakeReceiveContracts I)
    (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    PrefixPreserves I LifetimeEvent.Safe (afterMacPrefix msg src loaded mac) := by
  unfold afterMacPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _
        (orM_sameKernel (andM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _))
          (andM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _))))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _
        (andM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _)))
    | with_reducible exact sendHandshakeCookiePrefix_preserves c r _ _
    | with_reducible exact consumeInitiationPrefix_preserves c _
    | with_reducible exact consumeResponsePrefix_preserves c _
    | with_reducible exact setPeerEndpointFromSkbPrefix_preserves c _ _
    | with_reducible exact sendHandshakeResponsePrefix_preserves c r.socket r.index r.create r.put r.replace _
    | with_reducible exact beginSessionPrefix_preserves_ambient c r.create r.put r.replace _
    | with_reducible exact AmbientContracts.drop (timersSessionDerivedPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (timersHandshakeCompletePrefix_spec c (fun _ => True) _ _)
    | with_reducible exact sendKeepalivePrefix_preserves_ambient c r.tx _
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact r.stats _
    | with_reducible exact AmbientContracts.drop (timersAnyAuthenticatedPacketReceivedPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (timersTraversalPrefix_spec c (fun _ => True) _)
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem receiveHandshakePacketPrefix_preserves (c : AmbientContracts I) (r : HandshakeReceiveContracts I)
    (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves I LifetimeEvent.Safe (receiveHandshakePacketPrefix msg src) := by
  unfold receiveHandshakePacketPrefix
  repeat' first
    | with_reducible exact cookieMessageConsumePrefix_preserves c _
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ Cookies.loadPhase_sameKernel)
    | with_reducible exact AmbientContracts.drop (cookieLift_spec c r.cookie (fun _ => True) _
        (cookieValidatePacket_sameCookieKernel _ _ _))
    | with_reducible exact afterMacPrefix_preserves c r _ _ _ _
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

end Leanux.Proofs.WG.Lifetimes
