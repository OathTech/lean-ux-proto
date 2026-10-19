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
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def setPeerEndpointFromSkbPrefix (pid : PeerId) (src : SkbSource) : MixedM Unit := do
  let endpoint ← liftWGPrefix (endpointFromSkb src)
  if ← liftWGPrefix (branch .epFromSkbOk endpoint.isSome) then
    let some e := endpoint | liftWGPrefix (invariant "unreachable")
    setPeerEndpointPrefix pid e

def sendBufferAsReplyToSkbPrefix (src : SkbSource) (buffer : List UInt8) : MixedM Unit := do
  if ← liftWGPrefix (branch .replyInSkbNull false) then
    liftWGPrefix (invariant "a cookie reply without an skb")
  let endpoint ← liftWGPrefix (endpointFromSkb src)
  if ← liftWGPrefix (branch .replyEndpointErr endpoint.isNone) then
    liftWGPrefix (invariant "a cookie reply to an skb that is neither IPv4 nor IPv6")
  let some e := endpoint | liftWGPrefix (invariant "unreachable")
  if ← liftWGPrefix (branch .replyNoMem !(← liftWGPrefix (hiddenAlloc .replySkb))) then return
  if ← liftWGPrefix (branch .replyInet (e.family == AF_INET)) then
    _ ← send4Prefix e none buffer 0 false
  else if ← liftWGPrefix (branch .replyInet6 (e.family == AF_INET6)) then
    _ ← send6Prefix e none buffer 0 false

def sendHandshakeCookiePrefix (msg : List UInt8) (src : SkbSource) : MixedM Unit := do
  let index := u32le msg 4
  let mac1 := (msg.drop (msg.length - 32)).take 16
  sendBufferAsReplyToSkbPrefix src (← liftWGPrefix (cookieMessageCreate index src mac1))

def afterMacPrefix (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) : MixedM Unit := do
  -- packet_needs_cookie (receive.c:123-132):
  -- `(under_load && mac == WITH_COOKIE) || (!under_load && mac == NO_COOKIE)`
  let proceed ← liftWGPrefix <| WG.orM (WG.andM (branch .hsLoadedOperand underLoad) (branch .hsLoadedCookieOk (macState == .withCookie)))
                    (WG.andM (branch .hsNotLoaded (!underLoad)) (branch .hsMacNoCookie (macState == .noCookie)))
  let needsCookie ← do
    if proceed then pure false
    -- `else if (under_load && mac == VALID_MAC_BUT_NO_COOKIE)`
    else if ← liftWGPrefix (WG.andM (branch .hsNeedsCookieLoaded underLoad) (branch .hsNeedsCookieMac (macState == .noCookie))) then
      pure true
    else return   -- invalid MAC: the packet is dropped
  let t := messageType msg
  let peer ← do
    if ← liftWGPrefix (branch .hsSwitchInitiation (t == MESSAGE_HANDSHAKE_INITIATION)) then
      if ← liftWGPrefix (branch .hsInitNeedsCookie needsCookie) then
        sendHandshakeCookiePrefix msg src
        return
      let peer ← consumeInitiationPrefix msg
      if ← liftWGPrefix (branch .hsInitNoPeer peer.isNone) then return
      let some pid := peer | liftWGPrefix (invariant "unreachable")
      setPeerEndpointFromSkbPrefix pid src
      sendHandshakeResponsePrefix pid
      pure peer
    else if ← liftWGPrefix (branch .hsSwitchResponse (t == MESSAGE_HANDSHAKE_RESPONSE)) then
      if ← liftWGPrefix (branch .hsRespNeedsCookie needsCookie) then
        sendHandshakeCookiePrefix msg src
        return
      let peer ← consumeResponsePrefix msg
      if ← liftWGPrefix (branch .hsRespNoPeer peer.isNone) then return
      let some pid := peer | liftWGPrefix (invariant "unreachable")
      setPeerEndpointFromSkbPrefix pid src
      if ← liftWGPrefix (branch .hsRespSessionBegun (← beginSessionPrefix pid)) then
        timersSessionDerivedPrefix pid
        timersHandshakeCompletePrefix pid
        -- either sends the staged packets or stages a keepalive and sends it
        sendKeepalivePrefix pid
      pure peer
    else pure none
  if ← liftWGPrefix (branch .hsWrongPacket peer.isNone) then liftWGPrefix (invariant "a wrong type of packet in the handshake queue")
  let some pid := peer | liftWGPrefix (invariant "unreachable")
  -- Preserve the original peer update before device statistics.
  modifyPeerKeysPrefix pid fun p => { p with rxBytes := p.rxBytes + msg.length }
  liftWGPrefix (modifyDev (rxStatsUpdate msg.length))
  timersAnyAuthenticatedPacketReceivedPrefix pid
  timersTraversalPrefix pid
  peerPutMixed peer


def receiveHandshakePacketPrefix (msg : List UInt8) (src : SkbSource) : MixedM Unit := do
  if ← liftWGPrefix (branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE)) then
    cookieMessageConsumePrefix msg
    return
  let loaded ← liftWGPrefix Cookies.loadPhase
  let mac ← liftWGPrefix (cookieValidatePacket msg src loaded)
  afterMacPrefix msg src loaded mac

theorem setPeerEndpointFromSkbPrefix_erases (pid : PeerId) (src : SkbSource) :
    ErasesStatePrefix (setPeerEndpointFromSkbPrefix pid src) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkbPrefix setPeerEndpointFromSkb
  repeat' first
    | consume_conditional
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head setPeerEndpointPrefix; exact setPeerEndpointPrefix_erases _ _)
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_erases _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | consume_erases_modify_bind
    | maintenance_erases_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match


theorem sendBufferAsReplyToSkbPrefix_erases (src : SkbSource) (buffer : List UInt8) :
    ErasesStatePrefix (sendBufferAsReplyToSkbPrefix src buffer) (sendBufferAsReplyToSkb src buffer) := by
  unfold sendBufferAsReplyToSkbPrefix sendBufferAsReplyToSkb
  repeat' first
    | consume_conditional
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head send4Prefix; exact send4Prefix_erases _ _ _ _ _)
    | (maintenance_head send6Prefix; exact send6Prefix_erases _ _ _ _ _)
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_erases _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | consume_erases_modify_bind
    | maintenance_erases_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match


theorem sendHandshakeCookiePrefix_erases (msg : List UInt8) (src : SkbSource) :
    ErasesStatePrefix (sendHandshakeCookiePrefix msg src) (sendHandshakeCookie msg src) := by
  unfold sendHandshakeCookiePrefix sendHandshakeCookie
  repeat' first
    | consume_conditional
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head sendBufferAsReplyToSkbPrefix; exact sendBufferAsReplyToSkbPrefix_erases _ _)
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_erases _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | consume_erases_modify_bind
    | maintenance_erases_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match


theorem afterMacPrefix_erases (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) :
    ErasesStatePrefix (afterMacPrefix msg src underLoad macState) (Cookies.afterMac msg src underLoad macState) := by
  unfold afterMacPrefix Cookies.afterMac
  repeat' first
    | consume_conditional
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head sendHandshakeCookiePrefix; exact sendHandshakeCookiePrefix_erases _ _)
    | (maintenance_head consumeInitiationPrefix; exact consumeInitiationPrefix_erases _)
    | (maintenance_head consumeResponsePrefix; exact consumeResponsePrefix_erases _)
    | (maintenance_head setPeerEndpointFromSkbPrefix; exact setPeerEndpointFromSkbPrefix_erases _ _)
    | (maintenance_head sendHandshakeResponsePrefix; exact sendHandshakeResponsePrefix_erases _)
    | (maintenance_head beginSessionPrefix; exact beginSessionPrefix_erases _)
    | (maintenance_head timersSessionDerivedPrefix; exact timersSessionDerivedPrefix_erases _)
    | (maintenance_head timersHandshakeCompletePrefix; exact timersHandshakeCompletePrefix_erases _ _)
    | (maintenance_head sendKeepalivePrefix; exact sendKeepalivePrefix_erases _)
    | (maintenance_head timersAnyAuthenticatedPacketReceivedPrefix; exact timersAnyAuthenticatedPacketReceivedPrefix_erases _)
    | (maintenance_head timersTraversalPrefix; exact timersTraversalPrefix_erases _)
    | (maintenance_head peerPutMixed; exact peerPutMixed_erases _)
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_erases _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | consume_erases_modify_bind
    | maintenance_erases_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match


theorem receiveHandshakePacketPrefix_erases (msg : List UInt8) (src : SkbSource) :
    ErasesStatePrefix (receiveHandshakePacketPrefix msg src) (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  unfold receiveHandshakePacketPrefix
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro yes
  split
  · exact erasesStatePrefix_bind (cookieMessageConsumePrefix_erases msg) (fun _ => erasesStatePrefix_pure _)
  · exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun loaded =>
      erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun mac => afterMacPrefix_erases msg src loaded mac))


/-- Short-circuit Boolean actions inspect no resident stores when their
constituents do not; the frame composes only their normal endpoints. -/
theorem andM_sameView {S V : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {view : S → V} {a b : StateT S m Bool}
    (ha : SameView view a) (hb : SameView view b) :
    SameView view (do if ← a then b else pure false) := by
  apply SameView.bind ha
  intro yes
  split
  · exact hb
  · exact SameView.pure view false


structure HandshakeReceiveContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  socket : SocketContracts I
  cookie : CookieStable I
  tx : TxContracts I
  stats : ∀ len, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (modifyDev (rxStatsUpdate len)))
  index : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (liftIndex (indexInsert owner)))
  create : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairCreatePrefix pid)
  put : ∀ kp now, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairPutPrefix kp now)
  replace : ∀ pid kp, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (liftIndex (indexReplaceHandshake pid kp)))

structure ProductHandshakeReceiveContracts (I : List LifetimeEvent → World → Prop) : Prop where
  socket : ProductSocketContracts I
  cookie : ProductCookieStable I
  tx : ProductTxContracts I
  stats : ∀ len, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (modifyDev (rxStatsUpdate len))))
  index : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (liftIndex (indexInsert owner))))
  create : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairCreatePrefix pid))
  put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now))
  replace : ∀ pid kp, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (liftIndex (indexReplaceHandshake pid kp))))

theorem ProductHandshakeReceiveContracts.ofNative (r : HandshakeReceiveContracts I) :
    ProductHandshakeReceiveContracts (fun h w => I h w.wg) where
  socket := ⟨fun P count => (r.socket.stats P count).liftWGObserver⟩
  cookie := fun h w v he hi => r.cookie h w.wg v.wg (congrArg (fun s : ProductStore43 => s.2.2.2) he) hi
  tx := ProductTxContracts.ofNative r.tx
  stats := fun len => (r.stats len).liftWGObserver
  index := fun owner => (r.index owner).liftWGObserver
  create := fun pid => (r.create pid).liftWGObserver
  put := fun kp now => (r.put kp now).liftWGObserver
  replace := fun pid kp => (r.replace pid kp).liftWGObserver

theorem allocationHandshakeReceive : HandshakeReceiveContracts AllocationInv where
  socket := allocationSocket
  cookie := allocationCookieStable
  tx := allocationTx
  stats := allocationRx.stats
  index := by
    intro owner
    apply StatePrefixEnsures.lift _ (fun h w _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    have hp : Hoare (liftIndex (indexInsert owner)) (AllocationInv h) (fun _ => AllocationInv h) := by
      apply hoare_liftIndex
      intro g d table hg hd
      apply hg.congr
      · unfold identityView Peers.snapshot keypairResidents packetResidents
        simp [hd]
      · simp [allocationMetadata, deviceAllocationMetadata, hd]
    exact (hoare_iff_run_ambient _ _ _).mp hp w ambient x v ambient' hi hr
  create := keypairCreatePrefix_preserves
  put := keypairPutPrefix_allocation
  replace := indexReplaceHandshake_allocation

theorem setPeerEndpointFromSkbPrefix_preserves (c : AmbientContracts I) (pid : PeerId) (src : SkbSource) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (setPeerEndpointFromSkbPrefix pid src) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    AmbientContracts.drop (c.store (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (StateT.lift a)) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold setPeerEndpointFromSkbPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head setPeerEndpointPrefix; exact AmbientContracts.drop (setPeerEndpointPrefix_spec c (fun _ => True) _ _))
    | (maintenance_lift_action_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _))
    | (maintenance_lift_action_head hiddenAlloc; exact ambient (AmbientM.hiddenAlloc _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match


theorem sendBufferAsReplyToSkbPrefix_preserves (c : AmbientContracts I) (sc : SocketContracts I)
    (src : SkbSource) (buffer : List UInt8) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (sendBufferAsReplyToSkbPrefix src buffer) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    AmbientContracts.drop (c.store (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (StateT.lift a)) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold sendBufferAsReplyToSkbPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head send4Prefix; exact AmbientContracts.drop (send4Prefix_spec c sc (fun _ => True) _ _ _ _ _))
    | (maintenance_head send6Prefix; exact AmbientContracts.drop (send6Prefix_spec c sc (fun _ => True) _ _ _ _ _))
    | (maintenance_lift_action_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _))
    | (maintenance_lift_action_head hiddenAlloc; exact ambient (AmbientM.hiddenAlloc _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match


theorem sendHandshakeCookiePrefix_preserves (c : AmbientContracts I) (r : HandshakeReceiveContracts I)
    (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (sendHandshakeCookiePrefix msg src) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    AmbientContracts.drop (c.store (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (StateT.lift a)) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold sendHandshakeCookiePrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head sendBufferAsReplyToSkbPrefix; exact sendBufferAsReplyToSkbPrefix_preserves c r.socket _ _)
    | (maintenance_lift_action_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _))
    | (maintenance_lift_action_head hiddenAlloc; exact ambient (AmbientM.hiddenAlloc _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_lift_action_head cookieMessageCreate; exact CookieCall.preserves_ambient c r.cookie (.create _ _ _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match


theorem afterMacPrefix_preserves (c : AmbientContracts I) (r : HandshakeReceiveContracts I)
    (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (afterMacPrefix msg src loaded mac) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    AmbientContracts.drop (c.store (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (StateT.lift a)) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold afterMacPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head sendHandshakeCookiePrefix; exact sendHandshakeCookiePrefix_preserves c r _ _)
    | (maintenance_head consumeInitiationPrefix; exact consumeInitiationPrefix_preserves c _)
    | (maintenance_head consumeResponsePrefix; exact consumeResponsePrefix_preserves c _)
    | (maintenance_head setPeerEndpointFromSkbPrefix; exact setPeerEndpointFromSkbPrefix_preserves c _ _)
    | (maintenance_head sendHandshakeResponsePrefix; exact sendHandshakeResponsePrefix_preserves c r.socket r.index r.create r.put r.replace _)
    | (maintenance_head beginSessionPrefix; exact beginSessionPrefix_preserves_ambient c r.create r.put r.replace _)
    | (maintenance_head timersSessionDerivedPrefix; exact AmbientContracts.drop (timersSessionDerivedPrefix_spec c (fun _ => True) _))
    | (maintenance_head timersHandshakeCompletePrefix; exact AmbientContracts.drop (timersHandshakeCompletePrefix_spec c (fun _ => True) _ _))
    | (maintenance_head sendKeepalivePrefix; exact sendKeepalivePrefix_preserves_ambient c r.tx _)
    | (maintenance_head modifyPeerKeysPrefix; exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head timersAnyAuthenticatedPacketReceivedPrefix; exact AmbientContracts.drop (timersAnyAuthenticatedPacketReceivedPrefix_spec c (fun _ => True) _))
    | (maintenance_head timersTraversalPrefix; exact AmbientContracts.drop (timersTraversalPrefix_spec c (fun _ => True) _))
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_lift_action_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _))
    | (maintenance_lift_action_head hiddenAlloc; exact ambient (AmbientM.hiddenAlloc _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_lift_action_head WG.orM; apply store; apply orM_sameView <;> apply andM_sameView <;> intro initial <;> exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (maintenance_lift_action_head WG.andM; apply store; apply andM_sameView <;> intro initial <;> exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (maintenance_lift_action_head modifyDev; exact r.stats _)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match


theorem receiveHandshakePacketPrefix_preserves (c : AmbientContracts I) (r : HandshakeReceiveContracts I)
    (msg : List UInt8) (src : SkbSource) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (receiveHandshakePacketPrefix msg src) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    AmbientContracts.drop (c.store (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (StateT.lift a)) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold receiveHandshakePacketPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head cookieMessageConsumePrefix; exact cookieMessageConsumePrefix_preserves c _)
    | (maintenance_head afterMacPrefix; exact afterMacPrefix_preserves c r _ _ _ _)
    | (maintenance_lift_action_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _))
    | (maintenance_lift_action_head hiddenAlloc; exact ambient (AmbientM.hiddenAlloc _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_lift_action_head Cookies.loadPhase; exact store _ Cookies.loadPhase_sameStore)
    | (maintenance_lift_action_head cookieValidatePacket; exact CookieCall.preserves_ambient c r.cookie (.validate _ _ _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match


theorem setPeerEndpointFromSkbPrefix_preserves_product (c : ProductAmbientContracts I) (pid : PeerId) (src : SkbSource) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (setPeerEndpointFromSkbPrefix pid src)) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (StateT.lift a))) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  apply PrefixEnsures.preserves
  unfold setPeerEndpointFromSkbPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_lift
    | (maintenance_head setPeerEndpointPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (setPeerEndpointPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_lift_action_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _))
    | (maintenance_lift_action_head hiddenAlloc; exact ambient (AmbientM.hiddenAlloc _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem sendBufferAsReplyToSkbPrefix_preserves_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I)
    (src : SkbSource) (buffer : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (sendBufferAsReplyToSkbPrefix src buffer)) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (StateT.lift a))) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  apply PrefixEnsures.preserves
  unfold sendBufferAsReplyToSkbPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_lift
    | (maintenance_head send4Prefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (send4Prefix_spec_product c sc (fun _ => True) _ _ _ _ _))
    | (maintenance_head send6Prefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (send6Prefix_spec_product c sc (fun _ => True) _ _ _ _ _))
    | (maintenance_lift_action_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _))
    | (maintenance_lift_action_head hiddenAlloc; exact ambient (AmbientM.hiddenAlloc _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem sendHandshakeCookiePrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductHandshakeReceiveContracts I)
    (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (sendHandshakeCookiePrefix msg src)) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (StateT.lift a))) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  apply PrefixEnsures.preserves
  unfold sendHandshakeCookiePrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_lift
    | (maintenance_head sendBufferAsReplyToSkbPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact sendBufferAsReplyToSkbPrefix_preserves_product c r.socket _ _)
    | (maintenance_lift_action_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _))
    | (maintenance_lift_action_head hiddenAlloc; exact ambient (AmbientM.hiddenAlloc _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_lift_action_head cookieMessageCreate; exact CookieCall.preserves_product c r.cookie (.create _ _ _))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem afterMacPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductHandshakeReceiveContracts I)
    (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (afterMacPrefix msg src loaded mac)) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (StateT.lift a))) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  apply PrefixEnsures.preserves
  unfold afterMacPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_lift
    | (maintenance_head sendHandshakeCookiePrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact sendHandshakeCookiePrefix_preserves_product c r _ _)
    | (maintenance_head consumeInitiationPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact consumeInitiationPrefix_preserves_product c _)
    | (maintenance_head consumeResponsePrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact consumeResponsePrefix_preserves_product c _)
    | (maintenance_head setPeerEndpointFromSkbPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact setPeerEndpointFromSkbPrefix_preserves_product c _ _)
    | (maintenance_head sendHandshakeResponsePrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact sendHandshakeResponsePrefix_preserves_product c r.socket r.index r.create r.put r.replace _)
    | (maintenance_head beginSessionPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact beginSessionPrefix_preserves_product c r.create r.put r.replace _)
    | (maintenance_head timersSessionDerivedPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (timersSessionDerivedPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head timersHandshakeCompletePrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (timersHandshakeCompletePrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head sendKeepalivePrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact sendKeepalivePrefix_preserves_product c r.tx _)
    | (maintenance_head modifyPeerKeysPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head timersAnyAuthenticatedPacketReceivedPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (timersAnyAuthenticatedPacketReceivedPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head timersTraversalPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (timersTraversalPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head peerPutMixed; change PrefixPreserves I LifetimeEvent.Safe _; exact c.peerPut _)
    | (maintenance_lift_action_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _))
    | (maintenance_lift_action_head hiddenAlloc; exact ambient (AmbientM.hiddenAlloc _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_lift_action_head WG.orM; apply store; apply orM_sameView <;> apply andM_sameView <;> intro initial <;> exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (maintenance_lift_action_head WG.andM; apply store; apply andM_sameView <;> intro initial <;> exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (maintenance_lift_action_head modifyDev; exact r.stats _)
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem receiveHandshakePacketPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductHandshakeReceiveContracts I)
    (msg : List UInt8) (src : SkbSource) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (receiveHandshakePacketPrefix msg src)) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (StateT.lift a))) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  apply PrefixEnsures.preserves
  unfold receiveHandshakePacketPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_lift
    | (maintenance_head cookieMessageConsumePrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact cookieMessageConsumePrefix_preserves_product c _)
    | (maintenance_head afterMacPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact afterMacPrefix_preserves_product c r _ _ _ _)
    | (maintenance_lift_action_head endpointFromSkb; exact store _ (endpointFromSkb_sameWGStore _))
    | (maintenance_lift_action_head hiddenAlloc; exact ambient (AmbientM.hiddenAlloc _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_lift_action_head Cookies.loadPhase; exact store _ Cookies.loadPhase_sameStore)
    | (maintenance_lift_action_head cookieValidatePacket; exact CookieCall.preserves_product c r.cookie (.validate _ _ _))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

end Leanux.Proofs.WG.Lifetimes
