import Leanux.Proofs.WG.Roaming.HandshakeEndpointSource
import Leanux.Proofs.WG.Roaming.InitiationConsumeSource
import Leanux.Proofs.WG.Roaming.ResponseCallSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
open Origins HandshakeEndpoint

def initiationPacketPrefix (msg : List UInt8) (src : SkbSource) (underLoad : Bool) :
    WG.M (Option InitiationCallCut) := do
  let mac ← cookieValidatePacket msg src underLoad
  let proceed ← WG.orM (WG.andM (branch .hsLoadedOperand underLoad)
      (branch .hsLoadedCookieOk (mac == .withCookie)))
    (WG.andM (branch .hsNotLoaded (!underLoad)) (branch .hsMacNoCookie (mac == .noCookie)))
  let needsCookie ← do
    if proceed then pure false
    else if ← WG.andM (branch .hsNeedsCookieLoaded underLoad)
        (branch .hsNeedsCookieMac (mac == .noCookie)) then pure true
    else return none
  _ ← branch .hsSwitchInitiation true
  if ← branch .hsInitNeedsCookie needsCookie then
    sendHandshakeCookie msg src
    return none
  let consumed ← initiationConsume msg
  if ← branch .hsInitNoPeer consumed.isNone then return none
  let some cut := consumed | invariant "unreachable"
  return some ⟨underLoad, mac, cut, ← Campaign2.read⟩

/-- The original initiation continuation after the endpoint setter. Sending
the response and all common statistics, timers and release remain unchanged. -/
def initiationAfterSetter (msg : List UInt8) (pid : PeerId) : WG.M Unit := do
  sendHandshakeResponse pid
  let peer := some pid
  if ← branch .hsWrongPacket peer.isNone then
    invariant "a wrong type of packet in the handshake queue"
  let some pid := peer | invariant "unreachable"
  let p ← getPeer pid
  setPeer pid { p with rxBytes := p.rxBytes + msg.length }
  modifyDev fun d => { d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + msg.length }
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  peerPut peer

def initiationCallSuffix (msg : List UInt8) (src : SkbSource) : Option InitiationCallCut → WG.M Unit
  | none => pure ()
  | some cut => do
    setPeerEndpointFromSkb cut.consumed.pid src
    initiationAfterSetter msg cut.consumed.pid

def initiationCallPrefix (msg : List UInt8) (src : SkbSource) : WG.M (Option InitiationCallCut) := do
  _ ← branch .hsCookie false
  let underLoad ← responseLoad
  initiationPacketPrefix msg src underLoad

section EndpointContext
open Leanux.Proofs.Logged Origins HandshakeEndpoint
variable {m : Type → Type} [Monad m] (L : HandshakeEndpoint.Lift m)

def initiationSuffixWith (endpoint : PeerId → SkbSource → m Unit)
    (msg : List UInt8) (src : SkbSource) : Option InitiationCallCut → m Unit
  | none => pure ()
  | some cut => do
    endpoint cut.consumed.pid src
    L.action (initiationAfterSetter msg cut.consumed.pid)

theorem initiationPacket_context [LawfulMonad m] (endpoint : PeerId → SkbSource → m Unit)
    (msg : List UInt8) (src : SkbSource) (underLoad : Bool)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (L.action (initiationPacketPrefix msg src underLoad) >>=
      initiationSuffixWith L endpoint msg src) =
    (do let mac ← L.action (cookieValidatePacket msg src underLoad)
        HandshakeSources.afterMacWith (ops L endpoint) msg src underLoad mac) := by
  simp only [HandshakeSources.afterMacWith]
  simp only [response_source]
  simp only [initiationPacketPrefix, kind,
    MESSAGE_HANDSHAKE_INITIATION, Nat.reduceBEq,
    ops_step, ops_initiation, ops_response, ops_endpoint, ops_cookie, ops_session, ops_derived, ops_complete, ops_keepalive, ops_modifyPeer, ops_received, ops_traversal, ops_put, ← initiationConsume_erase msg, initiationPeer,
    lift_bind, lift_pure, initiationSuffixWith, bind_assoc, pure_bind, bind_if, abort_bind, apply_ite]
  simp only [branch_native, lift_bind, lift_pure, bind_assoc, pure_bind,
    Bool.false_eq_true, ite_false, ite_true, Option.isNone_map]
  apply bind_congr_right
  intro mac
  apply bind_congr_right
  intro proceed
  cases proceed <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  apply bind_congr_right
  intro ignored
  apply bind_congr_right
  intro unit2
  apply bind_congr_right
  intro consumed
  cases consumed with
  | none => simp
  | some cut =>
    simp only [Option.isNone_some, Bool.false_eq_true, ite_false, Option.map_some,
      lift_bind, lift_pure, bind_assoc, pure_bind, initiationSuffixWith, initiationAfterSetter,
      read_ignore, branch_native]
    congr 1

theorem initiation_context [LawfulMonad m] (endpoint : PeerId → SkbSource → m Unit)
    (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (L.action (initiationCallPrefix msg src) >>= initiationSuffixWith L endpoint msg src) =
      HandshakeSources.receptionWith (ops L endpoint) msg src := by
  simp only [initiationCallPrefix, HandshakeSources.receptionWith, kind,
    MESSAGE_HANDSHAKE_INITIATION, MESSAGE_HANDSHAKE_COOKIE, Nat.reduceBEq,
    ops_step, branch_native, lift_bind, lift_pure, bind_assoc, pure_bind,
    Bool.false_eq_true, ite_false]
  rw [responseLoad_context_source]
  apply bind_congr_right
  intro ignored
  apply bind_congr_right
  intro loaded
  exact initiationPacket_context L endpoint msg src loaded kind

theorem initiation_prefix_context {E : Type}
    (endpoint : PeerId → SkbSource → WGPrefix E Unit)
    (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (liftWGPrefix (initiationCallPrefix msg src) >>= initiationSuffixWith prefixLift endpoint msg src) =
      HandshakeSources.receptionWith (ops prefixLift endpoint) msg src :=
  initiation_context prefixLift endpoint msg src kind

end EndpointContext

theorem initiationPacket_source (msg : List UInt8) (src : SkbSource) (underLoad : Bool)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (initiationPacketPrefix msg src underLoad >>= initiationCallSuffix msg src) =
      Index.receivePacketBody msg src underLoad := by
  have context := initiationPacket_context native setPeerEndpointFromSkb msg src underLoad kind
  change (initiationPacketPrefix msg src underLoad >>= initiationCallSuffix msg src) =
    (cookieValidatePacket msg src underLoad >>= fun mac =>
      HandshakeSources.afterMacWith HandshakeSources.original msg src underLoad mac) at context
  rw [packet_original]
  simpa only [HandshakeSources.afterMac_original] using context


/-- Every original initiation setter path follows this successful consumer
cut; the no-cut suffix is pure. All original errors are retained. -/
theorem receiveHandshakePacket_initiation (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (initiationCallPrefix msg src >>= initiationCallSuffix msg src) = receiveHandshakePacket msg src := by
  have branch_native (decision : Decision) (value : Bool) :
      (branch decision value : WG.M Bool) = (do
        (monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
          decision, outcome := value, netRx := a.netRxSection}} : AmbientM Unit) : WG.M Unit)
        pure value) := rfl

  rw [← Index.receivePacket_source]
  simp only [initiationCallPrefix, Index.receivePacketSource, kind,
    MESSAGE_HANDSHAKE_INITIATION, MESSAGE_HANDSHAKE_COOKIE, Nat.reduceBEq,
    branch_native, bind_assoc, pure_bind, Bool.false_eq_true, ite_false]
  rw [← responseLoad_source]
  congr 1
  funext ignored
  congr 1
  funext underLoad
  exact initiationPacket_source msg src underLoad kind

def observedInitiationHandshake (msg : List UInt8) (src : SkbSource) :
    WG.M (Campaign2.Outcome (Option InitiationCallCut)) := do
  let observed ← Campaign2.inspect (initiationCallPrefix msg src)
  receiveHandshakePacket msg src
  pure observed

theorem observedInitiationHandshake_erase (msg : List UInt8) (src : SkbSource) :
    (do let _ ← observedInitiationHandshake msg src; pure ()) = receiveHandshakePacket msg src := by
  funext g ambient
  change ((((receiveHandshakePacket msg src).run g).run ambient >>= fun ((_, current), after) =>
    Except.ok ((Campaign2.observeResult (((initiationCallPrefix msg src).run g).run ambient), current), after))
      >>= fun ((_, current), after) => Except.ok (((), current), after)) =
        ((receiveHandshakePacket msg src).run g).run ambient
  cases run : ((receiveHandshakePacket msg src).run g).run ambient with
  | error e => rfl
  | ok pair => rcases pair with ⟨⟨value, final⟩, after⟩; cases value; rfl

def initiationCallTranscript (msg : List UInt8) (src : SkbSource) :
    WG.M (Campaign2.Outcome (Option InitiationCallCut)) := do
  let candidate ← initiationCallPrefix msg src
  let atCut ← Campaign2.read
  initiationCallSuffix msg src candidate
  return .ok (candidate, atCut)

/-- The observation is the actual prefix result selecting the original suffix,
including exact errors; a constant-none observer cannot meet this equality. -/
theorem observedInitiationHandshake_source (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    observedInitiationHandshake msg src = initiationCallTranscript msg src := by
  funext g ambient
  change (((receiveHandshakePacket msg src).run g).run ambient >>= fun ((_, current), after) =>
    Except.ok ((Campaign2.observeResult (((initiationCallPrefix msg src).run g).run ambient), current), after)) = _
  rw [← receiveHandshakePacket_initiation msg src kind]
  change ((((initiationCallPrefix msg src).run g).run ambient >>= fun ((out, current), after) =>
    ((initiationCallSuffix msg src out).run current).run after) >>= fun ((_, current), after) =>
      Except.ok ((Campaign2.observeResult (((initiationCallPrefix msg src).run g).run ambient), current), after)) =
    (((initiationCallPrefix msg src).run g).run ambient >>= fun ((cut, atCut), cutAmbient) =>
      ((initiationCallSuffix msg src cut).run atCut).run cutAmbient >>= fun ((_, current), after) =>
        Except.ok ((Except.ok (cut, Campaign2.snapshot atCut cutAmbient), current), after))
  cases hp : ((initiationCallPrefix msg src).run g).run ambient with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨⟨candidate, atCut⟩, cutAmbient⟩
    cases hs : ((initiationCallSuffix msg src candidate).run atCut).run cutAmbient <;> rfl

end Leanux.Proofs.WG.Roaming
