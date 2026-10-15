import Leanux.Proofs.WG.Roaming.InitiationConsumeSource
import Leanux.Proofs.WG.Roaming.ResponseCallSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def initiationPacketPrefix (msg : List UInt8) (src : SkbSource) (underLoad : Bool) :
    M (Option InitiationCallCut) := do
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
def initiationAfterSetter (msg : List UInt8) (pid : PeerId) : M Unit := do
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

def initiationCallSuffix (msg : List UInt8) (src : SkbSource) : Option InitiationCallCut → M Unit
  | none => pure ()
  | some cut => do
    setPeerEndpointFromSkb cut.consumed.pid src
    initiationAfterSetter msg cut.consumed.pid

def initiationCallPrefix (msg : List UInt8) (src : SkbSource) : M (Option InitiationCallCut) := do
  _ ← branch .hsCookie false
  let underLoad ← responseLoad
  initiationPacketPrefix msg src underLoad

theorem initiationPacket_source (msg : List UInt8) (src : SkbSource) (underLoad : Bool)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (initiationPacketPrefix msg src underLoad >>= initiationCallSuffix msg src) =
      Index.receivePacketBody msg src underLoad := by
  simp only [initiationPacketPrefix, Index.receivePacketBody, kind,
    MESSAGE_HANDSHAKE_INITIATION, Nat.reduceBEq,
    ← initiationConsume_erase msg, initiationPeer, initiationCallSuffix, initiationAfterSetter,
    bind_assoc, pure_bind, bind_if, bind_option, invariant_bind]
  simp only [branch, bind_assoc, pure_bind, Bool.false_eq_true, ite_false, ite_true,
    Option.isNone_map]
  congr 1
  funext mac
  congr 1
  funext proceed
  cases proceed <;> simp only [Bool.false_eq_true, ite_false, ite_true, bind_assoc,
    pure_bind, bind_if, bind_option, invariant_bind]
  congr 1
  funext unit
  congr 1
  funext unit2
  congr 1
  funext consumed
  cases consumed with
  | none => simp [initiationCallSuffix]
  | some cut =>
    simp only [Option.isNone_some, Bool.false_eq_true, ite_false, Option.map_some,
      bind_assoc, pure_bind, initiationCallSuffix, initiationAfterSetter]
    congr 1

/-- Every original initiation setter path follows this successful consumer
cut; the no-cut suffix is pure. All original errors are retained. -/
theorem receiveHandshakePacket_initiation (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (initiationCallPrefix msg src >>= initiationCallSuffix msg src) = receiveHandshakePacket msg src := by
  rw [← Index.receivePacket_source]
  simp only [initiationCallPrefix, Index.receivePacketSource, kind,
    MESSAGE_HANDSHAKE_INITIATION, MESSAGE_HANDSHAKE_COOKIE, Nat.reduceBEq,
    branch, bind_assoc, pure_bind, Bool.false_eq_true, ite_false]
  rw [← responseLoad_source]
  congr 1
  funext ignored
  congr 1
  funext underLoad
  exact initiationPacket_source msg src underLoad kind

def observedInitiationHandshake (msg : List UInt8) (src : SkbSource) :
    M (Campaign2.Outcome (Option InitiationCallCut)) := do
  let observed ← Campaign2.inspect (initiationCallPrefix msg src)
  receiveHandshakePacket msg src
  pure observed

theorem observedInitiationHandshake_erase (msg : List UInt8) (src : SkbSource) :
    (do let _ ← observedInitiationHandshake msg src; pure ()) = receiveHandshakePacket msg src := by
  funext entry
  change (((receiveHandshakePacket msg src).run entry >>= fun out =>
    Except.ok (Campaign2.observeResult ((initiationCallPrefix msg src).run entry), out.2))
      >>= fun out => Except.ok ((), out.2)) = (receiveHandshakePacket msg src).run entry
  cases run : (receiveHandshakePacket msg src).run entry with
  | error err => rfl
  | ok pair => rcases pair with ⟨unit, final⟩; cases unit; rfl

def initiationCallTranscript (msg : List UInt8) (src : SkbSource) :
    M (Campaign2.Outcome (Option InitiationCallCut)) := do
  let candidate ← initiationCallPrefix msg src
  let atCut ← Campaign2.read
  initiationCallSuffix msg src candidate
  return .ok (candidate, atCut)

/-- The observation is the actual prefix result selecting the original suffix,
including exact errors; a constant-none observer cannot meet this equality. -/
theorem observedInitiationHandshake_source (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    observedInitiationHandshake msg src = initiationCallTranscript msg src := by
  funext entry
  change ((receiveHandshakePacket msg src).run entry >>= fun out =>
    Except.ok (Campaign2.observeResult ((initiationCallPrefix msg src).run entry), out.2)) = _
  rw [← receiveHandshakePacket_initiation msg src kind]
  change (((initiationCallPrefix msg src).run entry >>= fun out =>
    (initiationCallSuffix msg src out.1).run out.2) >>= fun out =>
      Except.ok (Campaign2.observeResult ((initiationCallPrefix msg src).run entry), out.2)) =
    ((initiationCallPrefix msg src).run entry >>= fun cut =>
      (initiationCallSuffix msg src cut.1).run cut.2 >>= fun out =>
        Except.ok (Except.ok (cut.1, Campaign2.snapshot cut.2), out.2))
  cases hp : (initiationCallPrefix msg src).run entry with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨candidate, atCut⟩
    cases hs : (initiationCallSuffix msg src candidate).run atCut <;> rfl

end Leanux.Proofs.WG.Roaming
