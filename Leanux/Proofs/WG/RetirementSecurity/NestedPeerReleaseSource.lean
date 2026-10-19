import Leanux.Proofs.WG.AuthenticatedEffects.ResponseAcceptanceSource
import Leanux.Proofs.WG.AuthenticatedEffects.CookieRefusal
import Leanux.Proofs.WG.Queues.RxCleanupProtection

/-! Literal consumer, clear-worker and RX-cleanup sources with the nested
peer-reference repayment exposed. Acceptance still precedes protocol writes;
a later Stop does not move a repayment or its disposal cut. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
open Queues.RxCredits.HandshakeLoans

structure Ops (m : Type → Type) where
  step : {α : Type} → WG.M α → m α
  release : Option PeerId → m Unit

def native : Ops WG.M := ⟨fun a => a, peerPut⟩
def lifted : Ops (WGPrefix E) := ⟨liftWGPrefix, fun p => liftWGPrefix (peerPut p)⟩

variable {m : Type → Type} [Monad m]

def initiationOutWith (o : Ops m) (peer ret : Option PeerId) : m (Option PeerId) := do
  if ← o.step (branch .consumeFailedPut ret.isNone) then o.release peer
  return ret

def initiationTailWith (o : Ops m) (msg e ck hash : Key) (peer : Option PeerId)
    (pid : PeerId) : m (Option AcceptedInitiation) := do
  let failed : m (Option AcceptedInitiation) := do
    let _ ← initiationOutWith o peer none
    return none
  let p0 ← o.step (getPeer pid)
  let ss ← o.step (mixPrecomputedDh ck p0.precomputedStaticStatic)
  if ← o.step (branch .consumeSsFailed ss.isNone) then return ← failed
  let some (ckSs,key) := ss | o.step (invariant "unreachable")
  let ts ← o.step (messageDecrypt ((msg.drop 88).take 28) key hash)
  if ← o.step (branch .consumeTimestampFailed ts.isNone) then return ← failed
  let some (t,hashT) := ts | o.step (invariant "unreachable")
  let p ← o.step (getPeer pid)
  let replay := memcmp t p.latestTimestamp != .gt
  let floodLhs : Int64 := p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64
  let now ← o.step (hiddenClock64 .floodNow)
  if ← o.step (WG.orM (branch .consumeReplay replay)
      (branchCmp .consumeFlood (floodLhs > now) floodLhs.toInt now.toInt)) then
    return ← failed
  return some ⟨pid,peer,e,ckSs,hashT,t,p.latestTimestamp⟩

def initiationCheckWith (o : Ops m) (msg : Key) : m (Option AcceptedInitiation) := do
  let failed : m (Option AcceptedInitiation) := do
    let _ ← initiationOutWith o none none
    return none
  match ← o.step (initiationAuthFront msg) with
  | none => failed
  | some (e,ck,s,hash) =>
    let peer ← o.step (pubkeyLookup s)
    if ← o.step (branch .consumeNoPeer peer.isNone) then return ← failed
    let some pid := peer | o.step (invariant "unreachable")
    initiationTailWith o msg e ck hash peer pid

def responseTailWith (o : Ops m) (msg : Key) (identity : StaticIdentity)
    (pid : PeerId) : m (Option AcceptedResponse) := do
  let fail : m (Option AcceptedResponse) := do
    o.release (some pid)
    return none
  let p ← o.step (getPeer pid)
  let state := p.handshakeState
  if ← o.step (branch .crespNotCreatedInitiation (state != HANDSHAKE_CREATED_INITIATION)) then return ← fail
  let eph := (msg.drop 12).take 32
  let (ck,h) ← o.step (messageEphemeral true eph p.chainingKey p.hash)
  let ee ← o.step (mixDh false ck p.ephemeralPrivate eph)
  if ← o.step (branch .crespEeFailed ee.isNone) then return ← fail
  let some (ck,_) := ee | o.step (invariant "unreachable")
  let se ← o.step (mixDh false ck identity.staticPrivate eph)
  if ← o.step (branch .crespSeFailed se.isNone) then return ← fail
  let some (ck,_) := se | o.step (invariant "unreachable")
  let outs ← o.step (kdf true true ck p.presharedKey)
  let (ck,tempHash,key) := (← o.step (kdfOut outs 0),← o.step (kdfOut outs 1),← o.step (kdfOut outs 2))
  let h := noiseHash (h ++ tempHash)
  let dec ← o.step (messageDecrypt ((msg.drop 44).take 16) key h)
  if ← o.step (branch .crespDecryptFailed dec.isNone) then return ← fail
  let some (_,h) := dec | o.step (invariant "unreachable")
  let current ← o.step (getPeer pid)
  if ← o.step (branch .crespStateChanged (current.handshakeState != state)) then return ← fail
  return some ⟨pid,eph,h,ck⟩

def responseCheckWith (o : Ops m) (msg : Key) : m (Option AcceptedResponse) := do
  let identity := (← o.step getDev).staticIdentity
  if ← o.step (branch .crespNoIdentity !identity.hasIdentity) then return none
  let entry ← o.step (indexLookup [.handshake] (u32le msg 8))
  if ← o.step (branch .crespNoHandshake entry.isNone) then return none
  let some (IndexOwner.handshake _,pid) := entry |
    o.step (invariant "a keypair entry under the handshake mask")
  responseTailWith o msg identity pid

def cookieAfterWith (o : Ops m) (pid : PeerId) (cookie : Option Key) : m Unit := do
  if let some c := cookie then
    let birthdate ← o.step (hiddenClock64 .cookieBirthdate)
    let p ← o.step (getPeer pid)
    o.step (setPeer pid {p with cookie := c, cookieBirthdate := birthdate, cookieIsValid := true, haveSentMac1 := false})
  o.release (some pid)

def cookieWith (o : Ops m) (msg : Key) : m Unit := do
  let entry ← o.step (indexLookup [.handshake,.keypair] (u32le msg 4))
  if ← o.step (branch .cookieLookupMiss entry.isNone) then return
  let some (_,pid) := entry | o.step (invariant "unreachable")
  let cookie ← o.step (cookieAuthFront msg pid)
  cookieAfterWith o pid cookie

def clearWith (o : Ops m) (pid : PeerId) : m Unit := do
  o.step (handshakeClear pid)
  o.step (keypairsClear pid)
  o.release (some pid)

def flushedClearWith (o : Ops m) (pid : PeerId) : m Unit := do
  o.step (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
  _ ← o.step (hidden (.sectionStart .clearPeerWorker))
  clearWith o pid
  _ ← o.step (hidden (.sectionStop .clearPeerWorker))

def cleanupWith (o : Ops m) (id : SkbId) (pkt : RxPacket) (flag : Bool) : m Unit := do
  o.step (keypairPut (some pkt.keypair) false)
  o.release (some pkt.peer)
  _ ← o.step (branch .rxPollFree flag)
  o.step (freeRxSkb id)

theorem initiationOut_native (peer ret : Option PeerId) :
    initiationOutWith native peer ret = initiationOut peer ret := rfl

theorem initiationTail_native (msg e ck hash : Key) (peer : Option PeerId) (pid : PeerId) :
    initiationTailWith native msg e ck hash peer pid = initiationTailCheck msg e ck hash peer pid := rfl

theorem initiationCheck_native (msg : Key) :
    initiationCheckWith native msg = initiationAcceptedCheck msg := rfl

theorem responseTail_native (msg : Key) (identity : StaticIdentity) (pid : PeerId) :
    responseTailWith native msg identity pid = responseTailCheck msg identity pid := rfl

theorem responseCheck_native (msg : Key) :
    responseCheckWith native msg = responseAcceptedCheck msg := rfl

theorem cookieAfter_native (pid : PeerId) (cookie : Option Key) :
    cookieAfterWith native pid cookie = cookieAfterAuth pid cookie := rfl

theorem cookie_native (msg : Key) : cookieWith native msg = cookieMessageConsume msg := by
  rw [cookieAuthFront_factor]
  rfl

theorem clear_native (pid : PeerId) :
    clearWith native pid = queuedExpiredZeroKeyMaterial pid := rfl

theorem flushedClear_native (pid : PeerId) :
    flushedClearWith native pid = runFlushedClearWork pid := rfl

theorem cleanup_native (id : SkbId) (pkt : RxPacket) (flag : Bool) :
    cleanupWith native id pkt flag = Queues.RxCredits.cleanup id pkt flag := rfl

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
