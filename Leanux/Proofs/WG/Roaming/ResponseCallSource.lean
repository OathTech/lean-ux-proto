import Leanux.Proofs.WG.Roaming.ResponseLookupSource
import Leanux.Proofs.WG.Index.ReceiveOperations

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def responseLoad : M Bool := do
  -- `under_load = handshake_queue_len >= MAX_QUEUED_INCOMING_HANDSHAKES / 8`
  -- (receive.c:112): the counter, which a `wg_flood`'s batch has filled before
  -- the worker runs (E-B v2, the queue-depth design).
  let mut underLoad := false
  -- the compare's operands: the counter (an int) against the constant 512,
  -- compiled `> 511`, which the check's `ge` shift absorbs (declared 2026-10-14)
  let queueLen := (← getDev).handshakeQueueLen
  if ← branchCmp .hsUnderLoad (queueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8)
        (Int.ofNat queueLen) (Int.ofNat (MAX_QUEUED_INCOMING_HANDSHAKES / 8)) then
    -- `last_under_load = ktime_get_coarse_boottime_ns()` (receive.c:115)
    let now ← hiddenClock64 .underLoadNow
    modify fun w => { w with lastUnderLoad := some now }
    underLoad := true
  -- `else if (last_under_load)`: the function-static (receive.c:100), nonzero
  -- after a flood this trace ran (every normal trace keeps it `none`, §4.2).
  else if ← branch .hsWasUnderLoad (← get).lastUnderLoad.isSome then
    let some last := (← get).lastUnderLoad | invariant "unreachable"
    -- `under_load = !wg_birthdate_has_expired(last_under_load, 1)` (receive.c:117),
    -- the recorded clock against the saved time; `if (!under_load)
    -- last_under_load = 0` (receive.c:118-119): the decay's reset
    let (expired, lhs, now) ← birthdateTest last 1
    underLoad := !expired
    -- the age test's operands are recorded at receive.c:117 (`Decision.comparison`'s site)
    if ← branchCmp .hsDecayExpired expired lhs now then
      modify fun w => { w with lastUnderLoad := none }
  return underLoad


/-- A return-valued presentation of the existing exact load continuation. -/
theorem responseLoad_source (next : Bool → M Unit) :
    (responseLoad >>= next) = Index.receiveLoadThen next := by
  simp only [responseLoad, Index.receiveLoadThen, bind_assoc, pure_bind,
    bind_if, bind_option, invariant_bind]
  congr 1
  funext d
  congr 1
  funext loaded
  cases loaded <;> simp only [Bool.false_eq_true, ite_false, ite_true, bind_assoc, pure_bind]
  all_goals try rfl
  congr 1
  funext w
  congr 1
  funext wasLoaded
  cases wasLoaded <;> simp only [Bool.false_eq_true, ite_false, ite_true, bind_assoc, pure_bind]
  all_goals try rfl
  congr 1
  funext w
  cases w.lastUnderLoad with
  | none => rfl
  | some last =>
    simp only [bind_assoc, pure_bind]
    congr 1
    funext test
    rcases test with ⟨expired, lhs, now⟩
    congr 1
    funext changed
    cases changed <;> simp [bind_assoc]

def responsePacketPrefix (msg : List UInt8) (src : SkbSource) (underLoad : Bool) :
    M (Option ResponseCallCut) := do
  let mac ← cookieValidatePacket msg src underLoad
  let proceed ← WG.orM (WG.andM (branch .hsLoadedOperand underLoad)
      (branch .hsLoadedCookieOk (mac == .withCookie)))
    (WG.andM (branch .hsNotLoaded (!underLoad)) (branch .hsMacNoCookie (mac == .noCookie)))
  let needsCookie ← do
    if proceed then pure false
    else if ← WG.andM (branch .hsNeedsCookieLoaded underLoad)
        (branch .hsNeedsCookieMac (mac == .noCookie)) then pure true
    else return none
  _ ← branch .hsSwitchInitiation false
  _ ← branch .hsSwitchResponse true
  if ← branch .hsRespNeedsCookie needsCookie then
    sendHandshakeCookie msg src
    return none
  let consumed ← responseWithLookup msg
  if ← branch .hsRespNoPeer consumed.isNone then return none
  let some pair := consumed | invariant "unreachable"
  return some ⟨underLoad, mac, pair.1, pair.2, ← Campaign2.read⟩

/-- Exactly the original response continuation after its endpoint setter.
Session installation, keepalive, statistics, timers and final release remain. -/
def responseAfterSetter (msg : List UInt8) (pid : PeerId) : M Unit := do
  if ← branch .hsRespSessionBegun (← beginSession pid) then
    timersSessionDerived pid
    timersHandshakeComplete pid
    sendKeepalive pid
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

/-- There is no setter in the no-cut suffix; a cut invokes the original setter
immediately, before the full original continuation. -/
def responseCallSuffix (msg : List UInt8) (src : SkbSource) : Option ResponseCallCut → M Unit
  | none => pure ()
  | some cut => do
    setPeerEndpointFromSkb cut.consumed.input.pid src
    responseAfterSetter msg cut.consumed.input.pid

def responseCallPrefix (msg : List UInt8) (src : SkbSource) : M (Option ResponseCallCut) := do
  _ ← branch .hsCookie false
  let underLoad ← responseLoad
  responsePacketPrefix msg src underLoad

/-- This observer executes the unrestricted original caller. Its response-only
source correspondence is stated separately; discarding observations is unconditional. -/
def observedResponseHandshake (msg : List UInt8) (src : SkbSource) :
    M (Campaign2.Outcome (Option ResponseCallCut)) := do
  let observed ← Campaign2.inspect (responseCallPrefix msg src)
  receiveHandshakePacket msg src
  pure observed

theorem observedResponseHandshake_erase (msg : List UInt8) (src : SkbSource) :
    (do let _ ← observedResponseHandshake msg src; pure ()) = receiveHandshakePacket msg src := by
  funext w
  change (((receiveHandshakePacket msg src).run w >>= fun out =>
    Except.ok (Campaign2.observeResult ((responseCallPrefix msg src).run w), out.2))
      >>= fun out => Except.ok ((), out.2)) = (receiveHandshakePacket msg src).run w
  cases run : (receiveHandshakePacket msg src).run w with
  | error e => rfl
  | ok pair => rcases pair with ⟨unit, final⟩; cases unit; rfl

/-- Exact original response-body factor. A none cut performs no setter; every
setter path passes the successful consumer cut and starts the unchanged suffix. -/
theorem responsePacket_source (msg : List UInt8) (src : SkbSource) (underLoad : Bool)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (responsePacketPrefix msg src underLoad >>= responseCallSuffix msg src) =
      Index.receivePacketBody msg src underLoad := by
  simp only [responsePacketPrefix, Index.receivePacketBody, kind,
    MESSAGE_HANDSHAKE_RESPONSE, MESSAGE_HANDSHAKE_INITIATION, Nat.reduceBEq,
    ← responseWithLookup_erase msg, responseCallSuffix, responseAfterSetter,
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
  funext unit
  congr 1
  funext unit
  congr 1
  funext consumed
  cases consumed with
  | none => simp [responseCallSuffix]
  | some pair =>
    simp only [Option.isNone_some, Bool.false_eq_true, ite_false, Option.map_some,
      bind_assoc, pure_bind, responseCallSuffix, responseAfterSetter]
    congr 1

/-- Exact response-kind correspondence, including errors. The no-cut suffix
is pure; the some-cut suffix begins with precisely the original endpoint setter. -/
theorem receiveHandshakePacket_response (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (responseCallPrefix msg src >>= responseCallSuffix msg src) = receiveHandshakePacket msg src := by
  rw [← Index.receivePacket_source]
  simp only [responseCallPrefix, Index.receivePacketSource, kind,
    MESSAGE_HANDSHAKE_RESPONSE, MESSAGE_HANDSHAKE_COOKIE, Nat.reduceBEq,
    branch, bind_assoc, pure_bind, Bool.false_eq_true, ite_false]
  rw [← responseLoad_source]
  congr 1
  funext ignored
  congr 1
  funext underLoad
  exact responsePacket_source msg src underLoad kind

/-- The recorded cut comes from the very prefix whose result selects the
actual continuation, rather than from an independently related run. -/
def responseCallTranscript (msg : List UInt8) (src : SkbSource) :
    M (Campaign2.Outcome (Option ResponseCallCut)) := do
  let candidate ← responseCallPrefix msg src
  let atCut ← Campaign2.read
  responseCallSuffix msg src candidate
  return .ok (candidate, atCut)

/-- Completeness of the observation itself as well as of the original caller.
A constant-none observer would not satisfy this equality. Errors remain exact. -/
theorem observedResponseHandshake_source (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    observedResponseHandshake msg src = responseCallTranscript msg src := by
  funext w
  change ((receiveHandshakePacket msg src).run w >>= fun out =>
    Except.ok (Campaign2.observeResult ((responseCallPrefix msg src).run w), out.2)) = _
  rw [← receiveHandshakePacket_response msg src kind]
  change (((responseCallPrefix msg src).run w >>= fun out =>
    (responseCallSuffix msg src out.1).run out.2) >>= fun out =>
      Except.ok (Campaign2.observeResult ((responseCallPrefix msg src).run w), out.2)) =
    ((responseCallPrefix msg src).run w >>= fun cut =>
      (responseCallSuffix msg src cut.1).run cut.2 >>= fun out =>
        Except.ok (Except.ok (cut.1, Campaign2.snapshot cut.2), out.2))
  cases hp : (responseCallPrefix msg src).run w with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨candidate, atCut⟩
    cases hs : (responseCallSuffix msg src candidate).run atCut <;> rfl

end Leanux.Proofs.WG.Roaming
