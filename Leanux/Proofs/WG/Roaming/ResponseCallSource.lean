import Leanux.Proofs.WG.Roaming.HandshakeEndpointSource
import Leanux.Proofs.WG.Roaming.ResponseLookupSource
import Leanux.Proofs.WG.Index.ReceiveOperations

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
open Origins HandshakeEndpoint

def responseLoad : WG.M Bool := do
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
theorem responseLoad_source (next : Bool → WG.M Unit) :
    (responseLoad >>= next) = Index.receiveLoadThen next := by
  have bind_if {α β : Type} (condition : Prop) [Decidable condition]
      (yes no : WG.M α) (next : α → WG.M β) :
      ((if condition then yes else no) >>= next) =
        if condition then yes >>= next else no >>= next := by split <;> rfl
  have invariant_bind {α β : Type} (message : String) (next : α → WG.M β) :
      ((invariant message : WG.M α) >>= next) = (invariant message : WG.M β) := rfl

  simp only [responseLoad, Index.receiveLoadThen, bind_assoc, pure_bind,
    bind_if, invariant_bind]
  congr 1
  funext d
  congr 1
  funext loaded
  cases loaded <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  congr 1
  funext w
  congr 1
  funext wasLoaded
  cases wasLoaded <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  congr 1
  funext w
  cases w.lastUnderLoad with
  | none => rfl
  | some last =>
    simp only [bind_assoc]
    congr 1
    funext test
    rcases test with ⟨expired, lhs, now⟩
    congr 1
    funext changed
    cases changed <;> simp

def responsePacketPrefix (msg : List UInt8) (src : SkbSource) (underLoad : Bool) :
    WG.M (Option ResponseCallCut) := do
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
def responseAfterSetter (msg : List UInt8) (pid : PeerId) : WG.M Unit := do
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
def responseCallSuffix (msg : List UInt8) (src : SkbSource) : Option ResponseCallCut → WG.M Unit
  | none => pure ()
  | some cut => do
    setPeerEndpointFromSkb cut.consumed.input.pid src
    responseAfterSetter msg cut.consumed.input.pid

def responseCallPrefix (msg : List UInt8) (src : SkbSource) : WG.M (Option ResponseCallCut) := do
  _ ← branch .hsCookie false
  let underLoad ← responseLoad
  responsePacketPrefix msg src underLoad

/-- This observer executes the unrestricted original caller. Its response-only
source correspondence is stated separately; discarding observations is unconditional. -/
def observedResponseHandshake (msg : List UInt8) (src : SkbSource) :
    WG.M (Campaign2.Outcome (Option ResponseCallCut)) := do
  let observed ← Campaign2.inspect (responseCallPrefix msg src)
  receiveHandshakePacket msg src
  pure observed

theorem observedResponseHandshake_erase (msg : List UInt8) (src : SkbSource) :
    (do let _ ← observedResponseHandshake msg src; pure ()) = receiveHandshakePacket msg src := by
  funext g ambient
  change ((((receiveHandshakePacket msg src).run g).run ambient >>= fun ((_, current), after) =>
    Except.ok ((Campaign2.observeResult (((responseCallPrefix msg src).run g).run ambient), current), after))
      >>= fun ((_, current), after) => Except.ok (((), current), after)) =
        ((receiveHandshakePacket msg src).run g).run ambient
  cases run : ((receiveHandshakePacket msg src).run g).run ambient with
  | error e => rfl
  | ok pair => rcases pair with ⟨⟨value, final⟩, after⟩; cases value; rfl

section EndpointContext
open Leanux.Proofs.Logged Origins HandshakeEndpoint
variable {m : Type → Type} [Monad m] (L : HandshakeEndpoint.Lift m)

theorem responseLoad_context_source : responseLoad = Cookies.loadPhase := rfl

def responseSuffixWith (endpoint : PeerId → SkbSource → m Unit)
    (msg : List UInt8) (src : SkbSource) : Option ResponseCallCut → m Unit
  | none => pure ()
  | some cut => do
    endpoint cut.consumed.input.pid src
    L.action (responseAfterSetter msg cut.consumed.input.pid)

theorem responsePacket_context [LawfulMonad m] (endpoint : PeerId → SkbSource → m Unit)
    (msg : List UInt8) (src : SkbSource) (underLoad : Bool)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (L.action (responsePacketPrefix msg src underLoad) >>=
      responseSuffixWith L endpoint msg src) =
    (do let mac ← L.action (cookieValidatePacket msg src underLoad)
        HandshakeSources.afterMacWith (ops L endpoint) msg src underLoad mac) := by
  simp only [HandshakeSources.afterMacWith]
  simp only [response_source]
  simp only [responsePacketPrefix, kind,
    MESSAGE_HANDSHAKE_RESPONSE, MESSAGE_HANDSHAKE_INITIATION, Nat.reduceBEq,
    ops_step, ops_initiation, ops_response, ops_endpoint, ops_cookie, ops_session, ops_derived, ops_complete, ops_keepalive, ops_modifyPeer, ops_received, ops_traversal, ops_put, ← responseWithLookup_erase msg,
    lift_bind, lift_pure, responseSuffixWith, bind_assoc, pure_bind, bind_if, abort_bind, apply_ite]
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
  intro ignored
  apply bind_congr_right
  intro unit2
  apply bind_congr_right
  intro consumed
  cases consumed with
  | none => simp
  | some pair =>
    simp only [Option.isNone_some, Bool.false_eq_true, ite_false, Option.map_some,
      lift_bind, lift_pure, bind_assoc, pure_bind, responseSuffixWith, responseAfterSetter,
      read_ignore, branch_native, apply_ite]
    congr 1

theorem response_context [LawfulMonad m] (endpoint : PeerId → SkbSource → m Unit)
    (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (L.action (responseCallPrefix msg src) >>= responseSuffixWith L endpoint msg src) =
      HandshakeSources.receptionWith (ops L endpoint) msg src := by
  simp only [responseCallPrefix, HandshakeSources.receptionWith, kind,
    MESSAGE_HANDSHAKE_RESPONSE, MESSAGE_HANDSHAKE_COOKIE, Nat.reduceBEq,
    ops_step, branch_native, lift_bind, lift_pure, bind_assoc, pure_bind,
    Bool.false_eq_true, ite_false]
  rw [responseLoad_context_source]
  apply bind_congr_right
  intro ignored
  apply bind_congr_right
  intro loaded
  exact responsePacket_context L endpoint msg src loaded kind


theorem response_prefix_context {E : Type}
    (endpoint : PeerId → SkbSource → WGPrefix E Unit)
    (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (liftWGPrefix (responseCallPrefix msg src) >>= responseSuffixWith prefixLift endpoint msg src) =
      HandshakeSources.receptionWith (ops prefixLift endpoint) msg src :=
  response_context prefixLift endpoint msg src kind
end EndpointContext

/-- Exact original response-body factor. A none cut performs no setter; every
setter path passes the successful consumer cut and starts the unchanged suffix. -/
theorem responsePacket_source (msg : List UInt8) (src : SkbSource) (underLoad : Bool)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (responsePacketPrefix msg src underLoad >>= responseCallSuffix msg src) =
      Index.receivePacketBody msg src underLoad := by
  have context := responsePacket_context native setPeerEndpointFromSkb msg src underLoad kind
  change (responsePacketPrefix msg src underLoad >>= responseCallSuffix msg src) =
    (cookieValidatePacket msg src underLoad >>= fun mac =>
      HandshakeSources.afterMacWith HandshakeSources.original msg src underLoad mac) at context
  rw [packet_original]
  simpa only [HandshakeSources.afterMac_original] using context


/-- Exact response-kind correspondence, including errors. The no-cut suffix
is pure; the some-cut suffix begins with precisely the original endpoint setter. -/
theorem receiveHandshakePacket_response (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (responseCallPrefix msg src >>= responseCallSuffix msg src) = receiveHandshakePacket msg src := by
  have branch_native (decision : Decision) (value : Bool) :
      (branch decision value : WG.M Bool) = (do
        (monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
          decision, outcome := value, netRx := a.netRxSection}} : AmbientM Unit) : WG.M Unit)
        pure value) := rfl

  rw [← Index.receivePacket_source]
  simp only [responseCallPrefix, Index.receivePacketSource, kind,
    MESSAGE_HANDSHAKE_RESPONSE, MESSAGE_HANDSHAKE_COOKIE, Nat.reduceBEq,
    branch_native, bind_assoc, pure_bind, Bool.false_eq_true, ite_false]
  rw [← responseLoad_source]
  congr 1
  funext ignored
  congr 1
  funext underLoad
  exact responsePacket_source msg src underLoad kind

/-- The recorded cut comes from the very prefix whose result selects the
actual continuation, rather than from an independently related run. -/
def responseCallTranscript (msg : List UInt8) (src : SkbSource) :
    WG.M (Campaign2.Outcome (Option ResponseCallCut)) := do
  let candidate ← responseCallPrefix msg src
  let atCut ← Campaign2.read
  responseCallSuffix msg src candidate
  return .ok (candidate, atCut)

/-- Completeness of the observation itself as well as of the original caller.
A constant-none observer would not satisfy this equality. Errors remain exact. -/
theorem observedResponseHandshake_source (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    observedResponseHandshake msg src = responseCallTranscript msg src := by
  funext g ambient
  change (((receiveHandshakePacket msg src).run g).run ambient >>= fun ((_, current), after) =>
    Except.ok ((Campaign2.observeResult (((responseCallPrefix msg src).run g).run ambient), current), after)) = _
  rw [← receiveHandshakePacket_response msg src kind]
  change ((((responseCallPrefix msg src).run g).run ambient >>= fun ((out, current), after) =>
    ((responseCallSuffix msg src out).run current).run after) >>= fun ((_, current), after) =>
      Except.ok ((Campaign2.observeResult (((responseCallPrefix msg src).run g).run ambient), current), after)) =
    (((responseCallPrefix msg src).run g).run ambient >>= fun ((cut, atCut), cutAmbient) =>
      ((responseCallSuffix msg src cut).run atCut).run cutAmbient >>= fun ((_, current), after) =>
        Except.ok ((Except.ok (cut, Campaign2.snapshot atCut cutAmbient), current), after))
  cases hp : ((responseCallPrefix msg src).run g).run ambient with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨⟨candidate, atCut⟩, cutAmbient⟩
    cases hs : ((responseCallSuffix msg src candidate).run atCut).run cutAmbient <;> rfl


end Leanux.Proofs.WG.Roaming
