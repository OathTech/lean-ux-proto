import Leanux.Proofs.WG.Cookies.Frames
import Leanux.Proofs.WG.KeyTimes.Clock
import Leanux.Proofs.Framing.Product

/-! Source factors and exact rejection witnesses for the original handshake
receiver. The MAC2 is checked against the cookie returned by the actual first
makeCookie invocation, including its possible secret rotation. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Cookies
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing
open Leanux.Proofs.WG.CounterWindow Leanux.Proofs.WG.KeyTimes
open Leanux.Proofs.WG.Lifetimes

/-- The original queue-depth and recorded-clock load calculation. -/
def loadPhase : WG.M Bool := do
  let mut underLoad := false
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

/-- The source continuation form is native; its callback remains arbitrary. -/
private def withLoadNative (next : Bool → WG.M α) : WG.M α := do
  let mut underLoad := false
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
  next underLoad

/-- Execute the native prefix through the continuation monad's actual adapter.
For arbitrary product continuations this is the real liftWG. -/
def withLoad {m : Type → Type} [Monad m] [MonadLiftT WG.M m]
    (next : Bool → m Unit) : m Unit := do
  let loaded ← (withLoadNative pure : WG.M Bool)
  next loaded

/-- The unchanged original continuation after MAC validation. -/
def afterMac (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) : WG.M Unit := do
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
        -- either sends the staged packets or stages a keepalive and sends it
        sendKeepalive pid
      pure peer
    else pure none
  if ← branch .hsWrongPacket peer.isNone then invariant "a wrong type of packet in the handshake queue"
  let some pid := peer | invariant "unreachable"
  -- update_rx_stats: peer->rx_bytes (wg0's own rx counters,
  -- dev_sw_netstats_rx_add, are not tracked: nothing reads them on the
  -- modeled paths)
  let p ← getPeer pid
  setPeer pid { p with rxBytes := p.rxBytes + msg.length }
  -- update_rx_stats (receive.c:198): the device tstats too (W5, 2.6)
  modifyDev fun d => { d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + msg.length }
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  peerPut peer

private theorem if_bind {m : Type → Type} [Monad m]
    (p : Prop) [Decidable p] (a b : m α) (f : α → m β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl

private theorem invariant_bind (s : String) (f : α → Leanux.M β) :
    (invariant s >>= f) = (invariant s : Leanux.M β) := rfl

private theorem invariant_bind_wg (s : String) (f : α → WG.M β) :
    (invariant s >>= f) = (invariant s : WG.M β) := rfl

private theorem bind_congr {m : Type → Type} [Monad m]
    (a : m α) (f g : α → m β) (h : ∀ x, f x = g x) :
    (a >>= f) = (a >>= g) := congrArg (fun k => a >>= k) (funext h)

private theorem withLoadNative_eq (next : Bool → WG.M α) :
    withLoadNative next = (loadPhase >>= next) := by
  simp only [withLoadNative, loadPhase, bind_assoc, pure_bind, if_bind, invariant_bind_wg]
  repeat' first | rfl | (apply bind_congr; intro x) | split
  all_goals simp only [bind_assoc, pure_bind, if_bind, invariant_bind_wg]

theorem withLoad_eq {m : Type → Type} [Monad m] [MonadLiftT WG.M m]
    (next : Bool → m Unit) :
    withLoad next = ((liftM loadPhase : m Bool) >>= next) := by
  simp only [withLoad, withLoadNative_eq, bind_pure]

theorem receive_factor (msg : List UInt8) (src : SkbSource) :
    receiveHandshakePacket msg src = (do
      if ← branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE) then
        cookieMessageConsume msg
        return
      let loaded ← loadPhase
      let mac ← cookieValidatePacket msg src loaded
      afterMac msg src loaded mac) := by
  change (do
    if ← branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE) then
      cookieMessageConsume msg
      return
    withLoadNative fun loaded => do
      let mac ← cookieValidatePacket msg src loaded
      afterMac msg src loaded mac) = _
  rw [withLoadNative_eq]

def replyEntry (a : Ambient) : Ambient :=
  record (record (record (record (record (record (record a
    .hsLoadedOperand true) .hsLoadedCookieOk false) .hsNotLoaded false)
    .hsNeedsCookieLoaded true) .hsNeedsCookieMac true)
    .hsSwitchInitiation true) .hsInitNeedsCookie true

/-- The exact original rejection suffix contains only the cookie reply; the
Noise consume/create continuation is not reached. This includes reply Stops. -/
theorem afterMac_noCookie (msg : List UInt8) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (ht : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    ((afterMac msg src true .noCookie).run w).run a =
      ((sendHandshakeCookie msg src).run w).run (replyEntry a) := by
  have hc : (MacState.noCookie == MacState.withCookie) = false := rfl
  have hn : (MacState.noCookie == MacState.noCookie) = true := rfl
  simp [afterMac, hc, hn, WG.orM, WG.andM, StateT.run_bind, branch, branch_run, ht,
    MESSAGE_HANDSHAKE_INITIATION, replyEntry]

theorem loadPhase_sameStore : SameWGStore loadPhase := by
  apply SameView.of_wp
  intro initial
  have hc : Hoare (hiddenClock64 .underLoadNow : WG.M Int64)
      (fun w => wgStoreView w = initial) (fun _ w => wgStoreView w = initial) :=
    hoare_liftAmbient (AmbientM.hiddenClock64 .underLoadNow) _
  have hb := fun t => ((birthdateTest_sameWGWorld t 1).factor wgStoreView).wp
    (fun s => s = initial)
  unfold Hoare at hc
  mvcgen [loadPhase, hc, hb, getDev, branch, branchCmp, invariant,
    AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant]

def mac1Given (msg : List UInt8) := (msg.drop (msg.length - 32)).take 16
def mac1Computed (d : Device) (msg : List UInt8) :=
  blake2s 16 d.mac1Key (msg.take (msg.length - 32))
def mac2Given (msg : List UInt8) := (msg.drop (msg.length - 16)).take 16

/-- A witness to the actual load and make_cookie runs. Both state layers are
carried continuously; MAC2 failure compares against the cookie actually returned. -/
structure FailedMac2 (msg : List UInt8) (src : SkbSource) (w : WGWorld) (a : Ambient) where
  loaded : WGWorld
  loadedAmbient : Ambient
  device : Device
  made : WGWorld
  madeAmbient : Ambient
  cookie : List UInt8
  loadRun : (loadPhase.run w).run (record a .hsCookie false) =
    .ok ((true, loaded), loadedAmbient)
  devicePresent : loaded.dev = some device
  mac1Valid : mac1Computed device msg = mac1Given msg
  cookieRun : ((makeCookie src).run loaded).run
    (record (record loadedAmbient .macInvalid false) .macNoCookieCheck false) =
      .ok ((cookie, made), madeAmbient)
  mac2Invalid : blake2s 16 cookie (msg.take (msg.length - 16)) ≠ mac2Given msg

def FailedMac2.checked (h : FailedMac2 msg src w a) : Ambient :=
  record h.madeAmbient .macCookieInvalid true

theorem FailedMac2.validate (h : FailedMac2 msg src w a) :
    ((cookieValidatePacket msg src true).run h.loaded).run h.loadedAmbient =
      .ok ((.noCookie, h.made), h.checked) := by
  have hg (ambient : Ambient) : (getDev.run h.loaded).run ambient =
      .ok ((h.device, h.loaded), ambient) := by
    simp [getDev, h.devicePresent]
  have hm1 := h.mac1Valid
  have hm2 := h.mac2Invalid
  simp only [mac1Computed, mac1Given] at hm1
  simp only [mac2Given] at hm2
  have hb : (blake2s 16 h.cookie (msg.take (msg.length - 16)) != (msg.drop (msg.length - 16)).take 16) = true := by
    simpa only [bne_iff_ne] using hm2
  simp [cookieValidatePacket, StateT.run_bind, hg, branch, branch_run, hm1,
    h.cookieRun, hm2, hb, FailedMac2.checked]

/-- Whole original result equality, including a possible later reply failure. -/
theorem receive_rejected_run (msg : List UInt8) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (ht : messageType msg = MESSAGE_HANDSHAKE_INITIATION) (h : FailedMac2 msg src w a) :
    ((receiveHandshakePacket msg src).run w).run a =
      ((sendHandshakeCookie msg src).run h.made).run (replyEntry h.checked) := by
  rw [receive_factor]
  simp only [StateT.run_bind, ht, MESSAGE_HANDSHAKE_INITIATION, MESSAGE_HANDSHAKE_COOKIE,
    Nat.reduceBEq, branch, StateT.run_monadLift, StateT.run_pure, monadLift_self, branch_run,
    except_ok_bind, pure_bind, Bool.false_eq_true, ↓reduceIte, h.loadRun, h.validate]
  exact afterMac_noCookie msg src h.made h.checked ht

theorem receive_rejected_frame (msg : List UInt8) (src : SkbSource) (w v : WGWorld)
    (a b : Ambient) (ht : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (h : FailedMac2 msg src w a)
    (hr : ((receiveHandshakePacket msg src).run w).run a = .ok (((), v), b)) :
    noiseView v = noiseView w := by
  rw [receive_rejected_run msg src w a ht h] at hr
  have hs : noiseView v = noiseView h.made :=
    (ProjectedAction.iff_run_ambient _ _ _).mp (sendHandshakeCookie_frame msg src)
      h.made (replyEntry h.checked) () v b hr
  have hc : noiseView h.made = noiseView h.loaded :=
    (ProjectedAction.iff_run_ambient _ _ _).mp (makeCookie_frame src)
      h.loaded _ h.cookie h.made h.madeAmbient h.cookieRun
  have hl : wgStoreView h.loaded = wgStoreView w :=
    (ProjectedAction.iff_run_ambient _ _ _).mp loadPhase_sameStore
      w _ true h.loaded h.loadedAmbient h.loadRun
  exact hs.trans (hc.trans (congrArg viewOfStore hl))

/-- The source's under-load invalid-MAC drop records, before any type dispatch. -/
def dropEntry (a : Ambient) : Ambient :=
  record (record (record (record (record a .hsLoadedOperand true)
    .hsLoadedCookieOk false) .hsNotLoaded false) .hsNeedsCookieLoaded true)
    .hsNeedsCookieMac false

theorem afterMac_invalid (msg : List UInt8) (src : SkbSource) (w : WGWorld) (a : Ambient) :
    ((afterMac msg src true .invalid).run w).run a = .ok (((), w), dropEntry a) := by
  have hc : (MacState.invalid == MacState.withCookie) = false := rfl
  have hn : (MacState.invalid == MacState.noCookie) = false := rfl
  simp [afterMac, hc, hn, WG.orM, WG.andM, StateT.run_bind, branch, branch_run, dropEntry]

/-- Invalid MAC1 is rejected before make_cookie, independently of MAC2. -/
theorem receive_bad_mac1 (msg : List UInt8) (src : SkbSource) (w u : WGWorld)
    (a b : Ambient) (d : Device)
    (ht : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (hl : (loadPhase.run w).run (record a .hsCookie false) = .ok ((true, u), b))
    (hd : u.dev = some d) (hm : mac1Computed d msg ≠ mac1Given msg) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((), u), dropEntry (record b .macInvalid true)) := by
  have hg (ambient : Ambient) : (getDev.run u).run ambient = .ok ((d, u), ambient) := by
    simp [getDev, hd]
  have hb : (blake2s 16 d.mac1Key (msg.take (msg.length - 32)) !=
      (msg.drop (msg.length - 32)).take 16) = true := by
    simpa only [bne_iff_ne, mac1Computed, mac1Given] using hm
  have hv : ((cookieValidatePacket msg src true).run u).run b =
      .ok ((.invalid, u), record b .macInvalid true) := by
    have hm' := hm
    simp only [mac1Computed, mac1Given] at hm'
    simp [cookieValidatePacket, StateT.run_bind, hg, branch, branch_run, hb, hm']
  rw [receive_factor]
  simp only [StateT.run_bind, ht, MESSAGE_HANDSHAKE_INITIATION, MESSAGE_HANDSHAKE_COOKIE,
    Nat.reduceBEq, branch, StateT.run_monadLift, StateT.run_pure, monadLift_self, branch_run,
    except_ok_bind, pure_bind, Bool.false_eq_true, ↓reduceIte, hl, hv]
  exact afterMac_invalid msg src u (record b .macInvalid true)

theorem receive_bad_mac1_frame (msg : List UInt8) (src : SkbSource) (w u v : WGWorld)
    (a b c : Ambient) (d : Device)
    (ht : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (hl : (loadPhase.run w).run (record a .hsCookie false) = .ok ((true, u), b))
    (hd : u.dev = some d) (hm : mac1Computed d msg ≠ mac1Given msg)
    (hr : ((receiveHandshakePacket msg src).run w).run a = .ok (((), v), c)) :
    noiseView v = noiseView w := by
  rw [receive_bad_mac1 msg src w u a b d ht hl hd hm] at hr
  cases hr
  have hs : wgStoreView u = wgStoreView w :=
    (ProjectedAction.iff_run_ambient _ _ _).mp loadPhase_sameStore w _ true u b hl
  exact congrArg viewOfStore hs

end Leanux.Proofs.WG.Cookies
