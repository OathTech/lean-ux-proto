import Leanux.Proofs.WG.HandshakeSecurity.StaleInitiationInitialized

/-! The original initiation handler's exact continuation at consumer return.
This exposes no-response directly at an initialized receipt's after-state,
without asking the caller to reconstruct the preceding MAC ambient. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StaleInitiation
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects Cookies CounterWindow

def afterConsumer (msg : Key) (src : SkbSource) (peer : Option PeerId) : WG.M Unit := do
  if ← branch .hsInitNoPeer peer.isNone then return
  let some pid := peer | invariant "unreachable"
  setPeerEndpointFromSkb pid src
  sendHandshakeResponse pid
  if ← branch .hsWrongPacket peer.isNone then invariant "a wrong type of packet in the handshake queue"
  let some pid := peer | invariant "unreachable"
  let p ← getPeer pid
  setPeer pid {p with rxBytes := p.rxBytes + msg.length}
  modifyDev fun d => {d with rxPackets := d.rxPackets + 1,rxBytes := d.rxBytes + msg.length}
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  peerPut peer

def beforeConsumer (loaded : Bool) : WG.M Unit := do
  let _ ← branch .hsLoadedOperand loaded
  if loaded then
    let _ ← branch .hsLoadedCookieOk true
    pure ()
  else
    let _ ← branch .hsNotLoaded true
    let _ ← branch .hsMacNoCookie true
    pure ()
  let _ ← branch .hsSwitchInitiation true
  let _ ← branch .hsInitNeedsCookie false
  pure ()

theorem handler_factor (msg : Key) (src : SkbSource) (loaded : Bool)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    afterMac msg src loaded (authenticatedMac loaded) =
      (beforeConsumer loaded >>= fun _ => consumeInitiation msg >>= afterConsumer msg src) := by
  funext w a
  cases loaded <;>
    simp only [afterMac,authenticatedMac,kind,beforeConsumer,
      Bool.not_false,Bool.not_true,↓reduceIte,BEq.rfl,WG.orM,WG.andM,
      branch,pure_bind]
  all_goals rfl

theorem afterConsumer_refused (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient) :
    ((afterConsumer msg src none).run w).run a =
      .ok (((),w),record a .hsInitNoPeer true) := rfl

/-- The actual initialized stale receipt selects the native return continuation
that emits no response and changes no WG state. This source cut needs no
incoming freshness invariant or earlier MAC-ambient reconstruction. -/
theorem initialized_continuation (facts : H1DriverSourceFacts) (config : H1ConfigurationTagFrames)
    (traffic : H1TrafficTagFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (msg : Key) (r : WGRunWitness (Option PeerId))
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ CausalJournal.Event.exchange (.consumeInitiation msg r) :: post)
    (stale : Stale msg r.before r.ambientBefore) (src : SkbSource) :
    ((afterConsumer msg src r.value).run r.after).run r.ambientAfter =
      .ok (((),r.after),record r.ambientAfter .hsInitNoPeer true) := by
  rw [(initialized_refusal facts config traffic trace placeholders pre post msg r position stale).1]
  exact afterConsumer_refused msg src r.after r.ambientAfter

end Leanux.Proofs.WG.HandshakeSecurity.StaleInitiation
