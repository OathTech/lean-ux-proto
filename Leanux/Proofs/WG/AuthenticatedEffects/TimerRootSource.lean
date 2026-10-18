import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeCausalReceiver

/-! Exact native timer-arm occurrences inside the authenticated handshake
receiver. An arm names the index of the callback that entered it, rather than
using any older admission of the same peer as permission. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
open HandshakeCausal (Kind)
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

structure Arm where
  origin : Nat
  kind : HandshakeCausal.Kind
  peer : PeerId
  timer : PeerTimer
  delay : Nat
  caller : Option UInt64
  run : WGRunWitness Unit

def Arm.Native (r : Arm) : Prop := r.run.Valid (armTimer r.peer r.timer r.delay r.caller)

structure Queued where
  origin : Nat
  kind : HandshakeCausal.Kind
  peer : PeerId
  run : WGRunWitness Unit

def Queued.Native (r : Queued) : Prop :=
  r.run.Valid (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [r.peer]})

structure Submitted where
  origin : Nat
  kind : HandshakeCausal.Kind
  peer : PeerId
  items : List SkbId
  run : WGRunWitness Unit

def Submitted.Native (r : Submitted) : Prop := r.run.Valid (createData r.peer r.items)

inductive Event where
  | base (event : HandshakeCausal.Event)
  | armed (receipt : Arm)
  | queued (receipt : Queued)
  | submitted (receipt : Submitted)

def base : Event → Option HandshakeCausal.Event
  | .base e => some e
  | .armed _ | .queued _ | .submitted _ => none

def history (h : List Event) := h.filterMap base

def enter (kind : HandshakeCausal.Kind) (pid : PeerId) : WGPrefix Event Nat :=
  fun w a => ExceptT.mk fun h =>
    (.ok (((history h).length,w),a),h ++ [.base (.callback kind pid)])

def call (kind : HandshakeCausal.Kind) (pid : PeerId) (body : Nat → WGPrefix Event α) : WGPrefix Event α := do
  let origin ← enter kind pid
  body origin

def arm (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (t : PeerTimer)
    (delay : Nat) (caller : Option UInt64) : WGPrefix Event Unit :=
  receiptWGObserved (liftWGPrefix (armTimer pid t delay caller))
    (fun r => .armed ⟨origin,kind,pid,t,delay,caller,r⟩)

def modifyTimer (origin : Nat) (kind : HandshakeCausal.Kind) (site : HiddenSite)
    (pid : PeerId) (t : PeerTimer) (delay : Nat) : WGPrefix Event Bool := do
  let jc ← liftWGPrefix (callerJiffies site)
  if ← liftWGPrefix (modPeerTimerGuard pid) then
    arm origin kind pid t delay jc
    return true
  return false

def derived (origin : Nat) (pid : PeerId) : WGPrefix Event Unit := do
  discard <| modifyTimer origin .sessionDerived .timerJiffiesSessionDerived
    pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS

def traversal (origin : Nat) (pid : PeerId) : WGPrefix Event Unit := do
  let interval := (← liftWGPrefix (getPeer pid)).persistentKeepaliveInterval
  if ← liftWGPrefix (branchCmp .traversalKeepalive (interval != 0) interval 0) then
    discard <| modifyTimer origin .traversal .timerJiffiesTraversal
      pid .persistentKeepalive (interval * HZ)

def old (a : WGPrefix HandshakeCausal.Event α) : WGPrefix Event α := focusStatePrefix .base base a

def ops (mac : HandshakeMac) : Ops (WGPrefix Event) where
  step := liftWGPrefix
  session := fun pid => old (HandshakeCausal.call .session pid (beginSession pid))
  modifyPeer := fun pid f => old (HandshakeCausal.call .peerWrite pid (do setPeer pid (f (← getPeer pid))))
  create := fun pid => old (HandshakeCausal.call .responseCreate pid (createResponse pid))
  mac := fun pid msg => old (HandshakeCausal.call .outgoingMac pid (addMacToPacket pid msg))
  send := fun pid msg => old (HandshakeCausal.call .send pid (sendBufferToPeer pid msg))
  derived := fun pid => call .sessionDerived pid (fun origin => derived origin pid)
  traversal := fun pid => call .traversal pid (fun origin => traversal origin pid)
  sent := fun pid => old (HandshakeCausal.call .authenticatedSent pid (timersAnyAuthenticatedPacketSent pid))
  cookie := fun msg src => liftWGPrefix (sendHandshakeCookie msg src)
  initiation := fun msg => old (HandshakeCausal.initiation {mac with input := msg})
  response := fun msg => old (HandshakeCausal.response {mac with input := msg})
  endpoint := fun pid src => old (HandshakeCausal.call .endpoint pid (setPeerEndpointFromSkb pid src))
  complete := fun pid => old (HandshakeCausal.call .handshakeComplete pid (timersHandshakeComplete pid))
  keepalive := fun pid => old (HandshakeCausal.call .keepalive pid (sendKeepalive pid))
  received := fun pid => old (HandshakeCausal.call .authenticatedReceived pid (timersAnyAuthenticatedPacketReceived pid))
  put := fun peer => liftWGPrefix (WG.peerPut peer)
  cookieConsume := fun msg => liftWGPrefix (cookieMessageConsume msg)

def receive (msg : Key) (src : SkbSource) : WGPrefix Event Unit := do
  if ← liftWGPrefix (branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE)) then
    liftWGPrefix (cookieMessageConsume msg)
    return
  let loaded ← liftWGPrefix Cookies.loadPhase
  let checked ← captureWGRun (cookieValidatePacket msg src loaded)
  afterMacWith (ops ⟨msg,src,loaded,checked⟩) msg src loaded checked.value

end Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot
