import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeContracts
import Leanux.Proofs.WG.Queues.JointDevice

/-! Only explicit local trigger sites create fixture roots. Native input,
stack replies and deferred dispatch do not gain permission from this wrapper.
The guarded peer-configuration and open bodies are shared source factors. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

inductive PeerAction where
  | staging
  | keepalive

/-- Source metadata, not an authorization premise. The driver must call the
wrapper at the corresponding actual local operation site. -/
inductive Trigger where
  | transmit (family addr : Nat) (packets : List Packet) (mtu : Nat)
  | peerConfiguration (attrs : PeerAttrs) (peer : PeerId) (action : PeerAction)
  | identityConfiguration (attrs : DeviceAttrs) (peer : PeerId)
  | interfaceOpen (peer : PeerId) (action : PeerAction)

structure Hooks (E : Type) where
  enter : Trigger → WGPrefix E Nat := fun _ => pure 0
  leave : Nat → WGPrefix E Unit := fun _ => pure ()

def runWith (hooks : Hooks E) (trigger : Trigger) (body : WGPrefix E α) : WGPrefix E α := do
  let token ← hooks.enter trigger
  let result ← body
  hooks.leave token
  pure result

def neutral : Hooks E := {}

theorem run_neutral (trigger : Trigger) (body : WGPrefix E α) :
    runWith neutral trigger body = body := by
  simp [runWith,neutral]

/-- This is the exact branch order after allowed-IP processing. It exposes
only the two callbacks that configuration may actually use to start a send. -/
def peerFinishWith [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (staging keepalive : PeerId → m Unit)
    (out : PeerAttrs → Option PeerId → Int → m Int)
    (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) : m Int := do
  let running := (← step getDev).running
  if ← step (branch .peerHasKeepalive attrs.keepalive.isSome) then
    let interval := attrs.keepalive.getD 0
    let p ← step (getPeer pid)
    let send ← step (WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running)))
    step (setPeer pid {p with persistentKeepaliveInterval := interval})
    if ← step (branch .peerSendKeepalive send) then keepalive pid
  if ← step (branch .peerRunning running) then staging pid
  out attrs peer ret

/-- Original socket initialization and saved peer traversal, with local send
callbacks exposed at their original native guards. -/
def openWith [Monad m] (step : {α : Type} → WG.M α → m α)
    (staging keepalive : PeerId → m Unit) : m Int := do
  let dev ← step getDev
  _ ← step (branch .openHasInet dev.inet4Dev)
  _ ← step (branch .openHasInet6 dev.inet6Dev)
  let d ← step getDev
  let ret ← step (socketInit d.incomingPort)
  if ← step (branch .openSocketError (ret < 0)) then return ret
  for pid in d.peerList do
    _ ← step (branch .openPeersIter true)
    staging pid
    if ← step (branch .openKeepalive ((← step (getPeer pid)).persistentKeepaliveInterval != 0)) then
      keepalive pid
  _ ← step (branch .openPeersIter false)
  return 0

/-- Configuration creates roots only around its guarded local send callbacks;
the preceding lookup, updates and any removal drains remain outside them. -/
def peerFinishObserved (hooks : Hooks E)
    (staging keepalive : PeerId → WGPrefix E Unit)
    (out : PeerAttrs → Option PeerId → Int → WGPrefix E Int)
    (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) : WGPrefix E Int :=
  peerFinishWith liftWGPrefix
    (fun pid => runWith hooks (.peerConfiguration attrs pid .staging) (staging pid))
    (fun pid => runWith hooks (.peerConfiguration attrs pid .keepalive) (keepalive pid))
    out attrs peer pid ret

def openObserved (hooks : Hooks E) (staging keepalive : PeerId → WGPrefix E Unit) : WGPrefix E Int :=
  openWith liftWGPrefix
    (fun pid => runWith hooks (.interfaceOpen pid .staging) (staging pid))
    (fun pid => runWith hooks (.interfaceOpen pid .keepalive) (keepalive pid))

theorem peerFinish_neutral (staging keepalive : PeerId → WGPrefix E Unit)
    (out : PeerAttrs → Option PeerId → Int → WGPrefix E Int)
    (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    peerFinishObserved neutral staging keepalive out attrs peer pid ret =
      peerFinishWith liftWGPrefix staging keepalive out attrs peer pid ret := by
  simp only [peerFinishObserved,run_neutral]

theorem open_neutral (staging keepalive : PeerId → WGPrefix E Unit) :
    openObserved neutral staging keepalive = openWith liftWGPrefix staging keepalive := by
  simp only [openObserved,run_neutral]

end Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffects
