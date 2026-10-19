import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsNeutral
import Leanux.Proofs.WG.Lifetimes.TxCompletion

/-! The existing lifetime-observed timer/queue helpers with their original
accesses retained. Only completed arm and queue-append callbacks are exposed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

structure Ops (m : Type → Type) where
  step : {α : Type} → WG.M α → m α
  peer : PeerId → m Peer
  keypair : KeypairId → m Keypair
  modifyPeer : PeerId → (Peer → Peer) → m Unit
  guard : PeerId → m Bool
  arm : PeerId → PeerTimer → Nat → Option UInt64 → m Unit
  get : PeerId → m Unit
  put : Option PeerId → m Unit
  append : PeerId → m Unit

def native : Ops MixedM where
  step := liftWGPrefix
  peer := getPeerMixed
  keypair := getKeypairPrefix
  modifyPeer := modifyPeerKeysPrefix
  guard := modPeerTimerGuardPrefix
  arm := fun pid timer delay caller => armTimerPrefix pid timer delay caller
  get := peerGetMixed
  put := peerPutMixed
  append := fun pid => liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})

def modifyWith [Monad m] (o : Ops m) (site : HiddenSite) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) : m Bool := do
  let jc ← o.step (callerJiffies site)
  if ← o.guard pid then
    o.arm pid timer delay jc
    return true
  return false

def traversalWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  let interval := (← o.peer pid).persistentKeepaliveInterval
  if ← o.step (branchCmp .traversalKeepalive (interval != 0) interval 0) then
    discard <| modifyWith o .timerJiffiesTraversal pid .persistentKeepalive (interval * HZ)

def dataSentWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  if ← o.step (branch .timersDataSentNotPending !((← o.peer pid).timerPending .newHandshake)) then
    let jc ← o.step (callerJiffies .timerJiffiesDataSent)
    let jitter ← o.step (jitterBelowRekeyTimeout .newHandshakeJitter)
    if ← o.guard pid then
      o.arm pid .newHandshake (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter) jc

def queuedWith [Monad m] (o : Ops m) (pid : PeerId) (retry : Bool) : m Unit := do
  if ← o.step (branch .queuedNotRetry !retry) then
    o.modifyPeer pid fun p => {p with timerHandshakeAttempts := 0}
  let p ← o.peer pid
  if ← o.step (branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT not) then return
  if ← o.step (branch .queuedDead p.isDead) then return
  o.get pid
  if ← o.step (branch .queuedAlreadyQueued (p.handshakePending && !(← o.step (peekQueuedUnit .sendWorker pid)))) then
    o.put (some pid)
    return
  o.modifyPeer pid fun p => {p with handshakePending := true}
  o.step (recordQueued .sendWorker pid)
  o.append pid

def freshWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  let current := (← o.peer pid).keypairCurrent
  let send ← andPrefix (o.step (branch .freshKeypair current.isSome)) do
    let some id := current | o.step (invariant "unreachable")
    let k ← o.keypair id
    andPrefix (o.step (branch .freshValid k.sending.isValid)) do
      orPrefix (o.step (branchCmp .freshCounter (k.sendingCounter > REKEY_AFTER_MESSAGES) k.sendingCounter REKEY_AFTER_MESSAGES)) do
        andPrefix (o.step (branch .freshInitiator k.iAmTheInitiator)) do
          o.step (branchExpired .freshExpired k.sending.birthdate REKEY_AFTER_TIME)
  if ← o.step (branch .freshSend send) then queuedWith o pid false

theorem modify_factor (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    modPeerTimerPrefix site pid timer delay = modifyWith native site pid timer delay := rfl
theorem traversal_factor (pid : PeerId) : timersTraversalPrefix pid = traversalWith native pid := rfl
theorem dataSent_factor (pid : PeerId) : timersDataSentPrefix pid = dataSentWith native pid := rfl
theorem queued_factor (pid : PeerId) (retry : Bool) :
    sendQueuedHandshakeInitiationPrefix pid retry = queuedWith native pid retry := rfl
theorem fresh_factor (pid : PeerId) : keepKeyFreshPrefix pid = freshWith native pid := rfl

end Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffects
