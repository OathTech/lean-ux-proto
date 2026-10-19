import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerSource

/-! Native timer creation and handshake queueing with only the actual arm and
queue-append operations exposed. A caller can close these callbacks over its
current causal token; no lookup of an older admission is performed here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerEffects
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Ops (m : Type → Type) where
  step : {α : Type} → WG.M α → m α
  arm : PeerId → PeerTimer → Nat → Option UInt64 → m Unit
  append : PeerId → m Unit

def native : Ops WG.M where
  step := id
  arm := fun pid timer delay caller => armTimer pid timer delay caller
  append := fun pid => modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}

def observed (arm : PeerId → PeerTimer → Nat → Option UInt64 → WGPrefix E Unit)
    (append : PeerId → WGPrefix E Unit) : Ops (WGPrefix E) where
  step := liftWGPrefix
  arm := arm
  append := append

def modifyWith [Monad m] (o : Ops m) (site : HiddenSite) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) : m Bool := do
  let jc ← o.step (callerJiffies site)
  if ← o.step (modPeerTimerGuard pid) then
    o.arm pid timer delay jc
    return true
  return false

def derivedWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit :=
  discard <| modifyWith o .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS

def traversalWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  let interval := (← o.step (getPeer pid)).persistentKeepaliveInterval
  if ← o.step (branchCmp .traversalKeepalive (interval != 0) interval 0) then
    discard <| modifyWith o .timerJiffiesTraversal pid .persistentKeepalive (interval * HZ)

def dataSentWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  if ← o.step (branch .timersDataSentNotPending !((← o.step (getPeer pid)).timerPending .newHandshake)) then
    let jc ← o.step (callerJiffies .timerJiffiesDataSent)
    let jitter ← o.step (jitterBelowRekeyTimeout .newHandshakeJitter)
    if ← o.step (modPeerTimerGuard pid) then
      o.arm pid .newHandshake (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter) jc

def dataReceivedWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  if ← o.step (branch .timersDataReceivedRunning (← o.step getDev).running) then
    if ← o.step (branch .timersDataReceivedNotPending !((← o.step (getPeer pid)).timerPending .sendKeepalive)) then
      discard <| modifyWith o .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS
    else
      o.step (setPeer pid { (← o.step (getPeer pid)) with timerNeedAnotherKeepalive := true })

def initiatedWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  let jc ← o.step (callerJiffies .timerJiffiesHandshakeInitiated)
  let jitter ← o.step (jitterBelowRekeyTimeout .retransmitJitter)
  if ← o.step (modPeerTimerGuard pid) then
    o.arm pid .retransmitHandshake (REKEY_TIMEOUT_TICKS + jitter) jc

def queuedWith [Monad m] (o : Ops m) (pid : PeerId) (retry : Bool) : m Unit := do
  if ← o.step (branch .queuedNotRetry !retry) then
    o.step (setPeer pid { (← o.step (getPeer pid)) with timerHandshakeAttempts := 0 })
  let p ← o.step (getPeer pid)
  if ← o.step (branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·)) then return
  if ← o.step (branch .queuedDead p.isDead) then return
  o.step (peerGet pid)
  if ← o.step (branch .queuedAlreadyQueued (p.handshakePending && !(← o.step (peekQueuedUnit .sendWorker pid)))) then
    o.step (peerPut (some pid))
    return
  o.step (setPeer pid { (← o.step (getPeer pid)) with handshakePending := true })
  o.step (recordQueued .sendWorker pid)
  o.append pid

def retransmitWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  let attempts := (← o.step (getPeer pid)).timerHandshakeAttempts
  if ← o.step (branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES) then
    o.step (delTimer pid .sendKeepalive)
    o.step (purgeStagedPackets pid)
    if ← o.step (branch .retransmitZeroKeyNotPending !((← o.step (getPeer pid)).timerPending .zeroKeyMaterial)) then
      discard <| modifyWith o .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
  else
    let p ← o.step (getPeer pid)
    o.step (setPeer pid {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1})
    o.step (clearPeerEndpointSrc pid)
    queuedWith o pid true

def expiredKeepaliveWith [Monad m] (o : Ops m) (keepalive : PeerId → m Unit)
    (pid : PeerId) : m Unit := do
  keepalive pid
  if ← o.step (branch .keepaliveNeedAnother (← o.step (getPeer pid)).timerNeedAnotherKeepalive) then
    o.step (setPeer pid { (← o.step (getPeer pid)) with timerNeedAnotherKeepalive := false })
    discard <| modifyWith o .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS

def expiredNewWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  o.step (clearPeerEndpointSrc pid)
  queuedWith o pid false

def persistentWith [Monad m] (o : Ops m) (keepalive : PeerId → m Unit)
    (pid : PeerId) : m Unit := do
  if ← o.step (branch .persistentKeepaliveInterval ((← o.step (getPeer pid)).persistentKeepaliveInterval != 0)) then
    keepalive pid

def timerWith [Monad m] (o : Ops m) (keepalive : PeerId → m Unit)
    (pid : PeerId) : PeerTimer → m Unit
  | .retransmitHandshake => retransmitWith o pid
  | .sendKeepalive => expiredKeepaliveWith o keepalive pid
  | .newHandshake => expiredNewWith o pid
  | .zeroKeyMaterial => o.step (expiredZeroKeyMaterial pid)
  | .persistentKeepalive => persistentWith o keepalive pid

theorem modify_factor (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    modPeerTimer site pid timer delay = modifyWith native site pid timer delay := rfl
theorem derived_factor (pid : PeerId) : timersSessionDerived pid = derivedWith native pid := rfl
theorem traversal_factor (pid : PeerId) : timersTraversal pid = traversalWith native pid := rfl
theorem dataSent_factor (pid : PeerId) : timersDataSent pid = dataSentWith native pid := rfl
theorem dataReceived_factor (pid : PeerId) : timersDataReceived pid = dataReceivedWith native pid := rfl
theorem initiated_factor (pid : PeerId) : timersHandshakeInitiated pid = initiatedWith native pid := rfl
theorem queued_factor (pid : PeerId) (retry : Bool) :
    sendQueuedHandshakeInitiation pid retry = queuedWith native pid retry := rfl
theorem retransmit_factor (pid : PeerId) :
    expiredRetransmitHandshake pid = retransmitWith native pid := rfl
theorem expiredKeepalive_factor (pid : PeerId) :
    expiredSendKeepalive pid = expiredKeepaliveWith native sendKeepalive pid := rfl
theorem expiredNew_factor (pid : PeerId) : expiredNewHandshake pid = expiredNewWith native pid := rfl
theorem persistent_factor (pid : PeerId) :
    expiredSendPersistentKeepalive pid = persistentWith native sendKeepalive pid := rfl
theorem timer_factor (pid : PeerId) (timer : PeerTimer) :
    timerCallback pid timer = timerWith native sendKeepalive pid timer := by cases timer <;> rfl

end Leanux.Proofs.WG.AuthenticatedEffects.TimerEffects
