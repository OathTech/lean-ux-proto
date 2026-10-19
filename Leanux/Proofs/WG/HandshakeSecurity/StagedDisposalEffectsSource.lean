import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsSource

/-! The actual queue/retransmit helpers with their reference repayment and
counted purge exposed. Neutral callbacks recover the existing source exactly. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Effects
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects

def queuedWith [Monad m] (o : TimerEffects.Ops m) (release : Option PeerId → m Unit)
    (pid : PeerId) (retry : Bool) : m Unit := do
  if ← o.step (branch .queuedNotRetry !retry) then
    o.step (setPeer pid { (← o.step (getPeer pid)) with timerHandshakeAttempts := 0 })
  let p ← o.step (getPeer pid)
  if ← o.step (branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·)) then return
  if ← o.step (branch .queuedDead p.isDead) then return
  o.step (peerGet pid)
  if ← o.step (branch .queuedAlreadyQueued (p.handshakePending && !(← o.step (peekQueuedUnit .sendWorker pid)))) then
    release (some pid)
    return
  o.step (setPeer pid { (← o.step (getPeer pid)) with handshakePending := true })
  o.step (recordQueued .sendWorker pid)
  o.append pid

def retransmitWith [Monad m] (o : TimerEffects.Ops m)
    (release : Option PeerId → m Unit) (purge : PeerId → m Unit) (pid : PeerId) : m Unit := do
  let attempts := (← o.step (getPeer pid)).timerHandshakeAttempts
  if ← o.step (branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES) then
    o.step (delTimer pid .sendKeepalive)
    purge pid
    if ← o.step (branch .retransmitZeroKeyNotPending !((← o.step (getPeer pid)).timerPending .zeroKeyMaterial)) then
      discard <| TimerEffects.modifyWith o .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
  else
    let p ← o.step (getPeer pid)
    o.step (setPeer pid {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1})
    o.step (clearPeerEndpointSrc pid)
    queuedWith o release pid true

def newHandshakeWith [Monad m] (o : TimerEffects.Ops m)
    (release : Option PeerId → m Unit) (pid : PeerId) : m Unit := do
  o.step (clearPeerEndpointSrc pid)
  queuedWith o release pid false

theorem queued_neutral [Monad m] (o : TimerEffects.Ops m) (pid : PeerId) (retry : Bool) :
    queuedWith o (fun peer => o.step (peerPut peer)) pid retry = TimerEffects.queuedWith o pid retry := rfl

theorem retransmit_neutral [Monad m] (o : TimerEffects.Ops m) (pid : PeerId) :
    retransmitWith o (fun peer => o.step (peerPut peer))
      (fun peer => o.step (purgeStagedPackets peer)) pid = TimerEffects.retransmitWith o pid := rfl

theorem newHandshake_neutral [Monad m] (o : TimerEffects.Ops m) (pid : PeerId) :
    newHandshakeWith o (fun peer => o.step (peerPut peer)) pid = TimerEffects.expiredNewWith o pid := rfl

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Effects
