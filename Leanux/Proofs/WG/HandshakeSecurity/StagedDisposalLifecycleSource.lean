import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeLifecycleSource

/-! Counted staged erasure is observable at its native lifecycle cut. All
handshake drains keep their existing callback and order, including nested drains. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Logged

def afterDeadWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (drain : Option PeerId → m Unit)
    (release : Option PeerId → m Unit) (pid : PeerId) : m Unit := do
  if ← step (branch .peerRemoveNotDead !(← step (getPeer pid)).isDead) then
    step (unsupported "peer_remove_after_dead: WARN_ON(!peer->is_dead)")
  step (keypairsClear pid)
  SendExchange.timersStopWith step drain pid
  let d ← step getDev
  if !d.encryptQueue.empty || !d.decryptQueue.empty || !d.txWorkQueue.isEmpty
      || d.peers.toList.any (·.2.napiScheduled) then
    step (unsupported "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)")
  drain none
  if (← step getDev).numPeers == 0 then step (invariant "--num_peers below zero")
  step (modifyDev fun d => { d with numPeers := d.numPeers - 1 })
  release (some pid)

def removeWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (drain : Option PeerId → m Unit)
    (release : Option PeerId → m Unit) (peer : Option PeerId) : m Unit :=
  Configuration.peerRemoveWith step (fun pid => step (peerMakeDead pid))
    (afterDeadWith step drain release) peer

def removeAllWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (drain : Option PeerId → m Unit)
    (release : Option PeerId → m Unit) : m Unit :=
  Configuration.peerRemoveAllWith step (step free) (fun pid => step (peerMakeDead pid))
    (afterDeadWith step drain release)

def stopWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (drain : Option PeerId → m Unit)
    (purge : PeerId → m Unit) : m Unit := do
  for pid in (← step getDev).peerList do
    _ ← step (branch .stopPeersIter true)
    step (requireNotPending pid "wg_stop while a handshake is queued")
    purge pid
    SendExchange.timersStopWith step drain pid
    step (handshakeClear pid)
    step (keypairsClear pid)
    step (resetLastSentHandshake pid)
  _ ← step (branch .stopPeersIter false)
  if !(← step getDev).handshakeQueue.empty then
    step (unsupported "wg_stop with handshake messages queued for the receive worker (its timing)")
  _ ← step (branch .stopDrainIter false)
  step (modifyDev fun d => {d with handshakeQueueLen := 0})
  step (socketReinit none none)

def downWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (drain : Option PeerId → m Unit)
    (purge : PeerId → m Unit) : m Unit := do
  step (modifyDev fun d => {d with running := false})
  stopWith step drain purge

def destructWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (drain : Option PeerId → m Unit)
    (release : Option PeerId → m Unit) : m Unit :=
  Configuration.destructWith step (removeAllWith step drain release)
    (step (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish))

theorem afterDead_neutral [Monad m] (step : {α : Type} → WG.M α → m α)
    (drain : Option PeerId → m Unit) (pid : PeerId) :
    afterDeadWith step drain (fun peer => step (peerPut peer)) pid = SendExchange.afterDeadWith step drain pid := rfl
theorem remove_neutral [Monad m] (step : {α : Type} → WG.M α → m α)
    (drain : Option PeerId → m Unit) (peer : Option PeerId) :
    removeWith step drain (fun peer => step (peerPut peer)) peer = SendExchange.removeWith step drain peer := rfl
theorem removeAll_neutral [Monad m] (step : {α : Type} → WG.M α → m α)
    (drain : Option PeerId → m Unit) :
    removeAllWith step drain (fun peer => step (peerPut peer)) = SendExchange.removeAllWith step drain := rfl
theorem stop_neutral [Monad m] (step : {α : Type} → WG.M α → m α)
    (drain : Option PeerId → m Unit) :
    stopWith step drain (fun pid => step (purgeStagedPackets pid)) = SendExchange.stopWith step drain := rfl
theorem down_neutral [Monad m] (step : {α : Type} → WG.M α → m α)
    (drain : Option PeerId → m Unit) :
    downWith step drain (fun pid => step (purgeStagedPackets pid)) = SendExchange.downWith step drain := rfl
theorem destruct_neutral [Monad m] (step : {α : Type} → WG.M α → m α)
    (drain : Option PeerId → m Unit) :
    destructWith step drain (fun peer => step (peerPut peer)) = SendExchange.destructWith step drain := rfl

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.Lifecycle
