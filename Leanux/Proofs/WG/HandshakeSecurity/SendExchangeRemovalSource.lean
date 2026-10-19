import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeSource
import Leanux.Proofs.WG.Queues.JointDevice

/-! Configuration removal drains the same handshake-send callback as scheduled
work. No peer-removal failure, guard, or queue drain is skipped. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.SendExchange
open Leanux Leanux.WG Leanux.Proofs.Logged

def timersStopWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (drain : Option PeerId → m Unit) (pid : PeerId) : m Unit := do
  for timer in PeerTimer.all do step (delTimer pid timer)
  if (← step getDev).clearWorkQueue.contains pid then drain (some pid)

theorem timersStop_factor (pid : PeerId) :
    timersStopWith (fun {_} a => a) drainHandshakeSendWq pid = timersStop pid := rfl

def afterDeadWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (drain : Option PeerId → m Unit) (pid : PeerId) : m Unit := do
  if ← step (branch .peerRemoveNotDead !(← step (getPeer pid)).isDead) then
    step (unsupported "peer_remove_after_dead: WARN_ON(!peer->is_dead)")
  step (keypairsClear pid)
  timersStopWith step drain pid
  let d ← step getDev
  if !d.encryptQueue.empty || !d.decryptQueue.empty || !d.txWorkQueue.isEmpty
      || d.peers.toList.any (·.2.napiScheduled) then
    step (unsupported "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)")
  drain none
  if (← step getDev).numPeers == 0 then step (invariant "--num_peers below zero")
  step (modifyDev fun d => {d with numPeers := d.numPeers - 1})
  step (peerPut (some pid))

def removeWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (drain : Option PeerId → m Unit) (peer : Option PeerId) : m Unit :=
  Configuration.peerRemoveWith step (fun pid => step (peerMakeDead pid))
    (afterDeadWith step drain) peer

def removeAllWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α)
    (drain : Option PeerId → m Unit) : m Unit :=
  Configuration.peerRemoveAllWith step (step free) (fun pid => step (peerMakeDead pid))
    (afterDeadWith step drain)

theorem afterDead_factor (pid : PeerId) :
    afterDeadWith (fun {_} a => a) drainHandshakeSendWq pid = peerRemoveAfterDead pid := rfl
theorem remove_factor (peer : Option PeerId) :
    removeWith (fun {_} a => a) drainHandshakeSendWq peer = peerRemove peer := rfl
theorem removeAll_factor :
    removeAllWith (fun {_} a => a) drainHandshakeSendWq = peerRemoveAll := rfl

end Leanux.Proofs.WG.HandshakeSecurity.SendExchange
