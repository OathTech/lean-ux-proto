import Leanux.Proofs.WG.Config.QuietTimers
import Leanux.Proofs.WG.Noise.ClearModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def removalDeadGuard (pid : PeerId) : WG.M Unit := do
  if ← branch .peerRemoveNotDead !(← getPeer pid).isDead then
    unsupported "peer_remove_after_dead: WARN_ON(!peer->is_dead)"

def decrementPeerCount : WG.M Unit := do
  if (← getDev).numPeers == 0 then invariant "--num_peers below zero"
  modifyDev fun d => { d with numPeers := d.numPeers - 1 }

/-- Correct the legacy source equation by retaining the actual crypt-work guard. -/
theorem peerRemoveAfterDead_source (pid : PeerId) :
    peerRemoveAfterDead pid = (do
      removalDeadGuard pid
      keypairsClear pid
      timersStop pid
      let d ← getDev
      if !d.encryptQueue.empty || !d.decryptQueue.empty || !d.txWorkQueue.isEmpty ||
          d.peers.toList.any (·.2.napiScheduled) then
        unsupported "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)"
      drainHandshakeSendWq none
      decrementPeerCount
      peerPut (some pid)) := by
  have distribute {α β : Type} (q : Prop) [Decidable q] (a b : WG.M α) (f : α → WG.M β) :
      ((if q then a else b) >>= f) = (if q then a >>= f else b >>= f) := by
    split <;> rfl
  simp only [peerRemoveAfterDead, removalDeadGuard, decrementPeerCount,
    bind_assoc, distribute, pure_bind]

end Leanux.Proofs.WG.Config
