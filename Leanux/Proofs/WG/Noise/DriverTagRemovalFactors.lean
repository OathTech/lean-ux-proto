import Leanux.Proofs.WG.Queues.JointRemoval
import Leanux.Proofs.WG.Queues.JointDestruct

/-! Native factors separated from observer and frame dependencies. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Removal
open Leanux Leanux.WG
universe u

/-! The only new factor exposes the two actual inline workqueue flushes.
All guards, original errors and final accounting remain literal. -/
def afterDeadWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α)
    (keys timers : PeerId → m Unit) (drain : Option PeerId → m Unit)
    (release : PeerId → m Unit) (pid : PeerId) : m Unit := do
  if ← lift (do branch .peerRemoveNotDead !(← getPeer pid).isDead) then
    lift (unsupported "peer_remove_after_dead: WARN_ON(!peer->is_dead)")
  keys pid
  timers pid
  let d ← lift getDev
  if !d.encryptQueue.empty || !d.decryptQueue.empty || !d.txWorkQueue.isEmpty
      || d.peers.toList.any (·.2.napiScheduled) then
    lift (unsupported "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)")
  drain none
  if (← lift getDev).numPeers == 0 then lift (invariant "--num_peers below zero")
  lift (modifyDev fun d => {d with numPeers := d.numPeers-1})
  release pid

theorem afterDead_factor (pid : PeerId) : WG.peerRemoveAfterDead pid =
    afterDeadWith (fun {_} a => a) keypairsClear timersStop drainHandshakeSendWq
      (fun p => WG.peerPut (some p)) pid := by
  simp only [WG.peerRemoveAfterDead,afterDeadWith,bind_assoc]

abbrev destructFinishSource : WG.M Unit :=
  pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish

end Leanux.Proofs.WG.Noise.DriverTags.Removal
