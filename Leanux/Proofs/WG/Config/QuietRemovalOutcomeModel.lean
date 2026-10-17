import Leanux.Proofs.WG.Config.QuietModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Exact cleanup refusal order and the original successful removal effect. -/
def quietRemovalOutcome (d : Device) (pid : PeerId) (p : Peer)
    (out : Campaign2.Outcome Unit) : Prop :=
  let cleaned := quietCleanupDevice d pid p
  let peer := quietCleanupPeer p
  if !cleaned.encryptQueue.empty || !cleaned.decryptQueue.empty || !cleaned.txWorkQueue.isEmpty ||
      cleaned.peers.toList.any (·.2.napiScheduled) then
    out = .error (.outsideDomain
      s!"{Decision.keypairPutNull.info.file}:{Decision.keypairPutNull.info.line}"
      "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)")
  else
    let refusal : Option Stop := if peer.refcount = 1 then
      if peer.txQueue.peeked.isSome || !peer.txQueue.items.isEmpty ||
          peer.rxQueue.peeked.isSome || !peer.rxQueue.items.isEmpty then
        some (.invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)")
      else (PeerTimer.all.find? (fun t => peer.timerPending t || (peer.wheel t).isSome)).map
        (fun t => .invariant s!"peer {pid} released with its {repr t} timer pending")
    else none
    match refusal with
    | some stop => out = .error stop
    | none => ∃ final, out = .ok ((), final) ∧ final.wg.device = some (quietRemovedDevice d pid p)

end Leanux.Proofs.WG.Config
