import Leanux.Proofs.WG.Index.ReleaseModel

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Exact refusal order of final peer release; non-final release does not inspect it. -/
def peerReleaseRefusal (pid : PeerId) (p : Peer) : Option Stop :=
  if p.refcount = 1 then
    if p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty ||
        p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty then
      some (.invariant "rcu_release: a released peer with packets on its tx_queue or rx_queue (peer.c:191)")
    else (PeerTimer.all.find? (fun t => p.timerPending t || (p.wheel t).isSome)).map
      (fun t => .invariant s!"peer {pid} released with its {repr t} timer pending")
  else none

end Leanux.Proofs.WG.Index
