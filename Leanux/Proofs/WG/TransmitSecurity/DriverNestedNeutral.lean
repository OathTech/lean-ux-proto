import Leanux.Proofs.WG.TransmitSecurity.DriverSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseWorkerNeutral

/-! Native repayment callbacks recover the original nested source leaves.
The equalities retain every native state and stopped execution prefix. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem nestedOps_neutral (hooks : Hooks E)
    (release : hooks.peerRelease = fun peer => liftWGPrefix (peerPut peer)) :
    nestedOps hooks = RetirementSecurity.NestedPeerRelease.lifted := by
  unfold nestedOps
  rw [release]
  rfl

theorem clearWorker_lift (hooks : Hooks E)
    (release : hooks.peerRelease = fun peer => liftWGPrefix (peerPut peer)) :
    clearWorkerObserved hooks = liftPrefix Env.runOneClearWorker := by
  unfold clearWorkerObserved
  rw [nestedOps_neutral hooks release]
  exact RetirementSecurity.NestedPeerRelease.oneClear_lifted

theorem flushedClear_lift (hooks : Hooks E)
    (release : hooks.peerRelease = fun peer => liftWGPrefix (peerPut peer)) (pid : PeerId) :
    RetirementSecurity.NestedPeerRelease.flushedClearWith (nestedOps hooks) pid = liftWGPrefix (runFlushedClearWork pid) := by
  rw [nestedOps_neutral hooks release]
  exact RetirementSecurity.NestedPeerRelease.flushedClear_lifted pid

theorem rxFinish_lift (hooks : Hooks E)
    (release : hooks.peerRelease = fun peer => liftWGPrefix (peerPut peer)) (pid : PeerId) (ready : Packets.RxReady) :
    RetirementSecurity.NestedPeerRelease.rxFinishWith (nestedOps hooks) pid ready = liftWGPrefix (Packets.rxFinish pid ready) := by
  rw [nestedOps_neutral hooks release]
  exact RetirementSecurity.NestedPeerRelease.rxFinish_lifted pid ready

theorem receiveEntry_lift (hooks : Hooks E)
    (release : hooks.peerRelease = fun peer => liftWGPrefix (peerPut peer)) (msg : Key) (src : SkbSource) :
    receiveEntryObserved hooks msg src = liftWGObserver (liftWGPrefix (wgReceive msg src)) := by
  unfold receiveEntryObserved
  rw [nestedOps_neutral hooks release,RetirementSecurity.NestedPeerRelease.receive_lifted]

theorem dumpDispatch_lift (hooks : Hooks E)
    (release : hooks.peerRelease = fun peer => liftWGPrefix (peerPut peer)) (call : Syscall) :
    RetirementSecurity.NestedPeerRelease.dumpDispatch (nestedOps hooks) call = liftPrefix (Leanux.dispatch call) := by
  rw [nestedOps_neutral hooks release]
  exact RetirementSecurity.NestedPeerRelease.dumpDispatch_lifted call

end Leanux.Proofs.WG.TransmitSecurity.Driver
