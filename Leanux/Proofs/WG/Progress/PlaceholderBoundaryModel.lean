import Leanux.Proofs.WG.Progress.BatchBacklogModel
import Leanux.Proofs.WG.Progress.RunnerBoundaryAuditSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CurrentBoundaryWitness
open Leanux Leanux.Runner

def placeholderBoundaryTrace : Trace := { pendingTrace with
  id := "campaign2-current-placeholder-backlog"
  hidden := none
  steer := [(HiddenSite.udpPortDraw.info.label, some ((word 0).take 4))] }

/-- Supplied-record completion control for runtime reproduction.  These are
constructed records, not a captured Linux execution.  No theorem about this
control is claimed by the placeholder finding. -/
def recordedBoundaryControl : Trace := { pendingTrace with
  id := "campaign2-current-recorded-completion"
  hidden := some #[upRecords,
    batchRecords.take 3 ++
    [recAt (.sectionStart .receiveWorker) (word 1 ++ word 0),
     recAt (.sectionStop .receiveWorker) (word 1),
     recAt .jiffiesEnd (word 101)]] }

/-- Runtime-discovered domain-filter witness.  This checks the actual initialized
runner audit, not a reconstructed entry or successor.  Pending bookkeeping is
reported alongside only the explicit queue, count and NAPI tests. -/
def placeholderBoundaryCheck : Bool :=
  match executeTraceWithBoundaries placeholderBoundaryTrace true with
  | .error _ => false
  | .ok audit =>
    match audit.boundaries[1]? with
    | none => false
    | some cut =>
      match cut.after.wg.device with
      | none => false
      | some d =>
        cut.index == 1 && cut.result == 1 &&
        cut.after.ambient.pendingWork == [Worker.receiveWorker.index] &&
        cut.after.ambient.hidden.isNone && cut.after.ambient.suspended.isEmpty &&
        !cut.after.wg.netRxRaised && d.handshakeQueue.empty &&
        d.handshakeQueue.count == 0 && d.handshakeQueueLen == 0 &&
        d.decryptQueue.empty && d.encryptQueue.empty &&
        d.txWorkQueue.isEmpty && d.sendWorkQueue.isEmpty && d.clearWorkQueue.isEmpty &&
        !(d.peers.toList.any (fun item => item.2.napiScheduled))


end Leanux.Proofs.WG.Progress.CurrentBoundaryWitness
