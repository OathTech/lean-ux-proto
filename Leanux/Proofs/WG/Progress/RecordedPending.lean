import Leanux.Proofs.WG.Progress.QueueRefill
import Leanux.Proofs.WG.Progress.RunnerBoundaryAuditSource

/-! Current initialized supplied-record pending-dispatch regression.
The stream missing the empty redispatch is refused; supplying that section
is accepted with cleared pending work and empty queues at the audited cut.
These are fail-noisy interpreter checks, not kernel-reduction theorems.
The records use the supported legacy mode with armRecords=false. The former
committed-receipt comparator is deferred until its shared observer is carried. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordedPending
open Leanux Leanux.Runner Leanux.Proofs.WG Leanux.Proofs.WG.Progress

/-- Reuse the initialized handshake and encrypted incoming packet from the
earlier rejected-refill prefix. Yield after the nested refill, resume with the
new occupancy, and supply the original completion suffix. -/
def records : Array (List HiddenRecord) :=
  QueueRefill.rows.set! 4
    ((QueueRefill.rows[4]!).take 11 ++
      [recAt .reschedEncrypt (word 0),
       QueueRefill.stop .encryptWorker, QueueRefill.stop .decryptWorker,
       QueueRefill.start .txWorker,
       QueueRefill.start .netRx, QueueRefill.stop .netRx,
       recAt .newHandshakeJitter (word 1),
       recAt .birthdateExpired (QueueRefill.c 103),
       QueueRefill.start .netRx, QueueRefill.stop .netRx,
       recAt .birthdateExpired (QueueRefill.c 103),
       QueueRefill.stop .txWorker, QueueRefill.j 4])

def trace : Trace :=
  { QueueRefill.concreteTrace with
    id := "campaign2-recorded-encrypt-requeue", hidden := some records }

/-- Supply the required empty dispatch after useful work drains. The current
dispatcher consumes this section and clears the requeued encrypt identity. -/
def emptyRedispatchTrace : Trace :=
  { trace with
    hidden := some (records.set! 4
      ((records[4]!).dropLast ++
        [QueueRefill.start .encryptWorker, QueueRefill.stop .encryptWorker,
         QueueRefill.j 4])) }

/-- Both the native runner and its exact owned audit refuse the stream whose
requeued encrypt dispatch has no section. -/
def missingRedispatchCheck : Bool :=
  match executeTrace trace, executeTraceWithBoundaries trace false with
  | .error (op, .outsideDomain site message),
      .error (observedOp, .outsideDomain observedSite observedMessage) =>
    op == 4 && observedOp == 4 &&
      site == "drivers/net/wireguard/send.c:269" && observedSite == site &&
      message == "wg_packet_encrypt_worker is pending at the end of the wait (the dispatch its requeue causes has no section in the records)" &&
      observedMessage == message
  | _, _ => false

/-- The completed supplied stream is accepted by both actual runner and exact
audit. Its actual last cut has no pending work and the stated empty queues. -/
def drainedBoundaryCheck : Bool :=
  match executeTrace emptyRedispatchTrace,
      executeTraceWithBoundaries emptyRedispatchTrace false with
  | .ok _, .ok audit =>
    match audit.boundaries[4]? with
    | none => false
    | some cut =>
      match cut.after.wg.device with
      | none => false
      | some d =>
        audit.boundaries.length == 5 && cut.index == 4 && cut.result == 2 &&
        cut.after.ambient.pendingWork == [] &&
        cut.after.ambient.hidden == some [] &&
        cut.after.ambient.suspended.isEmpty && !cut.after.wg.netRxRaised &&
        d.handshakeQueue.empty && d.handshakeQueue.count == 0 &&
        d.handshakeQueueLen == 0 && d.decryptQueue.empty &&
        d.decryptQueue.count == 0 && d.encryptQueue.empty &&
        d.encryptQueue.count == 0 && d.txWorkQueue.isEmpty &&
        d.sendWorkQueue.isEmpty && d.clearWorkQueue.isEmpty &&
        d.peers.toList.all (fun entry =>
          !entry.2.napiScheduled && entry.2.rxQueue.all.isEmpty &&
          entry.2.txQueue.all.isEmpty)
  | _, _ => false

def reproduce : IO Unit := do
  unless missingRedispatchCheck do
    throw (IO.userError "recorded pending regression: missing-dispatch refusal changed")
  unless drainedBoundaryCheck do
    throw (IO.userError "recorded pending regression: accepted drained boundary changed")
  IO.println "Supplied-record regression passed: missing empty dispatch refused; supplied empty dispatch accepted with cleared pending work and empty queues"

#eval reproduce

end Leanux.Proofs.WG.Progress.RecordedPending
