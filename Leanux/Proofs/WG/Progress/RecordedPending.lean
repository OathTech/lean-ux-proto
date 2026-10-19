import Leanux.Proofs.WG.Progress.QueueRefill
import Leanux.Proofs.WG.Progress.RunnerBoundaryAuditSource
import Leanux.Proofs.WG.Progress.CommittedInitializedClaims

/-! Initialized supplied-record pending-identity counterexample.
This is a fail-noisy interpreter reproduction, not a kernel-reduction theorem.
Useful packet queues drain; the requeued encrypt identity remains pending.
The records use the supported legacy mode with armRecords=false. -/
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

/-- Supply the otherwise missing empty dispatch after useful work drains.
The current dispatcher refuses to consume its section start. -/
def emptyRedispatchTrace : Trace :=
  { trace with
    hidden := some (records.set! 4
      ((records[4]!).dropLast ++
        [QueueRefill.start .encryptWorker, QueueRefill.stop .encryptWorker,
         QueueRefill.j 4])) }

def boundaryCheck : Bool :=
  match executeTrace trace, executeTraceWithBoundaries trace false with
  | .ok _, .ok audit =>
    match audit.boundaries[4]? with
    | none => false
    | some cut =>
      match cut.after.wg.device with
      | none => false
      | some d =>
        audit.boundaries.length == 5 && cut.index == 4 && cut.result == 2 &&
        cut.after.ambient.pendingWork == [Worker.encryptWorker.index] &&
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

abbrev ReceiptRow := Nat × Nat × Nat × Nat × List Nat × List Nat × Option Nat

def receiptRow (r : CommittedRuns.Receipt) : Option ReceiptRow := do
  let .ran occupancy _ result := r.exit | none
  let .ok (_, final) := result.erase | none
  some (if r.origin = CommittedRuns.Origin.dispatch then 0 else 1,
    r.activation.worker.index, occupancy, result.attempts,
    r.before.ambient.pendingWork, final.ambient.pendingWork,
    final.wg.device.map (fun d => d.encryptQueue.count))

def receiptCheck : Bool :=
  let result := CommittedRuns.Initialized.inspection trace false
  let enc := Worker.encryptWorker.index
  let dec := Worker.decryptWorker.index
  let rx := Worker.receiveWorker.index
  let tx := Worker.txWorker.index
  result.1.isOk && result.2.length == 8 &&
    result.2.filterMap receiptRow ==
      [(0,rx,1,2,[],[enc],some 1),
       (0,enc,1,2,[],[],some 0),
       (0,tx,1,2,[],[],some 0),
       (0,dec,1,1,[enc],[enc],some 1),
       (0,enc,1,1,[],[enc],some 1),
       (1,enc,1,2,[enc],[enc],some 0),
       (1,dec,0,1,[enc],[enc],some 0),
       (0,tx,2,3,[enc],[enc],some 0)]

def emptyRedispatchCheck : Bool :=
  match executeTrace emptyRedispatchTrace with
  | .error (op, .hidden message) =>
    op == 4 && message == "expected jiffies_end (site 128), the record is site 44"
  | _ => false

def reproduce : IO Unit := do
  unless boundaryCheck do
    throw (IO.userError "recorded pending identity: accepted boundary check failed")
  unless receiptCheck do
    throw (IO.userError "recorded pending identity: committed receipt sequence changed")
  unless emptyRedispatchCheck do
    throw (IO.userError "recorded pending identity: empty redispatch control changed")
  IO.println "Reproduced supplied-record acceptance with pending encrypt identity, empty packet queues, eight committed receipts, and refused empty redispatch"

#eval reproduce

end Leanux.Proofs.WG.Progress.RecordedPending
