import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionHandshake

/-! The original handshake draining iteration retains active and suspended
TX service. Its send and keepalive subpaths have concrete native contracts;
no receive-worker callback hypothesis remains. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem handshake_receive_actor : Preserves (At (Covered locals crypt) crypt active) (liftWG WG.receiveStep) :=
  At.native (fun _=>serving_receive_step) TxSuspension.receive_step

theorem handshake_iteration : Preserves (At (Covered locals crypt) crypt active)
    (workerIter .receiveWorker none (liftWG WG.receiveStep) (Env.condResched .receiveWorker)) := by
  let P:=At (Covered locals crypt) crypt active
  have next:Preserves P (liftWG WG.receiveStep) := handshake_receive_actor
  have need:Preserves P (Env.condResched .receiveWorker) := actor_reschedule .receiveWorker
  have decision (d : Decision) (value : Bool) : Preserves P (Leanux.branch d value : Leanux.M Bool) := actor_branch d value
  change Preserves P _
  routing_tx_source [workerIter] using [next,need,decision]

end Leanux.Proofs.WG.RetirementSecurity.TxWork
