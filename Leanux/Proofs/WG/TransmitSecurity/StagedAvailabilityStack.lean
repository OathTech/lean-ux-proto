import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilitySendTransport
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityReceiveTransport
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityProductFrames
import Leanux.Proofs.WG.TransmitSecurity.NonceStackFrames
import Leanux.Proofs.WG.AuthenticatedEffects.SendCallerContracts

/-! Actual stack replies and worker entry points preserve staged origins. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

theorem stack (bytes : List UInt8) : ProductSafe (Driver.stackObserved hooks bytes) :=
  stackReceiveWith_preserves (fun _ _ before => before.2) product_stable _
    (fun bytes => receive4With_preserves (fun _ _ before => before.2) product_stable _
      (fun dst reply => reply4With_preserves (fun _ _ before => before.2) product_stable _
        (fun family addr packets mtu => product_state (transmit_observed family addr packets mtu))
        dst reply) bytes) bytes

theorem stack_flush (packets : List (List UInt8)) : ProductSafe (Driver.stackFlushObserved hooks packets) := by
  induction packets with
  | nil => exact product_pure _
  | cons bytes rest ih =>
    simp only [Driver.stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact product_bind (stack bytes) (fun _ => ih)

theorem send_worker : ProductSafe (Driver.sendWorkerObserved hooks) :=
  SendCallers.one_preserves Carrier Safe (fun _ _ before => before.2) _
    (fun pid => (flushed_send_observed pid).consequence (fun _ _ _ before => before.1) (fun _ _ _ _ after => after))

theorem receive_iteration : ProductSafe (Driver.receiveIterObserved hooks) :=
  workerIterPrefix_preserves _ _ (fun _ _ before => before.2) (product_state handshake_observed)
    (product_store _ (condResched_sameKernel _))

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
