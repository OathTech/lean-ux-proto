import Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshakeReceive

/-! Complete native handshake iterations connect to the campaign's shared
source driver. Endpoint state transport is independent from event chronology. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open OccurrenceStack TransmitSecurity

theorem iteration : Preserves (fun w : World => Ready locals active w.wg)
    (workerIter .receiveWorker none (liftWG receiveStep) (Env.condResched .receiveWorker)) := by
  let P := fun w : World => Ready locals active w.wg
  have next : Preserves P (liftWG receiveStep) :=
    PublicationPoll.native_product (Ready locals active) _ receive_step
  have need : Preserves P (Env.condResched .receiveWorker) :=
    OccurrenceDecrypt.product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  routing_tx_source [workerIter] using [next,need,ambient]

theorem shared {E : Type} {ρ : E → Option Nonce.Allocation} {hooks : Driver.Hooks E}
    (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Ready locals active w.wg) (h : List E)
    (run : (runPrefix (Driver.receiveIterObserved hooks) w h).1 = .ok (result,v)) :
    Ready locals active v.wg := by
  have projected := Driver.receiveIter_projects projects
  rw [Driver.nonce_receiveIterObserved_eq] at projected
  exact (hoare_iff_run _ _ _).mp iteration w result v before
    (DriverOwnership.product_native projected Nonce.receiveIterObserved_erases w v h run)

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
