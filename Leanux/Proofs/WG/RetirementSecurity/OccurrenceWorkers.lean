import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTx
import Leanux.Proofs.WG.TransmitSecurity.DriverWorkersProjection

/-! Native encryption, TX disposal and decryption iterations connect to the
same shared campaign driver through its exact source projection. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceWorkers
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open OccurrenceStack TransmitSecurity
variable {E : Type} {ρ : E → Option Nonce.Allocation} {hooks : Driver.Hooks E}

theorem encrypt (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Ready locals active w.wg)  (h : List E)
    (run : (runPrefix (Driver.encryptIterObserved hooks) w h).1 = .ok (result,v)) :
    Ready locals active v.wg := by
  have projected := Driver.encryptIter_projects projects
  rw [Driver.nonce_encryptIterObserved_eq] at projected
  exact (hoare_iff_run _ _ _).mp (OccurrenceEncrypt.iteration) w result v before
    (DriverOwnership.product_native projected (Nonce.encryptIterObserved_erases) w v h run)

theorem decrypt (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Ready locals active w.wg)  (h : List E)
    (run : (runPrefix (Driver.decryptIterObserved hooks) w h).1 = .ok (result,v)) :
    Ready locals active v.wg := by
  have projected := Driver.decryptIter_projects projects
  rw [Driver.nonce_decryptIterObserved_eq] at projected
  exact (hoare_iff_run _ _ _).mp (OccurrenceDecrypt.iteration) w result v before
    (DriverOwnership.product_native projected (Nonce.decryptIterObserved_erases) w v h run)

theorem tx (projects : Driver.HooksProjects ρ hooks Driver.nonceHooks)
    (before : Ready locals active w.wg) (pid : PeerId) (h : List E)
    (run : (runPrefix (Driver.txIterObserved hooks pid) w h).1 = .ok (result,v)) :
    Ready locals active v.wg := by
  have projected := Driver.txIter_projects projects pid
  rw [Driver.nonce_txIterObserved_eq] at projected
  exact (hoare_iff_run _ _ _).mp (OccurrenceTx.iteration pid) w result v before
    (DriverOwnership.product_native projected (Nonce.txIterObserved_erases pid) w v h run)

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceWorkers
