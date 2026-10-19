import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionNapi

/-! The native NAPI callback obligation is discharged by actual source proofs:
one transports fixed TX service, the other preserves suspended actor records.
Encryption and crypt-ahead therefore require no assumed callback contract. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem At.product {action : Leanux.M α}
    (service : ∀tx,Preserves (fun w:World=>Serving locals crypt tx w.wg) action)
    (suspension : SameView TxSuspension.suspended action) :
    Preserves (At (Covered locals crypt) crypt active) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have after:Serving locals crypt (active++actors w.ambient.suspended) v.wg :=
    (hoare_iff_run _ _ _).mp (service _) w result v before run
  have same:v.ambient.suspended=w.ambient.suspended :=
    (ProjectedAction.iff_run _ _ _).mp suspension w result v run
  simpa only [At,Serving,same] using after

theorem napi_actor : Preserves (At (Covered locals crypt) crypt active) Env.napiSoftirq :=
  At.product (fun _=>TxWorkNapi.softirq locals) TxSuspension.napi_softirq

theorem irq_exit_actor : Preserves (At (Covered locals crypt) crypt active) Env.napiIrqExit :=
  At.product (fun _=>TxWorkNapi.irqExit locals) TxSuspension.napi_irq_exit

theorem encrypt_iteration (before : At (Covered locals crypt) crypt tx w)
    (run : (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)).run w=
      .ok (result,v)) : At (Covered locals crypt) crypt tx v :=
  encrypt_iteration_service (fun _=>napi_actor) before run

theorem crypt_ahead (pid : PeerId) :
    Preserves (At (Covered locals crypt) crypt [pid]) (Env.cryptAhead pid) :=
  crypt_ahead_service (fun _=>napi_actor) pid

end Leanux.Proofs.WG.RetirementSecurity.TxWork
