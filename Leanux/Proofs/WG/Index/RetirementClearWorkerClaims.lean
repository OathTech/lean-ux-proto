import Leanux.Proofs.WG.Index.RetirementRetentionClaims
import Leanux.Proofs.WG.Index.HashSlotClearWorkerSource
import Leanux.Proofs.WG.Index.RetirementClearWorkerEffects
import Leanux.Proofs.WG.Index.RetirementClearWorkerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise
open Queues.RxCredits

/-- The complete original clear worker retains the supplied retirement
obligations on normal returns. Residency and final-payment positivity are
derived from that same execution, without readiness or funding assumptions. -/
theorem queuedExpiredZeroKeyMaterial_retirement (retired : Reservations) (pid : PeerId) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid) (View.RetirementSafe retired)
      (fun _ => View.RetirementSafe retired) := by
  intro g ambient result out after pre run
  obtain ⟨d,p,device,resident,_⟩ := queuedClear_normal_entry pid g out ambient after result run
  simp only [queuedExpiredZeroKeyMaterial,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨headValue,zero,zeroAmbient,headRun,keyValue,cleared,clearAmbient,keyRun,putRun⟩ := run
  cases headValue
  cases keyValue
  have clear : Ensures (handshakeClear pid) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (Config.expiryZeroDevice d pid p)) := by
    simpa only [Config.expiryReadPrefix,requireNotPending,pure_bind] using
      Config.expiryReadPrefix_exact pid d p resident
  have zeroDevice := clear g ambient () zero zeroAmbient device headRun
  have zeroReserved : View.RetirementSafe retired (Campaign2.snapshot zero zeroAmbient) := by
    intro actual present
    change zero.dev = some actual at present
    rw [zeroDevice] at present
    cases present
    exact expiryZeroDevice_deadHashedReserved retired d pid p resident (pre d device)
  have reserved := keypairsClear_retirement retired pid zero zeroAmbient ()
    cleared clearAmbient zeroReserved keyRun
  obtain ⟨before,peer,final,_,_,present,_,found⟩ :=
    keypairsClear_normal_cuts pid zero cleared zeroAmbient clearAmbient () keyRun
  have positive := (ClearWorker.peerPut_spec_clearTagMap_variant pid final
    (Config.emptyKeysPeer peer) found cleared clearAmbient result out after present putRun).1
  exact peerPut_retirement retired pid final (Config.emptyKeysPeer peer) found positive
    cleared clearAmbient result out after ⟨present,reserved⟩ putRun

/-- The actual flushed-clear wrapper adds dequeue and section records around
the same worker. The sole entry invariant is the retirement obligation. -/
theorem runFlushedClearWork_retirement (retired : Reservations) (pid : PeerId) :
    Campaign2.Ensures (runFlushedClearWork pid) (View.RetirementSafe retired)
      (fun _ => View.RetirementSafe retired) := by
  intro g ambient result out after pre run
  let P : WGWorld → Prop := fun w => View.RetirementSafe retired (Campaign2.snapshot w ambient)
  have dequeue : Ensures
      (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
      P (fun _ => P) := by
    intro w a value v b hi actual
    exact clearQueueErase_retirement retired pid w a value v b hi actual
  have worker : Ensures (queuedExpiredZeroKeyMaterial pid) P (fun _ => P) := by
    intro w a value v b hi actual
    exact queuedExpiredZeroKeyMaterial_retirement retired pid w a value v b hi actual
  exact runFlushedClearWork_preserves P pid dequeue worker g ambient result out after pre run

end Leanux.Proofs.WG.Index
