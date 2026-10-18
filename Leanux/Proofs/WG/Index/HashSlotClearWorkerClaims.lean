import Leanux.Proofs.WG.Index.HashSlotClearWorkerEffects
import Leanux.Proofs.WG.Index.HashSlotClearWorkerSource
import Leanux.Proofs.WG.Index.HashSlotClearWorkerFrames
import Leanux.Proofs.WG.Index.HashSlotClearClaims
import Leanux.Proofs.WG.Index.HashSlotReleaseClaims
import Leanux.Proofs.WG.Index.HashSlotLookupFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceZeroWorkerClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceExpiryClaims
import Leanux.Proofs.WG.Index.FlushSource
import Leanux.Proofs.WG.Noise.ClearWorkerClaims
import Leanux.Proofs.WG.Keypairs.MaterialOrigin

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Actual normal handshake clearing retains coverage. NULL words and missing
peers remain original stopped paths, without readiness hypotheses. -/
theorem handshakeClear_hashSlots (pid : PeerId) :
    Campaign2.Ensures (handshakeClear pid) View.HashSlotsSafe
      (fun _ => View.HashSlotsSafe) := by
  intro g ambient result out after pre run
  cases device : g.dev with
  | none =>
    simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
      device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
        device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have clear : Ensures (handshakeClear pid) (fun g => g.dev = some d)
          (fun _ g => g.dev = some (Config.expiryZeroDevice d pid p)) := by
        simpa only [Config.expiryReadPrefix,requireNotPending,pure_bind] using
          Config.expiryReadPrefix_exact pid d p resident
      have finalDevice := clear g ambient result out after device run
      intro actual present
      change out.dev = some actual at present
      rw [finalDevice] at present
      cases present
      exact expiryZeroDevice_hashSlotCoverage d pid p resident (pre d device)

/-- The complete actual clear worker preserves both invariants on every normal
return. Entry residency, reference positivity and last-release slot coverage
are derived, not supplied; stopped paths remain unchanged. -/
theorem queuedExpiredZeroKeyMaterial_hashSlots_coherent (pid : PeerId) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid)
      (fun s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s) := by
  intro g ambient result out after pre run
  obtain ⟨d,p,device,resident,live⟩ := queuedClear_normal_entry pid g out ambient after result run
  have coherent := queuedExpiredZeroKeyMaterial_owner_coherent pid d p resident live
    (hashSlotCoverage_lastOwnerCovered d pid p resident (pre.2 d device) (pre.1 d device))
    g ambient result out after ⟨device,pre.2⟩ run
  refine ⟨?_,coherent⟩
  simp only [queuedExpiredZeroKeyMaterial,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨headValue,zero,zeroAmbient,headRun,keyValue,cleared,clearAmbient,keyRun,putRun⟩ := run
  cases headValue
  cases keyValue
  have zeroCoverage := handshakeClear_hashSlots pid g ambient () zero zeroAmbient pre.1 headRun
  have coverage := keypairsClear_hashSlots pid zero zeroAmbient () cleared clearAmbient zeroCoverage keyRun
  obtain ⟨before,peer,final,_,_,present,_,found⟩ :=
    keypairsClear_normal_cuts pid zero cleared zeroAmbient clearAmbient () keyRun
  have positive := (ClearWorker.peerPut_spec_clearTagMap_variant pid final
    (Config.emptyKeysPeer peer) found cleared clearAmbient result out after present putRun).1
  exact peerPut_hashSlots pid final (Config.emptyKeysPeer peer) found positive (fun _ => rfl)
    cleared clearAmbient result out after ⟨present,coverage⟩ putRun

/-- The original dequeue and section records wrap that same complete clear
worker; membership and successful dispatch are not entry assumptions. -/
theorem runFlushedClearWork_hashSlots_coherent (pid : PeerId) :
    Campaign2.Ensures (runFlushedClearWork pid)
      (fun s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s) := by
  intro g ambient result out after pre run
  let P : WGWorld → Prop := fun w =>
    View.HashSlotsSafe (Campaign2.snapshot w ambient) ∧
      View.OwnerCoherentSafe (Campaign2.snapshot w ambient)
  have dequeue : Ensures
      (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
      P (fun _ => P) := by
    intro w a value v b hi actual
    exact clearQueueErase_hashSlots_coherent pid w a value v b hi actual
  have worker : Ensures (queuedExpiredZeroKeyMaterial pid) P (fun _ => P) := by
    intro w a value v b hi actual
    exact queuedExpiredZeroKeyMaterial_hashSlots_coherent pid w a value v b hi actual
  exact runFlushedClearWork_preserves P pid dequeue worker g ambient result out after pre run

end Leanux.Proofs.WG.Index
