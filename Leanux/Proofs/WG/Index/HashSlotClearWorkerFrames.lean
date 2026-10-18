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

/-- Removing one queued clear occurrence changes no hashed owner or key slot. -/
theorem clearQueueErase_hashSlots_coherent (pid : PeerId) :
    Campaign2.Ensures
      (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
      (fun s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s) := by
  intro w a value v b hi actual
  cases actual
  constructor
  · intro d found
    change (w.dev.map fun old => {old with clearWorkQueue := old.clearWorkQueue.erase pid}) = some d at found
    cases device : w.dev with
    | none => simp [device] at found
    | some old =>
      simp only [device,Option.map_some,Option.some.injEq] at found
      subst d
      exact hi.1 old device
  · intro d found
    change (w.dev.map fun old => {old with clearWorkQueue := old.clearWorkQueue.erase pid}) = some d at found
    cases device : w.dev with
    | none => simp [device] at found
    | some old =>
      simp only [device,Option.map_some,Option.some.injEq] at found
      subst d
      exact hi.2 old device


end Leanux.Proofs.WG.Index
