import Leanux.Proofs.WG.Index.OwnerCoherenceClearWorkerFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceClearWorkerSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- The real dispatcher preserves owner coherence with coverage required only
for its actual named/head peer. Selection, section and body refusals remain
partial errors; no queue-wide coverage or readiness is assumed. -/
theorem runOneClearWorker_owner_coherent :
    Campaign2.Product.Ensures Env.runOneClearWorker ClearWorkerOwnerEntry
      (fun _ s => View.OwnerCoherentSafe s.toSnapshot) := by
  intro initial result final pre run
  rw [runOneClearWorker_select_source,StateT.run_bind] at run
  cases selection : clearWorkerSelect.run initial with
  | error stop => rw [selection] at run; cases run
  | ok pair =>
    obtain ⟨pid,middle⟩ := pair
    rw [selection] at run
    change ((do
      modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}
      Env.runWorker .clearPeerWorker (queuedExpiredZeroKeyMaterial pid) : Leanux.M Unit).run middle) = _ at run
    obtain ⟨same,selected,queued⟩ := clearWorkerSelect_selected initial middle pid selection
    obtain ⟨d,p,device,resident,live,covered⟩ := pre.2 pid selected
    have current : middle.wg.dev = some d := same ▸ device
    let removed : Device := {d with clearWorkQueue := d.clearWorkQueue.erase pid}
    let next : World := {middle with wg := {middle.wg with dev := some removed}}
    have dequeue : (modifyDev (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) :
        Leanux.M Unit).run middle = .ok ((),next) := by
      change Except.ok ((),{middle with wg := {middle.wg with dev := middle.wg.dev.map _}}) = _
      rw [current]
      rfl
    rw [StateT.run_bind,dequeue] at run
    have conditions := clearDequeue_owner_conditions d pid p (pre.1 d device) covered
    have safe : ∀ current, next.wg.dev = some current → HashedOwnersCoherent current := by
      intro current found
      change some removed = some current at found
      cases found
      exact conditions.1
    exact clearWorkerSection_owner_coherent pid removed p resident live conditions.2
      next result final ⟨rfl,safe⟩ run

end Leanux.Proofs.WG.Index
