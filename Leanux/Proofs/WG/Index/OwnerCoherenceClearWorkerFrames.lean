import Leanux.Proofs.WG.Index.OwnerCoherenceZeroWorkerClaims
import Leanux.Proofs.WG.TimerDiscipline.SectionFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Queue removal changes no owner, resident, reference count or slot. -/
theorem clearDequeue_owner_conditions (d : Device) (pid : PeerId) (p : Peer)
    (safe : HashedOwnersCoherent d) (covered : LastOwnerCovered d pid p) :
    HashedOwnersCoherent {d with clearWorkQueue := d.clearWorkQueue.erase pid} ∧
    LastOwnerCovered {d with clearWorkQueue := d.clearWorkQueue.erase pid} pid p := by
  exact ⟨safe, covered⟩

/-- Section inputs may stop, but cannot change the worker's owner obligations. -/
theorem clearWorkerSection_owner_coherent (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (covered : LastOwnerCovered d pid p) :
    Noise.Product.Ensures
      (Env.runWorker .clearPeerWorker (liftWG (queuedExpiredZeroKeyMaterial pid)))
      (fun w => w.wg.dev = some d ∧ ∀ current, w.wg.dev = some current → HashedOwnersCoherent current)
      (fun _ w => ∀ current, w.wg.dev = some current → HashedOwnersCoherent current) := by
  have body : Noise.Product.Ensures (liftWG (queuedExpiredZeroKeyMaterial pid))
      (fun w => w.wg.dev = some d ∧ ∀ current, w.wg.dev = some current → HashedOwnersCoherent current)
      (fun _ w => ∀ current, w.wg.dev = some current → HashedOwnersCoherent current) := by
    intro initial result final pre run
    change (((queuedExpiredZeroKeyMaterial pid).run initial.wg).run initial.ambient >>=
      fun ((value,g),a) => Except.ok (value,{initial with wg := g,ambient := a})) = _ at run
    cases actual : ((queuedExpiredZeroKeyMaterial pid).run initial.wg).run initial.ambient with
    | error stop => rw [actual] at run; cases run
    | ok pair =>
      obtain ⟨⟨value,g⟩,a⟩ := pair
      rw [actual] at run
      cases run
      exact queuedExpiredZeroKeyMaterial_owner_coherent pid d p resident live covered
        initial.wg initial.ambient result g a pre actual
  exact (Noise.Product.ensures_iff _ _ _).mpr
    (TimerDiscipline.runWorker_kernel_contract .clearPeerWorker _
      (fun g _ _ _ => g.dev = some d ∧ ∀ current, g.dev = some current → HashedOwnersCoherent current)
      (fun g _ _ _ => ∀ current, g.dev = some current → HashedOwnersCoherent current)
      ((Noise.Product.ensures_iff _ _ _).mp body))

end Leanux.Proofs.WG.Index
