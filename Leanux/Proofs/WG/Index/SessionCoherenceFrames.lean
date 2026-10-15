import Leanux.Proofs.WG.Index.SessionCoherenceModel
import Leanux.Proofs.WG.Noise.RotationEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem clearPut_other_key {key : Option KeypairId} {d final : Device}
    (release : ClearPut key d final) (id : KeypairId)
    (excluded : key ≠ some id) :
    final.keypairs[id]? = d.keypairs[id]? := by
  cases release with
  | null => rfl
  | present d other k resident live word =>
    apply released_other_keypair
    intro same
    exact excluded (congrArg some same)

theorem rotationRun_excluded_key {pid : PeerId} {d final : Device}
    {actions : List RotationAction} (steps : RotationRun pid d actions final)
    (id : KeypairId) (excluded : some id ∉ rotationReleases actions) :
    final.keypairs[id]? = d.keypairs[id]? := by
  revert excluded
  induction steps with
  | nil => intro _; rfl
  | write d final change p rest resident tail ih =>
    intro excluded
    have restExcluded : some id ∉ rotationReleases rest := by
      simpa only [rotationReleases] using excluded
    simpa only [rotationWriteDevice] using ih restExcluded
  | put d middle final key rest release tail ih =>
    intro excluded
    have different : key ≠ some id := by
      intro same
      apply excluded
      simp [rotationReleases, same]
    have restExcluded : some id ∉ rotationReleases rest := by
      intro member
      apply excluded
      simp [rotationReleases, member]
    rw [ih restExcluded, clearPut_other_key release id different]

theorem clearPut_handshake_mem {key : Option KeypairId} {d final : Device}
    (release : ClearPut key d final) (pid : PeerId) (index : Nat) :
    ({ index, owner := IndexOwner.handshake pid } ∈ final.indexTable) ↔
      { index, owner := IndexOwner.handshake pid } ∈ d.indexTable := by
  cases release with
  | null => rfl
  | present d other k resident live word =>
    rw [released_table]
    simp [removeOwner]

theorem rotationRun_handshake_mem {pid : PeerId} {d final : Device}
    {actions : List RotationAction} (steps : RotationRun pid d actions final)
    (owner : PeerId) (index : Nat) :
    ({ index, owner := IndexOwner.handshake owner } ∈ final.indexTable) ↔
      { index, owner := IndexOwner.handshake owner } ∈ d.indexTable := by
  induction steps with
  | nil => rfl
  | write d final change p rest resident tail ih => exact ih
  | put d middle final key rest release tail ih =>
    exact ih.trans (clearPut_handshake_mem release owner index)

end Leanux.Proofs.WG.Index
