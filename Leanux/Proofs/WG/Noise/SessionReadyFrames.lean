import Leanux.Proofs.WG.Noise.SessionReadyModel
import Leanux.Proofs.WG.Index.SessionCoherenceFrames

/-! Pure transport of the static release budget and handshake index membership
through the original preparation and rotation effects. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

theorem sessionPrepared_ready (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (birth : Int64) (ready : SessionReady d p counter) :
    ClearReady (sessionPrepared pid d p counter birth)
      (rotationReleases (rotationPlan (sessionZeroPeer p)
        (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId)) := by
  intro id count
  obtain ⟨k, resident, word, refs⟩ := ready id count
  by_cases same : id = d.nextKeypairId
  · subst id
    simp only [Index.createdDevice, Std.TreeMap.getElem?_insert_self, Option.some.injEq] at resident
    subst k
    refine ⟨sessionDerivedKey
      (sessionAssignedKey { internalId := counter + 1, peer := p.handshakeEntryPeer } p p.handshakeState)
      (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth, ?_, ?_, ?_⟩
    · simp [sessionPrepared, sessionDerivedDevice]
    · by_cases role : p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE <;>
        simpa [sessionDerivedKey, sessionAssignedKey, role] using word
    · by_cases role : p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE <;>
        simpa [sessionDerivedKey, sessionAssignedKey, role] using refs
  · refine ⟨k, ?_, word, refs⟩
    simpa [sessionPrepared, sessionDerivedDevice, Std.TreeMap.getElem?_insert, same,
      Ne.symm same] using resident

theorem rotationRun_handshake_hashed {pid : PeerId} {d final : Device}
    {actions : List RotationAction} (steps : RotationRun pid d actions final)
    (owner : PeerId) (hashed : d.indexTable.any (·.owner == .handshake owner) = true) :
    final.indexTable.any (·.owner == .handshake owner) = true := by
  obtain ⟨entry, member, matching⟩ := List.any_eq_true.mp hashed
  have same : entry.owner = .handshake owner := by simpa using matching
  apply List.any_eq_true.mpr
  refine ⟨{index := entry.index, owner := .handshake owner}, ?_, by simp⟩
  apply (Index.rotationRun_handshake_mem steps owner entry.index).mpr
  cases entry with
  | mk index tag =>
    simp only at same
    subst tag
    exact member

end Leanux.Proofs.WG.Noise
