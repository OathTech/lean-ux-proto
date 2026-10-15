import Leanux.Proofs.WG.Index.SessionCoherenceFrames

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem table_field_injective {α : Type} (field : IndexEntry → α)
    {table : List IndexEntry} (unique : table.Pairwise (fun a b => field a ≠ field b))
    {a b : IndexEntry} (ha : a ∈ table) (hb : b ∈ table) (same : field a = field b) :
    a = b := by
  induction table generalizing a b with
  | nil => simp at ha
  | cons head rest ih =>
    obtain ⟨apart, tail⟩ := List.pairwise_cons.mp unique
    rcases List.mem_cons.mp ha with ah | ar
    · rcases List.mem_cons.mp hb with bh | br
      · exact ah.trans bh.symm
      · rw [ah] at same
        exact False.elim (apart b br same)
    · rcases List.mem_cons.mp hb with bh | br
      · rw [bh] at same
        exact False.elim (apart a ar same.symm)
      · exact ih tail ar br same

theorem sessionEffect_installed (pid : PeerId) (d : Device) (p : Peer)
    (counter finalCounter : Nat) (final : Device)
    (self : p.handshakeEntryPeer = some pid)
    (fresh : SessionRotationFresh p d.nextKeypairId)
    (safe : DeviceTablesSafe final)
    (effect : SessionEffect pid d p counter true final finalCounter) :
    SessionInstalled pid d p final := by
  obtain ⟨state, alive, word, count, birth, rotated, steps, hashed, rfl⟩ := effect
  let key := sessionDerivedKey
    (sessionAssignedKey { internalId := counter + 1, peer := p.handshakeEntryPeer } p p.handshakeState)
    (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth
  have excluded : some d.nextKeypairId ∉ rotationReleases
      (rotationPlan (sessionZeroPeer p) (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId) := by
    have plan : rotationPlan (sessionZeroPeer p)
        (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId =
        rotationPlan p (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId := rfl
    rw [plan]
    exact fresh
  have keyResident : rotated.keypairs[d.nextKeypairId]? = some key := by
    rw [rotationRun_excluded_key steps d.nextKeypairId excluded]
    simp [sessionPrepared, sessionDerivedDevice, createdDevice, key]
  have keyPeer : key.peer = some pid := by
    simp [key, sessionDerivedKey, sessionAssignedKey, self]
    split <;> rfl
  have keyCount : key.refcount = 1 := by
    simp [key, sessionDerivedKey, sessionAssignedKey]
    split <;> rfl
  have caller := rotationRun_peer steps (sessionZeroPeer p)
    (by simp [sessionPrepared])
  have slot :
      (if p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE then
        (rotationPeer (rotationPlan (sessionZeroPeer p)
          (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId) (sessionZeroPeer p)).keypairCurrent
      else (rotationPeer (rotationPlan (sessionZeroPeer p)
          (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId) (sessionZeroPeer p)).keypairNext)
        = some d.nextKeypairId := by
    by_cases role : p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE <;>
      by_cases pending : p.keypairNext.isSome = true <;>
      simp [rotationPlan, rotateWithNext, rotateWithoutNext, rotateResponder,
        rotationPeer, RotationWrite.apply, role, pending, sessionZeroPeer]
  obtain ⟨entry, member, owner⟩ := List.any_eq_true.mp hashed
  have own : entry.owner = .handshake pid := by simpa using owner
  have old : { index := entry.index, owner := IndexOwner.handshake pid } ∈ d.indexTable := by
    have he : entry = { index := entry.index, owner := IndexOwner.handshake pid } := by
      cases entry; simp_all
    rw [he] at member
    exact (rotationRun_handshake_mem steps pid entry.index).mp member
  have published : { index := entry.index, owner := IndexOwner.keypair d.nextKeypairId } ∈
      replaceOwner pid d.nextKeypairId rotated.indexTable := by
    apply List.mem_map.mpr
    refine ⟨entry, member, ?_⟩
    simp [own]
  refine ⟨key, _, entry.index, keyResident, keyPeer, keyCount, caller, slot, old, published, ?_⟩
  intro other present
  constructor
  · intro indexEq
    have same := table_field_injective IndexEntry.index safe.1 present published indexEq
    simpa only using congrArg IndexEntry.owner same
  · intro ownerEq
    have same := table_field_injective IndexEntry.owner safe.2.1 present published ownerEq
    simpa only using congrArg IndexEntry.index same

end Leanux.Proofs.WG.Index
