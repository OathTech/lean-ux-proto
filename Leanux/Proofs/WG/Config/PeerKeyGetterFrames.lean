import Leanux.Proofs.WG.Config.PeerKeyGetterModel
import Leanux.Proofs.WG.Config.KeyRequest

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- One quiet expiry/precomputation step preserves every resident peer's
readback and cursor fields, with no equality of the raw peer maps. -/
theorem peerUpdatedDevice_getter_frame (d : Device) (pid : PeerId) (p : Peer) (now : Int64)
    (resident : d.peers[pid]? = some p) :
    {peerUpdatedDevice d pid p now with peers := {}, keypairs := {}, indexTable := []} =
      {d with peers := {}, keypairs := {}, indexTable := []} ∧
    ∀ q : PeerId, ((peerUpdatedDevice d pid p now).peers[q]?).map keyGetterPeerView =
      (d.peers[q]?).map keyGetterPeerView := by
  constructor
  · have invalidated (base : Device) (kp : Option KeypairId) :
        {invalidateDevice base kp with peers := {}, keypairs := {}, indexTable := []} =
          {base with peers := {}, keypairs := {}, indexTable := []} := by
      cases kp with
      | none => rfl
      | some id => cases found : base.keypairs[id]? <;> simp [invalidateDevice, found]
    unfold peerUpdatedDevice expiredDevice
    rw [invalidated, invalidated]
    cases has : d.staticIdentity.hasIdentity <;>
      cases nonNull : (curve25519 d.staticIdentity.staticPrivate p.remoteStatic).2
    all_goals simp only [expiryHeadDevice, withPeer, precomputeDevice, has, nonNull, Bool.false_eq_true, ↓reduceIte]
    all_goals rfl
  · intro q
    by_cases same : q = pid
    · subst q
      rw [peerUpdatedDevice_peer, resident]
      rfl
    · simp [peerUpdatedDevice, expiredDevice, invalidateDevice_peers, expiryHeadDevice,
        withPeer, Std.TreeMap.getElem?_insert, Ne.symm same,
        precomputeDevice_other pid q d p same]

/-- Ordered actual observations retain each occurrence's own expiry witness.
Only the readback projection is framed; index/key stores and handshake data change. -/
theorem observedKeyPeerRun_getter_frame (d final : Device) (pids : List PeerId)
    (observations : List (Option (Int64 × Option Bool)))
    (run : ObservedKeyPeerRun false d pids observations final) :
    {final with peers := {}, keypairs := {}, indexTable := []} =
      {d with peers := {}, keypairs := {}, indexTable := []} ∧
    ∀ q : PeerId, (final.peers[q]?).map keyGetterPeerView = (d.peers[q]?).map keyGetterPeerView := by
  induction run with
  | nil => exact ⟨rfl, fun _ => rfl⟩
  | cons d pid p observation step next rest observations final resident effect device tail ih =>
    obtain ⟨now, effect⟩ := effect
    simp only [Bool.false_eq_true, ↓reduceIte] at effect
    have nextEq : next = peerUpdatedDevice d pid p now :=
      Option.some.inj (device.symm.trans effect.2)
    subst next
    have head := peerUpdatedDevice_getter_frame d pid p now resident
    exact ⟨ih.1.trans head.1, fun q => (ih.2 q).trans (head.2 q)⟩

/-- The total readback view uses actual final residents for every original
list occurrence; its fallback is unreachable on that listed domain. -/
theorem keyGetterPeers_frame (base current : Device) (peers : PeerId → Peer)
    (same : ∀ q : PeerId, (current.peers[q]?).map keyGetterPeerView = (base.peers[q]?).map keyGetterPeerView)
    (residents : ∀ q ∈ base.peerList, base.peers[q]? = some (peers q)) :
    (∀ q ∈ base.peerList, current.peers[q]? = some (keyGetterPeers base current peers q)) ∧
      ∀ q, keyGetterPeerView (keyGetterPeers base current peers q) = keyGetterPeerView (peers q) := by
  have present (q : PeerId) (resident : base.peers[q]? = some (peers q)) :
      ∃ p, current.peers[q]? = some p ∧ keyGetterPeerView p = keyGetterPeerView (peers q) := by
    apply Option.map_eq_some_iff.mp
    rw [same q, resident]
    rfl
  constructor
  · intro q member
    have resident := residents q member
    obtain ⟨p, found, _⟩ := present q resident
    simp only [keyGetterPeers, member, ite_true, found, Option.getD_some]
  · intro q
    by_cases member : q ∈ base.peerList
    · obtain ⟨p, found, equal⟩ := present q (residents q member)
      simpa only [keyGetterPeers, member, ite_true, found, Option.getD_some] using equal
    · simp only [keyGetterPeers, member, ite_false]

end Leanux.Proofs.WG.Config
