import Leanux.Proofs.WG.Config.MixedPeerModel

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do Lean

/-- Selected-peer and trie facts from the exact ordered device transform.
This says nothing about ownership consistency of other nodes or peer lists. -/
theorem mixedPeerEffect_readback (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (psk : Key) (interval addr cidr : Nat) (bad : Bool) (ret : Int) (final : Device)
    (effect : MixedPeerEffect v4 d pid p psk interval addr cidr bad ret final) :
    ∃ inserted : Bool,
      ret = (if inserted then (if bad then -EINVAL else 0) else -ENOMEM) ∧
      final.peers[pid]? = some (mixedPeerReadback p psk interval d.nextNode bad inserted) ∧
      (inserted = true → final.nodes[d.nextNode]? = some
        {newNode addr cidr (allowedBits v4) (some pid) with parent := allowedRoot v4}) ∧
      final.peerAllowedips.seq = d.peerAllowedips.seq + 1 := by
  rcases effect with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨false, rfl, ?_, ?_, rfl⟩
    · simp [mixedPeerExit, mixedPeerBase, mixedPeerKeyed, mixedPeerReadback,
        withPeer, insertSequenceDevice]
    · intro impossible; cases impossible
  · refine ⟨true, rfl, ?_, ?_, ?_⟩
    · cases bad <;> simp [mixedPeerExit, mixedPeerBase, mixedPeerKeyed, mixedPeerReadback,
        withPeer, insertSequenceDevice, emptyRootInserted]
    · intro _
      cases bad <;> simp [mixedPeerExit, withPeer, emptyRootInserted, insertSequenceDevice,
        mixedPeerBase]
    · cases bad <;> cases v4 <;> rfl

end Leanux.Proofs.WG.Config
