import Leanux.Proofs.WG.Config.AllowedTransferRequestSource
import Leanux.Proofs.WG.Config.AllowedRoundTripSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- Two actual peer dumps share the original evolving buffer and context. The
first empty-list dump resets the sequence before the destination reads its node. -/
theorem transfer_paired_readback (v4 : Bool) (d : Device) (id : NodeId) (addr cidr : Nat)
    (parent : Slot) (donor target : PeerId) (oldPeer newPeer : Peer)
    (ctx : DumpCtx) (skb : NlSkb)
    (different : donor ≠ target) (width : cidr ≤ allowedBits v4)
    (root : allowedRootValue v4 d = some id)
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) (some donor) with parent })
    (oldResident : d.peers[donor]? = some oldPeer) (newResident : d.peers[target]? = some newPeer)
    (oldOnly : listRemove oldPeer.allowedipsList id = []) (newEmpty : newPeer.allowedipsList = [])
    (fresh : ctx.nextAllowedip = none)
    (room : 340 + allowedIpSpace (allowedFamily v4) ≤ skb.room) :
    Returns (do
      let ret ← setAllowedip target (allowedAttrs v4 addr cidr)
      let first ← getPeerDump donor ctx skb
      let second ← getPeerDump target first.2.1 first.1
      pure (ret, first.2.2, second))
      (fun w => w.k.wg = some d)
      (fun result w => w.k.wg = some
          (transferRequestDevice d id { newNode addr cidr (allowedBits v4) (some donor) with parent } target newPeer) ∧
        result = (0,
          PeerDump.complete { publicKey := hexKey oldPeer.remoteStatic, attrs := peerFixedAttrs oldPeer },
          { skb with room := skb.room - (peerFixedSpace oldPeer + peerFixedSpace newPeer + 4 + allowedIpSpace (allowedFamily v4)) },
          { ctx with nextAllowedip := none, allowedipsSeq := 0 },
          PeerDump.complete { publicKey := hexKey newPeer.remoteStatic, attrs := peerFixedAttrs newPeer ++
            [("allowed_ips", Json.arr #[allowedJson v4 addr cidr])] })) := by
  let n := { newNode addr cidr (allowedBits v4) (some donor) with parent }
  let updated := transferRequestDevice d id n target newPeer
  let old := eraseListedPeer id oldPeer
  let next := transferredPeer id newPeer
  have ho : updated.peers[donor]? = some old := by
    simp [updated, transferRequestDevice, transferRootDevice_peers, different,
      insertSequenceDevice, oldResident, old]
  have ht : updated.peers[target]? = some next := by
    simp [updated, transferRequestDevice, transferRootDevice_peers, next]
  have hn : updated.nodes[id]? = some { newNode addr cidr (allowedBits v4) (some target) with parent } := by
    simp [updated, transferRequestDevice, transferRootDevice, deleteListedNodes_nodes, n, newNode]
  have oldRoom : peerFixedSpace old ≤ 168 := by
    unfold peerFixedSpace
    split <;> (try split) <;> omega
  have hs := setAllowedip_root_transfer v4 d id addr cidr (some donor) parent target newPeer width root node newResident
  intro initial hd
  obtain ⟨ret, afterSet, setRun, hret, hdev⟩ := hs initial hd
  subst ret
  obtain ⟨first, afterFirst, firstRun, firstDev, firstResult⟩ :=
    getPeerDump_empty_device updated donor old ctx skb ho oldOnly fresh (by omega) afterSet hdev
  subst first
  obtain ⟨second, final, secondRun, finalDev, secondResult⟩ :=
    getPeerDump_single v4 updated next id target addr cidr parent
      { ctx with nextAllowedip := none, allowedipsSeq := 0 }
      { skb with room := skb.room - peerFixedSpace old }
      ht (by simp [next, transferredPeer, newEmpty, listRemove]) hn rfl (Or.inl rfl)
      (by dsimp; omega) afterFirst firstDev
  refine ⟨(0, PeerDump.complete { publicKey := hexKey old.remoteStatic, attrs := peerFixedAttrs old }, second), final, ?_, ?_⟩
  · simp only [StateT.run_bind, setRun]
    change ((getPeerDump donor ctx skb).run afterSet >>= fun a =>
      ((fun b => ((0, a.1.2.2, b.1), b.2)) <$>
        (getPeerDump target a.1.2.1 a.1.1).run a.2)) = _
    rw [firstRun]
    change ((fun b => ((0, PeerDump.complete { publicKey := hexKey old.remoteStatic, attrs := peerFixedAttrs old }, b.1), b.2)) <$>
      (getPeerDump target { ctx with nextAllowedip := none, allowedipsSeq := 0 }
        { skb with room := skb.room - peerFixedSpace old }).run afterFirst) = _
    rw [secondRun]
    rfl
  · refine ⟨finalDev, ?_⟩
    simp [secondResult, old, next, eraseListedPeer, transferredPeer, peerFixedSpace,
      peerFixedAttrs, Nat.sub_sub, Nat.add_assoc]

end Leanux.Proofs.WG.Config
