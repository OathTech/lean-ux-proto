import Leanux.Proofs.WG.Config.MultipartFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem multipart_getNode (id : NodeId) (d : Device) (n : AipNode)
    (resident : d.nodes[id]? = some n) :
    ⦃fun g => ⌜g.dev = some d⌝⦄ liftAip (getNode id)
    ⦃⇓ q g => ⌜g.dev = some d ∧ q = n⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient device
  refine ⟨n, {g with dev := some d}, ambient, ?_, rfl, rfl⟩
  simp [liftAip, getNode, getDev, modifyDev, device, resident]
  rfl

theorem dumpTail_resume_source (p : Peer) (b : NodeId) (ctx : DumpCtx) (skb : NlSkb)
    (cursor : ctx.nextAllowedip = some b) (room : 72 ≤ skb.room) :
    getPeerDumpTailSource p ctx skb = (do
      _ ← branch .getPeerNoNest false
      _ ← branch .getPeerPubkeyFail false
      _ ← branch .getPeerFirst false
      getPeerDumpAllowedSource p ctx skb { skb with room := skb.room - 40 }
        (hexKey p.remoteStatic) [("public_key", toJson (hexKey p.remoteStatic))] (some b)) := by
  have r4 : ¬ skb.room < 4 := by omega
  have r40 : ¬ skb.room - 4 < 36 := by omega
  funext g ambient
  simp [getPeerDumpTailSource, cursor, NlSkb.put, nlaTotal, r4, r40, Nat.sub_sub,
    branch, AmbientM.branch]


theorem coalesce_multipart (d : Device) (p : Peer) (addr₁ cidr₁ addr₂ cidr₂ : Nat)
    (endpoint : p.endpoint = none) :
    coalesce [.data 2 (deviceFixedAttrs d) (some [multipartFirst p addr₁ cidr₁]),
      .data 2 [] (some [multipartLast p addr₂ cidr₂]), .done 2 0] =
      pure (.ok (multipartJson d p addr₁ cidr₁ addr₂ cidr₂)) := by
  have hn : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
  simp [coalesce, multipartFirst, multipartLast, multipartJson, peerFixedAttrs, endpoint,
    hn, List.forIn_cons, List.forIn_nil, bind_assoc, List.lookup]


theorem multipart_getter_returns (pid : PeerId) (d : Device) (p : Peer)
    (ctx : DumpCtx) (skb : NlSkb) (expected : PeerDumpResult)
    (resident : d.peers[pid]? = some p)
    (tail : Returns (getPeerDumpTailSource p ctx skb) (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result = expected)) :
    Returns (getPeerDump pid ctx skb) (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result = expected) := by
  have hg : Returns (getPeer pid) (fun g => g.dev = some d)
      (fun result g => result = p ∧ g.dev = some d) := by
    intro g ambient device
    refine ⟨p, g, ambient, ?_, rfl, device⟩
    simp [getPeer, getDev, device, resident]
    rfl
  rw [getPeerDump_source]
  refine returns_bind _ _ hg ?_
  intro q g ambient pre
  obtain ⟨rfl, device⟩ := pre
  exact tail g ambient device

end Leanux.Proofs.WG.Config
