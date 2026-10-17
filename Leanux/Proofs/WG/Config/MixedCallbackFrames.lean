import Leanux.Proofs.WG.Config.MixedPageScanModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The mixed serializer loop preserves the held peer cursor stored in the
context through every complete, split and cancelled branch. Other fields and
the separate next-peer cursor retain their modeled updates. -/
theorem mixedPeerScan_oldCursor (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
    (skb : NlSkb) (prior : Array PeerDumpAttrs) :
    (mixedPeerScan d peers nodes rows ctx cursor skb prior).native.1.nextPeer = ctx.nextPeer := by
  have one (p : Peer) (c : DumpCtx) (s : NlSkb) (ids : List NodeId) :
      (weightedPeerResult d nodes p c s ids).2.1.nextPeer = c.nextPeer := by
    let cost := if c.nextAllowedip.isNone then peerFixedSpace p else 40
    let attrs := if c.nextAllowedip.isNone then peerFixedAttrs p else [("public_key",toJson (hexKey p.remoteStatic))]
    change (if cost ≤ s.room then
      weightedAllowedResult d nodes c s {s with room := s.room-cost} (hexKey p.remoteStatic) attrs ids
      else (s,c,.cancelled)).2.1.nextPeer = c.nextPeer
    by_cases fits : cost ≤ s.room
    · simp only [ite_eq_left fits]
      cases ids with
      | nil => rfl
      | cons id ids =>
        simp only [weightedAllowedResult]
        split
        · rfl
        · split <;> rfl
    · simp only [ite_eq_right fits]

  induction rows generalizing ctx cursor skb prior with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨pid,ids⟩ := row
    have preserved := one (peers pid) ctx skb ids
    cases outcome : weightedPeerResult d nodes (peers pid) ctx skb ids with
    | mk out rest =>
      obtain ⟨after,verdict⟩ := rest
      simp only [outcome] at preserved
      cases verdict with
      | complete attrs =>
        simpa only [mixedPeerScan,outcome] using
          (ih after (some pid) out (prior.push attrs)).trans preserved
      | split attrs => simpa only [mixedPeerScan,outcome] using preserved
      | cancelled => simpa only [mixedPeerScan,outcome] using preserved

end Leanux.Proofs.WG.Config
