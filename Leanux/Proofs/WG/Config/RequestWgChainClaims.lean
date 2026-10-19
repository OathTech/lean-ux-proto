import Leanux.Proofs.WG.Config.RequestWgChainSource

/-! Projected WG adjacency derived from the unchanged whole-request certificate. A key receipt anchors the completed peer chain. Only normal outcomes identify the chain endpoint with the final WG state; an interrupted peer's internal effects are not asserted. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder.WgLinks
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Leanux.Proofs.WG.Configuration

theorem original_request_wg_links (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _=>True)
      (fun initial outcome=>∃result:Inspection,result.outcome=outcome ∧
        Certificate attrs initial result ∧ Facts result) := by
  intro g a _
  exact ⟨inspection attrs g a,inspection_outcome attrs g a,
    inspection_certificate attrs g a,inspection_facts attrs g a⟩

theorem certificate_peer_chain (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (key : Receipt) (member : key∈result.receipts) (kind : key.kind=.keyStage) :
    ∃endpoint,Chain key.after.wg (peerReceipts result.receipts) endpoint := by
  have point:=matches_facts attrs initial result certificate.1.1
  rcases point.1 with none | ⟨endpoint,linked⟩
  · exact False.elim (none key member kind)
  · exact ⟨endpoint,linked key member kind⟩

theorem certificate_first_peer (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (key : Receipt) (member : key∈result.receipts) (kind : key.kind=.keyStage)
    (peer : Receipt) (first : (peerReceipts result.receipts)[0]?=some peer) :
    peer.before.wg=key.after.wg := by
  obtain ⟨_,chain⟩:=certificate_peer_chain attrs initial result certificate key member kind
  exact chain.first peer first

theorem certificate_adjacent_peers (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (key : Receipt) (member : key∈result.receipts) (kind : key.kind=.keyStage)
    (i : Nat) (left right : Receipt)
    (selected : (peerReceipts result.receipts)[i]?=some left)
    (next : (peerReceipts result.receipts)[i+1]?=some right) :
    left.after.wg=right.before.wg := by
  obtain ⟨_,chain⟩:=certificate_peer_chain attrs initial result certificate key member kind
  exact chain.adjacent i left right selected next

theorem certificate_final_chain (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (key : Receipt) (member : key∈result.receipts) (kind : key.kind=.keyStage) :
    Chain key.after.wg (peerReceipts result.receipts) final.wg := by
  have point:=matches_facts attrs initial result certificate.1.1
  rw [Facts,normal] at point
  exact point.2 key member kind

theorem certificate_last_peer (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (key : Receipt) (member : key∈result.receipts) (kind : key.kind=.keyStage)
    (i : Nat) (peer : Receipt)
    (selected : (peerReceipts result.receipts)[i]?=some peer)
    (last : i+1=(peerReceipts result.receipts).length) :
    peer.after.wg=final.wg :=
  (certificate_final_chain attrs initial result certificate ret final normal key member kind).last
    i peer selected last

theorem certificate_empty_peers (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (key : Receipt) (member : key∈result.receipts) (kind : key.kind=.keyStage)
    (empty : peerReceipts result.receipts=[]) :
    final.wg=key.after.wg :=
  ((certificate_final_chain attrs initial result certificate ret final normal key member kind).empty empty).symm

end Leanux.Proofs.WG.Config.RequestOrder.WgLinks
