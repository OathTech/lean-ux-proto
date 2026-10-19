import Leanux.Proofs.WG.Config.RequestOrderInspectionSource

/-! Projected whole-request certificate, completed peer positions, and accepted-entry effects. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

theorem inspection_receipt_valid (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : InspectionFacts attrs entry result)
    (position : Nat) (r : Receipt) (selected : result.receipts[position]? = some r) :
    Valid attrs r :=
  facts.2.1 r (List.mem_of_getElem? selected)

theorem original_request_certificate (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _ => True)
      (fun entry outcome => ∃ result : Inspection,
        result.outcome = outcome ∧ Certificate attrs entry result) := by
  intro w ambient _
  exact ⟨inspection attrs w ambient,inspection_outcome attrs w ambient,
    inspection_certificate attrs w ambient⟩

theorem inspection_returns (attrs : DeviceAttrs) :
    Campaign2.Returns (inspect attrs) (fun _ => True)
      (fun result entry => Certificate attrs entry result) := by
  intro w ambient _
  exact ⟨inspection attrs w ambient,w,ambient,rfl,inspection_certificate attrs w ambient⟩

theorem certificate_peer_position (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs entry result)
    (i : Nat) (r : Receipt) (p : PeerAttrs)
    (selected : (peerReceipts result.receipts)[i]? = some r) (kind : r.kind = .peer p) :
    (attrs.peers.getD [])[i]? = some (.attrs p) :=
  request_peer_position attrs result.receipts facts.1.2.2.1 i r p selected kind

theorem certificate_entry (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs entry result)
    (nonempty : result.receipts ≠ []) :
    ∃ r rest, result.receipts = r :: rest ∧ EntryReceipt attrs entry.wg r := by
  rcases facts.2.1 with empty | begun
  · exact False.elim (nonempty empty)
  · exact begun

end Leanux.Proofs.WG.Config.RequestOrder
