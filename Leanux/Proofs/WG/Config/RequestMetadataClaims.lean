import Leanux.Proofs.WG.Config.RequestMetadataSource

/-! Projected same-run key/peer metadata consistency and normal final-state linkage. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Leanux.Proofs.WG.Configuration

theorem matches_metadata (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (matched : Matches attrs entry result) : MetadataFacts result := by
  obtain ⟨w,ambient,rfl,rfl⟩ := matched
  exact inspection_metadata attrs w ambient

theorem original_request_metadata (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _=>True)
      (fun entry outcome=>∃result : Inspection,
        result.outcome=outcome ∧ Certificate attrs entry result ∧ MetadataFacts result) := by
  intro w ambient _
  exact ⟨inspection attrs w ambient,inspection_outcome attrs w ambient,
    inspection_certificate attrs w ambient,inspection_metadata attrs w ambient⟩

theorem certificate_key_final_metadata (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs entry result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : Receipt) (member : r ∈ result.receipts) (kind : r.kind=.keyStage) :
    getterMetadataObservation r.after=getterMetadataObservation final := by
  have point := (matches_metadata attrs entry result facts.1.1).2
  rw [normal] at point
  exact point r member _ (by simp only [metadataValues,kind,List.mem_singleton])

theorem certificate_peer_final_metadata (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs entry result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : Receipt) (member : r ∈ result.receipts) (p : PeerAttrs) (kind : r.kind=.peer p) :
    getterMetadataObservation r.before=getterMetadataObservation final ∧
      getterMetadataObservation r.after=getterMetadataObservation final := by
  have point := (matches_metadata attrs entry result facts.1.1).2
  rw [normal] at point
  exact ⟨point r member _ (by simp [metadataValues,kind]),
    point r member _ (by simp [metadataValues,kind])⟩

theorem certificate_key_peer_metadata (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs entry result)
    (key peer : Receipt) (keyMember : key ∈ result.receipts) (keyKind : key.kind=.keyStage)
    (peerMember : peer ∈ result.receipts) (p : PeerAttrs) (peerKind : peer.kind=.peer p) :
    getterMetadataObservation key.after=getterMetadataObservation peer.before ∧
      getterMetadataObservation key.after=getterMetadataObservation peer.after := by
  obtain ⟨metadata,point⟩ := (matches_metadata attrs entry result facts.1.1).1
  have k := point key keyMember (getterMetadataObservation key.after) (by simp [metadataValues,keyKind])
  have b := point peer peerMember (getterMetadataObservation peer.before) (by simp [metadataValues,peerKind])
  have a := point peer peerMember (getterMetadataObservation peer.after) (by simp [metadataValues,peerKind])
  exact ⟨k.trans b.symm,k.trans a.symm⟩

end Leanux.Proofs.WG.Config.RequestOrder
