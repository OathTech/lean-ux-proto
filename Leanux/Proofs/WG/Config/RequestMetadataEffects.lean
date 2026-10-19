import Leanux.Proofs.WG.Config.RequestMetadataModel

/-! Pure metadata-history algebra. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG

theorem MetadataAll.append {left right : List Receipt} {metadata : GetterMetadata}
    (a : MetadataAll left metadata) (b : MetadataAll right metadata) :
    MetadataAll (left++right) metadata := by
  intro r member value selected
  rcases List.mem_append.mp member with prior|next
  · exact a r prior value selected
  · exact b r next value selected

theorem NoMetadata.all {h : List Receipt} (point : NoMetadata h) (metadata : GetterMetadata) :
    MetadataAll h metadata := by
  intro r member value selected
  rw [point r member] at selected
  cases selected

theorem NoMetadata.consistent {h : List Receipt} (point : NoMetadata h) :
    MetadataConsistent h := ⟨none,point.all none⟩

end Leanux.Proofs.WG.Config.RequestOrder
