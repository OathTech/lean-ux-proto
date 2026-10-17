import Leanux.Proofs.WG.Config.EndpointPaginationModel
import Leanux.Proofs.WG.Config.PaginationCapacityFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Equal serialized device and peer prefix sizes transport the actual
endpoint-aware boundary domain and DATA/DONE count. This is a substantive
pure frame across updates; no computation type supplies it. -/
theorem endpointPagination_spaces (d e : Device) (p q : Peer)
    (deviceSpace : devicePrefixSpace d = devicePrefixSpace e)
    (peerSpace : peerFixedSpace p = peerFixedSpace q) (ids : List NodeId) :
    (endpointPaginationFresh d p ids ↔ endpointPaginationFresh e q ids) ∧
      endpointPaginationReceiveCount d p ids = endpointPaginationReceiveCount e q ids := by
  have first : endpointFirstCapacity d p = endpointFirstCapacity e q := by
    simp only [endpointFirstCapacity,deviceSpace,peerSpace]
  have resume : ipv4ResumeCapacity d = ipv4ResumeCapacity e := by
    simp only [ipv4ResumeCapacity,deviceSpace]
  cases ids with
  | nil => exact ⟨Iff.rfl,rfl⟩
  | cons start rest =>
    constructor
    · simp only [endpointPaginationFresh,first,resume]
    · simp only [endpointPaginationReceiveCount,first,deviceSpace,peerSpace]
      split
      · rfl
      · exact ipv4TailReceiveCount_prefixSpace d e deviceSpace _

end Leanux.Proofs.WG.Config
