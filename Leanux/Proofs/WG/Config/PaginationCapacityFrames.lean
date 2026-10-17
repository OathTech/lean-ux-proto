import Leanux.Proofs.WG.Config.PaginationCountModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The exact canonical resumed receive count depends on the serialized
device prefix size. This is a substantive pure transport lemma across Device
updates, not a frame supplied by a narrowed computation type. -/
theorem ipv4TailReceiveCount_prefixSpace (d e : Device)
    (same : devicePrefixSpace d = devicePrefixSpace e) (ids : List NodeId) :
    ipv4TailReceiveCount d ids = ipv4TailReceiveCount e ids := by
  have resume : ipv4ResumeCapacity d = ipv4ResumeCapacity e := by
    simp only [ipv4ResumeCapacity,same]
  cases ids with
  | nil => simp only [ipv4TailReceiveCount]
  | cons first rest =>
    conv => lhs; rw [ipv4TailReceiveCount]
    conv => rhs; rw [ipv4TailReceiveCount]
    rw [resume,same]
    cases remaining : rest.drop (ipv4ResumeCapacity e - 1) with
    | nil => rfl
    | cons next tail =>
      have ih := ipv4TailReceiveCount_prefixSpace d e same
        (rest.drop (ipv4ResumeCapacity e - 1))
      simpa only [remaining] using congrArg (fun n => 1 + n) ih
termination_by ids.length
decreasing_by simp_wf; omega

/-- Prefix-size preservation transports both the exact boundary domain and
its DATA/DONE count. No list uniqueness or extra socket room is introduced. -/
theorem ipv4Pagination_prefixSpace (d e : Device)
    (same : devicePrefixSpace d = devicePrefixSpace e) (ids : List NodeId) :
    (ipv4PaginationFresh d ids ↔ ipv4PaginationFresh e ids) ∧
      ipv4PaginationReceiveCount d ids = ipv4PaginationReceiveCount e ids := by
  have first : ipv4FirstCapacity d = ipv4FirstCapacity e := by
    simp only [ipv4FirstCapacity,same]
  have resume : ipv4ResumeCapacity d = ipv4ResumeCapacity e := by
    simp only [ipv4ResumeCapacity,same]
  cases ids with
  | nil => exact ⟨Iff.rfl,rfl⟩
  | cons start rest =>
    constructor
    · simp only [ipv4PaginationFresh,first,resume]
    · simp only [ipv4PaginationReceiveCount,first,same]
      split
      · rfl
      · exact ipv4TailReceiveCount_prefixSpace d e same _

end Leanux.Proofs.WG.Config
