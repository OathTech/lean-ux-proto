import Leanux.Proofs.WG.Noise.ReceptionCoverageSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ReceptionCaller
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Origins

/-- Every surviving tag along a normal reception call is inherited across
nonreceipt work or supplied by an actual checked handshake receipt. This
permits peer deletion and does not assert successful completion. -/
theorem original_reception_tag_coverage (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observeClassified msg src) (fun s => s = entry)
      (fun call final =>
        ReceiveStepCaller.ReceptionShape msg src call ∧
        TagCoverage entry.tagAt call.receipts final.tagAt) := by
  intro g ambient call final after pre run
  have shape := original_reception_dispatch msg src g ambient call final after True.intro run
  have coverage := observeClassified_coverage msg src g ambient call final after run
  refine ⟨shape,?_⟩
  subst entry
  exact coverage

end Leanux.Proofs.WG.Noise.ReceptionCaller
