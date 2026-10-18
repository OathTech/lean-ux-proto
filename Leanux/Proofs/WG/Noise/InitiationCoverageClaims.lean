import Leanux.Proofs.WG.Noise.InitiationCoverageSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.InitiationCaller
open Leanux Leanux.WG TimerDiscipline

/-- The actual normal sender links entry and final tags through its zero-or-one
creator receipt. The original rate classification and receipt provenance remain;
a created message need not have been delivered. -/
theorem original_initiation_tag_coverage (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observe pid) (fun s => s = entry)
      (fun call final =>
        RateObserved pid entry call ∧ CallFacts pid entry call ∧
        TagCoverage entry.tagAt call.receipts final.tagAt) := by
  intro g ambient call final after pre run
  have facts := original_initiation_receipts pid entry g ambient call final after pre run
  have coverage := observe_coverage pid entry g ambient call final after
    (congrArg Campaign2.Snapshot.tagAt pre) run
  exact ⟨facts.1,facts.2,coverage⟩

/-- The final original peer release may delete peers; it cannot invent or
change surviving tags. This is a normal worker contract, without a reference
readiness or initialized-run premise. -/
theorem original_initiation_worker_tag_coverage (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observeWorker pid) (fun s => s = entry)
      (fun call final =>
        RateObserved pid entry call ∧ CallFacts pid entry call ∧
        TagCoverage entry.tagAt call.receipts final.tagAt) := by
  intro g ambient call final after pre run
  have facts := original_initiation_worker_receipts pid entry g ambient call final after pre run
  have coverage := observeWorker_coverage pid entry g ambient call final after
    (congrArg Campaign2.Snapshot.tagAt pre) run
  exact ⟨facts.1,facts.2,coverage⟩

end Leanux.Proofs.WG.Noise.InitiationCaller
