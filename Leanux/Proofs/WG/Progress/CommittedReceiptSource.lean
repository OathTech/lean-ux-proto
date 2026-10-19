import Leanux.Proofs.WG.Progress.CommittedReceiptBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns
open Leanux Leanux.Proofs.Logged

theorem run_source_preserves (origin : Origin) (activation : Activation) :
    PrefixPreserves (fun history _=>SourceHistory history) SourceHistory (run origin activation) :=
  History.run_preserves SourceReceipt sourceReceipt_fresh origin activation

end Leanux.Proofs.WG.Progress.CommittedRuns
