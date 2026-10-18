import Leanux.Proofs.WG.Index.ReceiveCoreSource
import Leanux.Proofs.WG.Index.ReachedWorkersSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing

/-- Original normal data completion preserves current slot compatibility and
the full index component through confirmation, staging and source validation. -/
theorem consumeDataDone_index (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Campaign2.Ensures (consumeDataDone pid pkt endpoint) View.StagedIndexReady
      (fun _ => View.StagedIndexReady) := by
  intro w a result v b pre run
  exact (StagingRich.ready_native v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (ReceiveCompletion.consume_ready pid pkt endpoint)
      w a result v b ((StagingRich.ready_native w a).mp pre) run)

/-- Actual clear-work dispatch derives its selected queue entry and preserves
the supplied index component on normal return, with no readiness premise. -/
theorem clearWorker_index :
    Campaign2.Product.Ensures Env.runOneClearWorker
      (fun s=>View.IndexCore s.toSnapshot) (fun _ s=>View.IndexCore s.toSnapshot) :=
  ReachedWorkers.clear_core

end Leanux.Proofs.WG.Index
