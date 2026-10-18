import Leanux.Proofs.WG.Index.DataIngressSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem consumeData_indexCore (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Campaign2.Ensures (consumeData msg src ds) View.IndexCore (fun _=>View.IndexCore) :=
  (Noise.ensures_iff _ _ _).mpr (DataIngress.core msg src ds)

theorem consumeData_index (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Campaign2.Ensures (consumeData msg src ds) View.StagedIndexReady
      (fun _=>View.StagedIndexReady) := by
  intro w a result v b pre run
  exact (StagingRich.ready_native v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (DataIngress.ready msg src ds)
      w a result v b ((StagingRich.ready_native w a).mp pre) run)

end Leanux.Proofs.WG.Index
