import Leanux.Proofs.WG.Progress.CommittedRunModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Initialized
open Lean Leanux

abbrev Inspection :=
  Except (Nat × Stop) (Json × Campaign2.Product.Snapshot) × List Receipt


end Leanux.Proofs.WG.Progress.CommittedRuns.Initialized
