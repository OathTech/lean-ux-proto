import Leanux.Proofs.WG.Roaming.ResponseModel
import Leanux.Proofs.WG.Campaign2.ProductView

namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

/-- The native consumption certificate together with the actual fixture
observation at entry. The native lift preserves that fixture. -/
structure ResponseConsumed extends Roaming.ResponseConsumed where
  fixture : Campaign2.Product.Fixture

def ResponseConsumed.committedSnapshot (cut : ResponseConsumed) : Campaign2.Product.Snapshot :=
  { toSnapshot := cut.committed, fixture := cut.fixture }

def ResponseConsumedFacts (msg : List UInt8) (cut : ResponseConsumed) : Prop :=
  Roaming.ResponseConsumedFacts msg cut.toResponseConsumed

end Leanux.Proofs.WG.Roaming.Product
