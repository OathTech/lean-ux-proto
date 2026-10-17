import Leanux.Proofs.WG.Roaming.ResponseLookupProductModel

namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG


structure ResponseCallCut where
  underLoad : Bool
  mac : MacState
  lookup : ResponseLookupCut
  consumed : ResponseConsumed
  beforeSetter : Campaign2.Product.Snapshot

def restoreResponseCallCut (fixture : Campaign2.Product.Fixture) (cut : Roaming.ResponseCallCut) :
    ResponseCallCut where
  underLoad := cut.underLoad
  mac := cut.mac
  lookup := restoreResponseLookupCut fixture cut.lookup
  consumed := ⟨cut.consumed, fixture⟩
  beforeSetter := { toSnapshot := cut.beforeSetter, fixture }

end Leanux.Proofs.WG.Roaming.Product
