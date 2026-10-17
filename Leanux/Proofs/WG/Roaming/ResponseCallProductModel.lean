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

def ResponseCallFacts (msg : List UInt8) (cut : ResponseCallCut) : Prop :=
  ((cut.underLoad = true ∧ cut.mac = .withCookie) ∨
    (cut.underLoad = false ∧ cut.mac = .noCookie)) ∧
  ResponseLookupFacts cut.lookup ∧ cut.consumed.input = cut.lookup.input ∧
  ResponseConsumedFacts msg cut.consumed ∧
  cut.beforeSetter.wg.device = cut.consumed.committedSnapshot.wg.device

def ResponseCallObservation (msg : List UInt8)
    (observed : Campaign2.Product.Outcome (Option ResponseCallCut)) : Prop :=
  ∃ candidate atCut, observed = .ok (candidate, atCut) ∧
    ∀ cut, candidate = some cut → cut.beforeSetter = atCut ∧ ResponseCallFacts msg cut

end Leanux.Proofs.WG.Roaming.Product
