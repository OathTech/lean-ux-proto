import Leanux.Proofs.WG.Roaming.InitiationConsumeProductModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.Product
open Leanux Leanux.WG

structure InitiationCallCut where
  underLoad : Bool
  mac : MacState
  consumed : InitiationConsumed
  beforeSetter : Campaign2.Product.Snapshot

def restoreInitiationCallCut (fixture : Campaign2.Product.Fixture) (cut : Roaming.InitiationCallCut) :
    InitiationCallCut where
  underLoad := cut.underLoad
  mac := cut.mac
  consumed := restoreInitiationConsume fixture cut.consumed
  beforeSetter := {toSnapshot := cut.beforeSetter, fixture}

def InitiationCallFacts (msg : List UInt8) (cut : InitiationCallCut) : Prop :=
  ((cut.underLoad = true ∧ cut.mac = .withCookie) ∨
    (cut.underLoad = false ∧ cut.mac = .noCookie)) ∧
  InitiationConsumedFacts msg cut.consumed ∧
  cut.beforeSetter.wg.device = cut.consumed.committed.wg.device

def InitiationCallObservation (msg : List UInt8)
    (observed : Campaign2.Product.Outcome (Option InitiationCallCut)) : Prop :=
  ∃ candidate atCut, observed = .ok (candidate, atCut) ∧
    ∀ cut, candidate = some cut → cut.beforeSetter = atCut ∧ InitiationCallFacts msg cut

end Leanux.Proofs.WG.Roaming.Product
