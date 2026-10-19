import Leanux.Proofs.WG.Queues.AdmissionSelection
import Leanux.Proofs.WG.Queues.OuterEffects

/-! The position is a list/array iteration index in the existing outer source
certificate, not a search for an equal operation or equal journal value. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.OuterSelection
open Leanux Leanux.WG Leanux.Proofs.Logged
open AdmissionSelection

def never {action : PrefixOuter RxHistory.Event α} (rule : ConservationOuter.Rule action) :
    OuterQuery rule := fun _ _=>False

theorem never_fates {action : PrefixOuter RxHistory.Event α} (rule : ConservationOuter.Rule action) :
    OuterFates (never rule) := by
  intro cs h x k next certificate c selected
  contradiction

def reindex {action other : PrefixOuter RxHistory.Event α} (same : action=other)
    (rule : ConservationOuter.Rule action) (query : OuterQuery rule) :
    OuterQuery (ConservationOuter.reindex same rule) := query

theorem reindex_fates {action other : PrefixOuter RxHistory.Event α} (same : action=other)
    (rule : ConservationOuter.Rule action) (query : OuterQuery rule) (chosen : OuterFates query) :
    OuterFates (reindex same rule query) := chosen

/-- Early `.done` cannot select a later iteration. The accumulator at a
selected `.yield` continuation is exactly the actual preceding result. -/
def forIn (items : List γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,ConservationOuter.Rule (action item acc))
    (queries : ∀item acc,OuterQuery (rules item acc)) (index : Nat) :
    OuterQuery (ConservationOuter.forIn items initial action rules) :=
  match items,index with
  | [],_=>never _
  | item::_,0=>outerLeft (rules item initial) _ (queries item initial)
  | item::tail,n+1=>outerRight (rules item initial) _ (fun step=>match step with
      | .done _=>never _
      | .yield result=>forIn tail result action rules queries n)

theorem forIn_fates (items : List γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,ConservationOuter.Rule (action item acc))
    (queries : ∀item acc,OuterQuery (rules item acc)) (index : Nat)
    (chosen : ∀item acc,OuterFates (queries item acc))
    (effects : ∀item acc,OuterEffects.Conserves (rules item acc)) :
    OuterFates (forIn items initial action rules queries index) := by
  induction items generalizing initial index with
  | nil=>exact never_fates _
  | cons item rest ih=>
    cases index with
    | zero=>
      apply outerLeft_fates _ _ _ (chosen item initial)
      intro step
      cases step with
      | done result=>exact OuterEffects.pure result
      | yield result=>exact OuterEffects.forIn rest result action rules effects
    | succ n=>
      apply outerRight_fates
      intro step
      cases step with
      | done result=>exact never_fates _
      | yield result=>exact ih result n

def array (items : Array γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,ConservationOuter.Rule (action item acc))
    (queries : ∀item acc,OuterQuery (rules item acc)) (index : Nat) :
    OuterQuery (ConservationOuter.array items initial action rules) :=
  forIn items.toList initial action rules queries index

theorem array_fates (items : Array γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,ConservationOuter.Rule (action item acc))
    (queries : ∀item acc,OuterQuery (rules item acc)) (index : Nat)
    (chosen : ∀item acc,OuterFates (queries item acc))
    (effects : ∀item acc,OuterEffects.Conserves (rules item acc)) :
    OuterFates (array items initial action rules queries index) :=
  forIn_fates items.toList initial action rules queries index chosen effects

end Leanux.Proofs.WG.Queues.RxCredits.OuterSelection
