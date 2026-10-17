import Leanux.Proofs.WG.Queues.RunnerSelectionData

/-! Introduction at specified original source cuts. The enclosing certificate
supplies the actual continuation; no successful-tail premise is added.
These lemmas lift local selections, not a definition of admission coverage. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.RunnerSelectionCuts
open Leanux Leanux.WG Leanux.Proofs.Logged
open AdmissionSelection RunnerSelectionData

/-- A local selected certificate fixes the actual first return and journal.
Source determinism and ledger uniqueness align it with the enclosing bind. -/
theorem bind_left {action : PrefixOuter RxHistory.Event α} {nextAction : α→PrefixOuter RxHistory.Event β}
    {first : ConservationOuter.Rule action} {next : ∀x,ConservationOuter.Rule (nextAction x)}
    (a : Selection first) (b : ∀x,Selection (next x))
    (source : (ConservationOuter.bind first next).relation cs h y k final)
    (front : first.relation cs h x j middle)
    (chosen : a.query operation inner front c) :
    (RunnerSelectionData.bind a b).query operation inner source c := by
  obtain ⟨x',j',middle',front',tail⟩ := source
  obtain ⟨rfl,rfl⟩ := (first.source front').symm.trans (first.source front)
  have same := first.unique front' front
  subst middle'
  exact Or.inl ⟨x,j,middle,front,tail,chosen⟩

/-- The selected tail follows this actual first certificate, with its exact
returned value and ledger. Neither equal operations nor equal event values
elsewhere in the execution identify this cut. -/
theorem bind_right {action : PrefixOuter RxHistory.Event α} {nextAction : α→PrefixOuter RxHistory.Event β}
    {first : ConservationOuter.Rule action} {next : ∀x,ConservationOuter.Rule (nextAction x)}
    (a : Selection first) (b : ∀x,Selection (next x))
    (source : (ConservationOuter.bind first next).relation cs h y k final)
    (front : first.relation cs h x j middle)
    (tail : (next x).relation middle j y k final)
    (chosen : (b x).query operation inner tail c) :
    (RunnerSelectionData.bind a b).query operation inner source c :=
  Or.inr ⟨x,j,middle,front,tail,chosen⟩

theorem runAt_selected (index : Nat) (w : World) {action : RxHistory.Obs α}
    (rule : ConservationSource.Rule action) (queries : Nat→Query rule)
    (fates : ∀inner,Fates (queries inner)) (effects : ConservationEffects.Conserves rule)
    (source : (ConservationOuter.runAt index w rule).relation cs h out k final)
    (chosen : queries inner source c) :
    (RunnerSelectionData.runAt index w rule queries fates effects).query index inner source c :=
  ⟨rfl,chosen⟩

/-- Selection at the first actual loop body needs no assumption about the
remainder's success: the enclosing normal certificate provides that remainder. -/
theorem forIn_here (item : γ) (items : List γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,ConservationOuter.Rule (action item acc))
    (selected : ∀item acc,Selection (rules item acc))
    (source : (ConservationOuter.forIn (item::items) initial action rules).relation cs h result k final)
    (front : (rules item initial).relation cs h step j middle)
    (chosen : (selected item initial).query operation inner front c) :
    (RunnerSelectionData.forIn (item::items) initial action rules selected).query operation inner source c := by
  obtain ⟨step',j',middle',front',tail⟩ := source
  obtain ⟨rfl,rfl⟩ := ((rules item initial).source front').symm.trans ((rules item initial).source front)
  have same := (rules item initial).unique front' front
  subst middle'
  exact ⟨0,step,j,middle,front,tail,chosen⟩

/-- Only an actual `.yield` reaches the selected later position. The saved
accumulator and ledger are exactly the first body's returned values. -/
theorem forIn_later (item : γ) (items : List γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,ConservationOuter.Rule (action item acc))
    (selected : ∀item acc,Selection (rules item acc))
    (source : (ConservationOuter.forIn (item::items) initial action rules).relation cs h result k final)
    (front : (rules item initial).relation cs h (.yield acc) j middle)
    (tail : (ConservationOuter.forIn items acc action rules).relation middle j result k final)
    (chosen : (RunnerSelectionData.forIn items acc action rules selected).query operation inner tail c) :
    (RunnerSelectionData.forIn (item::items) initial action rules selected).query operation inner source c := by
  obtain ⟨index,selection⟩ := chosen
  exact ⟨index+1,.yield acc,j,middle,front,tail,selection⟩

end Leanux.Proofs.WG.Queues.RxCredits.RunnerSelectionCuts
