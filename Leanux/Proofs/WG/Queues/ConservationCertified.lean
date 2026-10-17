import Leanux.Proofs.WG.Queues.ConservationOuter

/-! Concrete outer rules paired with normal establishment. The constructors
retain source-run certificates separately from endpoint funding. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ConservationCertified
open Leanux Leanux.WG Leanux.Proofs.Logged
open ConservationOuter

structure Certified (action : PrefixOuter RxHistory.Event α)
    (P : Ledger→List RxHistory.Event→Prop)
    (Q : α→Ledger→List RxHistory.Event→Prop) where
  rule : Rule action
  establishes : Ensures rule P Q

def pure (x : α) (step : ∀cs h,P cs h→Q x cs h) :
    Certified (pure x : PrefixOuter RxHistory.Event α) P Q :=
  ⟨ConservationOuter.pure x,pure_ensures x step⟩

def stopped (reason : Nat × Stop) :
    Certified (throw reason : PrefixOuter RxHistory.Event α) P Q :=
  ⟨ConservationOuter.stopped reason,stopped_ensures reason⟩

def bind {action : PrefixOuter RxHistory.Event α} {nextAction : α→PrefixOuter RxHistory.Event β}
    (first : Certified action P Q) (next : ∀x,Certified (nextAction x) (Q x) R) :
    Certified (action >>= nextAction) P R :=
  ⟨ConservationOuter.bind first.rule (fun x=>(next x).rule),
    bind_ensures first.establishes (fun x=>(next x).establishes)⟩

def branch (condition : Prop) [Decidable condition]
    {yes no : PrefixOuter RxHistory.Event α}
    (a : condition→Certified yes P Q) (b : ¬condition→Certified no P Q) :
    Certified (if condition then yes else no) P Q := by
  by_cases h : condition
  · simpa only [h,↓reduceIte] using a h
  · simpa only [h,↓reduceIte] using b h

def runAt (index : Nat) (w : World) {action : RxHistory.Obs α}
    (rule : ConservationSource.Rule action) (established : HolderTrafficDispatch.Established rule loans)
    (pre : ∀cs h,P cs h→HolderEntry.Inv cs loans h w)
    (post : ∀out cs h,HolderEntry.Inv cs loans h out.2→Q out cs h) :
    Certified (runAtPrefix index w action) P Q := by
  refine ⟨ConservationOuter.runAt index w rule,?_⟩
  intro cs h out k hi run
  obtain ⟨next,certificate,entry⟩ := runAt_ensures index w rule established (pre cs h hi) run
  exact ⟨next,certificate,post out next k entry⟩

def forIn (items : List γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (I : β→Ledger→List RxHistory.Event→Prop)
    (body : ∀item acc,Certified (action item acc) (I acc)
      (fun step=>I (match step with | .done x=>x | .yield x=>x)))
    (pre : ∀cs h,P cs h→I initial cs h)
    (post : ∀out cs h,I out cs h→Q out cs h) :
    Certified (ForIn.forIn items initial action) P Q := by
  refine ⟨ConservationOuter.forIn items initial action (fun item acc=>(body item acc).rule),?_⟩
  intro cs h out k hi run
  obtain ⟨next,certificate,entry⟩ := forIn_ensures items initial action
    (fun item acc=>(body item acc).rule) I (fun item acc=>(body item acc).establishes) (pre cs h hi) run
  exact ⟨next,certificate,post out next k entry⟩

def array (items : Array γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (I : β→Ledger→List RxHistory.Event→Prop)
    (body : ∀item acc,Certified (action item acc) (I acc)
      (fun step=>I (match step with | .done x=>x | .yield x=>x)))
    (pre : ∀cs h,P cs h→I initial cs h)
    (post : ∀out cs h,I out cs h→Q out cs h) :
    Certified (ForIn.forIn items initial action) P Q := by
  refine ⟨ConservationOuter.array items initial action (fun item acc=>(body item acc).rule),?_⟩
  intro cs h out k hi run
  obtain ⟨next,certificate,entry⟩ := array_ensures items initial action
    (fun item acc=>(body item acc).rule) I (fun item acc=>(body item acc).establishes) (pre cs h hi) run
  exact ⟨next,certificate,post out next k entry⟩

end Leanux.Proofs.WG.Queues.RxCredits.ConservationCertified
