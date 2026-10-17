import Leanux.Proofs.WG.Queues.OuterSelection
import Leanux.Proofs.WG.Queues.SyscallSelection

/-! Query and fate proof data on the existing outer source certificate.
The first index is the actual runner operation number; the second selects
the admission within its flood or batch. No execution is defined here. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.RunnerSelectionData
open Leanux Leanux.WG Leanux.Proofs.Logged
open AdmissionSelection

variable {P : Ledger→List RxHistory.Event→Prop}

structure Selection {action : PrefixOuter RxHistory.Event α} (rule : ConservationOuter.Rule action) where
  query : Nat → Nat → OuterQuery rule
  fates : ∀ operation inner, OuterFates (query operation inner)
  effects : OuterEffects.Conserves rule

def never {action : PrefixOuter RxHistory.Event α} (rule : ConservationOuter.Rule action)
    (effects : OuterEffects.Conserves rule) : Selection rule :=
  ⟨fun _ _ => OuterSelection.never rule, fun _ _ => OuterSelection.never_fates rule, effects⟩

def pure (x : α) : Selection (ConservationOuter.pure x) :=
  never _ (OuterEffects.pure x)

def stopped (reason : Nat × Stop) : Selection (ConservationOuter.stopped (α:=α) reason) :=
  never _ (OuterEffects.stopped reason)

def bind {action : PrefixOuter RxHistory.Event α} {nextAction : α→PrefixOuter RxHistory.Event β}
    {first : ConservationOuter.Rule action} {next : ∀x,ConservationOuter.Rule (nextAction x)}
    (front : Selection first) (tail : ∀x,Selection (next x)) :
    Selection (ConservationOuter.bind first next) where
  query operation inner := fun {cs h x k final} certificate c =>
    outerLeft first next (front.query operation inner) certificate c ∨
    outerRight first next (fun x=>(tail x).query operation inner) certificate c
  fates operation inner := by
    intro cs h x k final certificate c chosen
    rcases chosen with left | right
    · exact outerLeft_fates first next _ (front.fates operation inner)
        (fun x=>(tail x).effects) certificate left
    · exact outerRight_fates first next _ (fun x=>(tail x).fates operation inner) certificate right
  effects := OuterEffects.bind front.effects (fun x=>(tail x).effects)

def runAt (index : Nat) (w : World) {action : RxHistory.Obs α}
    (rule : ConservationSource.Rule action) (queries : Nat→Query rule)
    (chosen : ∀inner,Fates (queries inner)) (effects : ConservationEffects.Conserves rule) :
    Selection (ConservationOuter.runAt index w rule) where
  query operation inner := fun {cs h x k final} certificate c => operation=index ∧ queries inner certificate c
  fates operation inner := by
    intro cs h x k final certificate c selection
    exact chosen inner certificate selection.2
  effects := OuterEffects.runAt index w rule effects

def quietRunAt (index : Nat) (w : World) {action : RxHistory.Obs α}
    (rule : ConservationSource.Rule action) (effects : ConservationEffects.Conserves rule) :
    Selection (ConservationOuter.runAt index w rule) :=
  never _ (OuterEffects.runAt index w rule effects)

def forIn (items : List γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,ConservationOuter.Rule (action item acc))
    (selected : ∀item acc,Selection (rules item acc)) :
    Selection (ConservationOuter.forIn items initial action rules) where
  query operation inner := fun {cs h x k final} certificate c => ∃index,
    OuterSelection.forIn items initial action rules
      (fun item acc=>(selected item acc).query operation inner) index certificate c
  fates operation inner := by
    intro cs h x k final certificate c selection
    obtain ⟨index,chosen⟩ := selection
    exact OuterSelection.forIn_fates items initial action rules _ index
      (fun item acc=>(selected item acc).fates operation inner)
      (fun item acc=>(selected item acc).effects) certificate chosen
  effects := OuterEffects.forIn items initial action rules (fun item acc=>(selected item acc).effects)

def array (items : Array γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,ConservationOuter.Rule (action item acc))
    (selected : ∀item acc,Selection (rules item acc)) :
    Selection (ConservationOuter.array items initial action rules) where
  query operation inner := fun {cs h x k final} certificate c => ∃index,
    OuterSelection.array items initial action rules
      (fun item acc=>(selected item acc).query operation inner) index certificate c
  fates operation inner := by
    intro cs h x k final certificate c selection
    obtain ⟨index,chosen⟩ := selection
    exact OuterSelection.array_fates items initial action rules _ index
      (fun item acc=>(selected item acc).fates operation inner)
      (fun item acc=>(selected item acc).effects) certificate chosen
  effects := OuterEffects.array items initial action rules (fun item acc=>(selected item acc).effects)

def certified_pure {Q : α→Ledger→List RxHistory.Event→Prop} (x : α) (step : ∀cs h,P cs h→Q x cs h) :
    Selection (ConservationCertified.pure x step).rule := pure x

def certified_stopped (reason : Nat × Stop) :
    Selection (ConservationCertified.stopped (α:=α) (P:=P) (Q:=Q) reason).rule := stopped reason

def certified_bind {action : PrefixOuter RxHistory.Event α} {nextAction : α→PrefixOuter RxHistory.Event β}
    {first : ConservationCertified.Certified action P Q}
    {next : ∀x,ConservationCertified.Certified (nextAction x) (Q x) R}
    (front : Selection first.rule) (tail : ∀x,Selection (next x).rule) :
    Selection (ConservationCertified.bind first next).rule := bind front tail

def certified_mpr {action other : PrefixOuter RxHistory.Event α}
    (same : action=other)
    (types : ConservationCertified.Certified action P Q=ConservationCertified.Certified other P Q)
    (checked : ConservationCertified.Certified other P Q) (selected : Selection checked.rule) :
    Selection (Eq.mpr types checked).rule := by
  cases same
  exact selected

def certified_branch (condition : Prop) [Decidable condition]
    {yes no : PrefixOuter RxHistory.Event α}
    (a : condition→ConservationCertified.Certified yes P Q)
    (b : ¬condition→ConservationCertified.Certified no P Q)
    (ha : ∀h,Selection (a h).rule) (hb : ∀h,Selection (b h).rule) :
    Selection (ConservationCertified.branch condition a b).rule := by
  unfold ConservationCertified.branch
  split
  next yes=>
    apply certified_mpr (same:=by simp only [yes,↓reduceIte])
    exact ha yes
  next no=>
    apply certified_mpr (same:=by simp only [no,↓reduceIte])
    exact hb no

def certified_forIn {Q : β→Ledger→List RxHistory.Event→Prop} (items : List γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (I : β→Ledger→List RxHistory.Event→Prop)
    (body : ∀item acc,ConservationCertified.Certified (action item acc) (I acc)
      (fun step=>I (match step with | .done x=>x | .yield x=>x)))
    (pre : ∀cs h,P cs h→I initial cs h) (post : ∀out cs h,I out cs h→Q out cs h)
    (selected : ∀item acc,Selection (body item acc).rule) :
    Selection (ConservationCertified.forIn items initial action I body pre post).rule :=
  forIn items initial action _ selected

def certified_array {Q : β→Ledger→List RxHistory.Event→Prop} (items : Array γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (I : β→Ledger→List RxHistory.Event→Prop)
    (body : ∀item acc,ConservationCertified.Certified (action item acc) (I acc)
      (fun step=>I (match step with | .done x=>x | .yield x=>x)))
    (pre : ∀cs h,P cs h→I initial cs h) (post : ∀out cs h,I out cs h→Q out cs h)
    (selected : ∀item acc,Selection (body item acc).rule) :
    Selection (ConservationCertified.array items initial action I body pre post).rule :=
  array items initial action _ selected

end Leanux.Proofs.WG.Queues.RxCredits.RunnerSelectionData
