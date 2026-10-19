import Leanux.Proofs.WG.Queues.ConservationEffects
import Leanux.Proofs.WG.Queues.ConservationCertified

/-! Source-only carrier conservation through the original outer monad.
This propagates an incoming carrier; it does not invent an admitted occurrence
or classify a removal as a completed disposition. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.OuterEffects
open Leanux Leanux.WG Leanux.Proofs.Logged
open ConservationOuter

variable {P : Ledger→List RxHistory.Event→Prop}

def Conserves {action : PrefixOuter RxHistory.Event α} (rule : Rule action) : Prop :=
  ∀ {cs h x k next},rule.relation cs h x k next→TrafficEffects.Conserved cs next h k

theorem pure (x : α) : Conserves (ConservationOuter.pure x) := by
  rintro cs h y k next ⟨_,rfl,rfl⟩
  exact TrafficEffects.refl

theorem stopped (reason : Nat × Stop) : Conserves (ConservationOuter.stopped (α:=α) reason) := by
  intro cs h x k next certificate
  exact False.elim certificate

theorem bind {action : PrefixOuter RxHistory.Event α} {nextAction : α→PrefixOuter RxHistory.Event β}
    {first : Rule action} {next : ∀x,Rule (nextAction x)}
    (front : Conserves first) (tail : ∀x,Conserves (next x)) :
    Conserves (ConservationOuter.bind first next) := by
  rintro cs h y k final ⟨x,j,middle,a,b⟩
  exact TrafficEffects.trans (front a) (tail x b)

theorem reindex {action other : PrefixOuter RxHistory.Event α}
    (same : action=other) (rule : Rule action) (effect : Conserves rule) :
    Conserves (ConservationOuter.reindex same rule) := effect

theorem runAt (index : Nat) (w : World) {action : RxHistory.Obs α}
    (rule : ConservationSource.Rule action) (effect : ConservationEffects.Conserves rule) :
    Conserves (ConservationOuter.runAt index w rule) := fun certificate=>effect certificate

theorem forIn (items : List γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,Rule (action item acc))
    (effect : ∀item acc,Conserves (rules item acc)) :
    Conserves (ConservationOuter.forIn items initial action rules) := by
  induction items generalizing initial with
  | nil=>exact pure initial
  | cons item tail ih=>
    apply reindex
    apply bind (effect item initial)
    intro step
    cases step with
    | done result=>exact pure result
    | yield result=>exact ih result

theorem array (items : Array γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,Rule (action item acc))
    (effect : ∀item acc,Conserves (rules item acc)) :
    Conserves (ConservationOuter.array items initial action rules) :=
  forIn items.toList initial action rules effect

theorem certified_pure {Q : α→Ledger→List RxHistory.Event→Prop} (x : α) (step : ∀cs h,P cs h→Q x cs h) :
    Conserves (ConservationCertified.pure x step).rule := pure x

theorem certified_stopped (reason : Nat × Stop) :
    Conserves (ConservationCertified.stopped (α:=α) (P:=P) (Q:=Q) reason).rule := stopped reason

theorem certified_bind {action : PrefixOuter RxHistory.Event α} {nextAction : α→PrefixOuter RxHistory.Event β}
    {first : ConservationCertified.Certified action P Q}
    {next : ∀x,ConservationCertified.Certified (nextAction x) (Q x) R}
    (front : Conserves first.rule) (tail : ∀x,Conserves (next x).rule) :
    Conserves (ConservationCertified.bind first next).rule := bind front tail

theorem certified_mpr {action other : PrefixOuter RxHistory.Event α}
    (same : action=other)
    (types : ConservationCertified.Certified action P Q=ConservationCertified.Certified other P Q)
    (checked : ConservationCertified.Certified other P Q) (effect : Conserves checked.rule) :
    Conserves (Eq.mpr types checked).rule := by
  cases same
  exact effect

theorem certified_branch (condition : Prop) [Decidable condition]
    {yes no : PrefixOuter RxHistory.Event α}
    (a : condition→ConservationCertified.Certified yes P Q)
    (b : ¬condition→ConservationCertified.Certified no P Q)
    (ha : ∀h,Conserves (a h).rule) (hb : ∀h,Conserves (b h).rule) :
    Conserves (ConservationCertified.branch condition a b).rule := by
  unfold ConservationCertified.branch
  split
  next yes=>
    apply certified_mpr (same:=by simp only [yes,↓reduceIte])
    exact ha yes
  next no=>
    apply certified_mpr (same:=by simp only [no,↓reduceIte])
    exact hb no

theorem certified_runAt {Q : α × World→Ledger→List RxHistory.Event→Prop} (index : Nat) (w : World) {action : RxHistory.Obs α}
    (rule : ConservationSource.Rule action) (established : HolderTrafficDispatch.Established rule loans)
    (pre : ∀cs h,P cs h→HolderEntry.Inv cs loans h w)
    (post : ∀out cs h,HolderEntry.Inv cs loans h out.2→Q out cs h)
    (effect : ConservationEffects.Conserves rule) :
    Conserves (ConservationCertified.runAt index w rule established pre post).rule :=
  runAt index w rule effect

theorem certified_forIn {Q : β→Ledger→List RxHistory.Event→Prop} (items : List γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (I : β→Ledger→List RxHistory.Event→Prop)
    (body : ∀item acc,ConservationCertified.Certified (action item acc) (I acc)
      (fun step=>I (match step with | .done x=>x | .yield x=>x)))
    (pre : ∀cs h,P cs h→I initial cs h) (post : ∀out cs h,I out cs h→Q out cs h)
    (effect : ∀item acc,Conserves (body item acc).rule) :
    Conserves (ConservationCertified.forIn items initial action I body pre post).rule :=
  forIn items initial action _ effect

theorem certified_array {Q : β→Ledger→List RxHistory.Event→Prop} (items : Array γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (I : β→Ledger→List RxHistory.Event→Prop)
    (body : ∀item acc,ConservationCertified.Certified (action item acc) (I acc)
      (fun step=>I (match step with | .done x=>x | .yield x=>x)))
    (pre : ∀cs h,P cs h→I initial cs h) (post : ∀out cs h,I out cs h→Q out cs h)
    (effect : ∀item acc,Conserves (body item acc).rule) :
    Conserves (ConservationCertified.array items initial action I body pre post).rule :=
  array items initial action _ effect

end Leanux.Proofs.WG.Queues.RxCredits.OuterEffects
