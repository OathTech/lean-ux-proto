import Leanux.Proofs.WG.Queues.HolderTrafficDispatch
import Leanux.Proofs.WG.Queues.JointRunnerSource

/-! Normal source certificates through the existing outer runner monad.
Worlds remain the explicit arguments/results of runAtPrefix and the original
runner accumulator. No second interpreter or stopped-state account is added. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ConservationOuter
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

abbrev Relation (α : Type) := Ledger → List RxHistory.Event → α → List RxHistory.Event → Ledger → Prop

/-- Source-only evidence on the same exact outer action. A separate normal
establishment theorem must construct this relation from its input entry. -/
structure Rule (action : PrefixOuter RxHistory.Event α) where
  relation : Relation α
  source : ∀ {cs h x k next},relation cs h x k next → runPrefixOuter action h=(.ok x,k)
  appends : ∀ {cs h x k next},relation cs h x k next → ∃ suffix,k=h++suffix
  unique : ∀ {cs h x k left right},relation cs h x k left → relation cs h x k right → left=right

def pure (x : α) : Rule (pure x : PrefixOuter RxHistory.Event α) where
  relation := fun cs h y k next=>y=x ∧ k=h ∧ next=cs
  source := by rintro cs h y k next ⟨rfl,rfl,rfl⟩; rfl
  appends := by rintro cs h y k next ⟨_,rfl,_⟩; exact ⟨[],by simp⟩
  unique := by intro cs h y k left right a b; exact a.2.2.trans b.2.2.symm

/-- An indexed Stop has no normal certificate and no fabricated returned World. -/
def stopped (reason : Nat × Stop) : Rule (throw reason : PrefixOuter RxHistory.Event α) where
  relation := fun _ _ _ _ _=>False
  source := by intros; contradiction
  appends := by intros; contradiction
  unique := by intros; contradiction

def bind {action : PrefixOuter RxHistory.Event α} {nextAction : α→PrefixOuter RxHistory.Event β}
    (first : Rule action) (next : ∀x,Rule (nextAction x)) : Rule (action >>= nextAction) where
  relation := fun cs h y k final=>∃x j middle,first.relation cs h x j middle ∧ (next x).relation middle j y k final
  source := by
    rintro cs h y k final ⟨x,j,middle,a,b⟩
    simp only [runPrefixOuter_bind,first.source a,(next x).source b]
  appends := by
    rintro cs h y k final ⟨x,j,middle,a,b⟩
    obtain ⟨front,hfront⟩ := first.appends a
    obtain ⟨tail,htail⟩ := (next x).appends b
    exact ⟨front++tail,by rw [htail,hfront,List.append_assoc]⟩
  unique := by
    rintro cs h y k left right ⟨x,j,middle,a,b⟩ ⟨x',j',middle',a',b'⟩
    have same := (first.source a).symm.trans (first.source a')
    obtain ⟨rfl,rfl⟩ := same
    have ledger := first.unique a a'
    subst middle'
    exact (next x).unique b b'

/-- The actual operation index and returned World remain in this runAt action.
Its relation is exactly the inner source relation at that input World. -/
def runAt (index : Nat) (w : World) {action : RxHistory.Obs α}
    (rule : ConservationSource.Rule action) : Rule (runAtPrefix index w action) where
  relation := fun cs h out k next=>rule.relation cs w h out.1 out.2 k next
  source := by
    intro cs h out k next certificate
    simp only [runAtPrefix_run,rule.source certificate,Except.mapError]
  appends := by intro cs h out k next certificate; exact rule.appends certificate
  unique := by intro cs h out k left right a b; exact rule.unique a b

/-- Equality transport retains the relation definitionally; only its exact
source equation changes presentation. -/
def reindex {action other : PrefixOuter RxHistory.Event α}
    (same : action=other) (rule : Rule action) : Rule other where
  relation := rule.relation
  source := by intro cs h x k next certificate; rw [←same]; exact rule.source certificate
  appends := rule.appends
  unique := rule.unique

def forIn (items : List γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,Rule (action item acc)) : Rule (ForIn.forIn items initial action) :=
  match items with
  | []=>pure initial
  | item::tail=>reindex (by rw [List.forIn_cons])
      (bind (rules item initial) fun step=>match step with
        | .done result=>pure result
        | .yield result=>forIn tail result action rules)

def array (items : Array γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,Rule (action item acc)) : Rule (ForIn.forIn items initial action) := by
  exact reindex (by rw [Array.forIn_toList]) (forIn items.toList initial action rules)

/-- Normal establishment retains the chosen source certificate as well as
the result-dependent endpoint assertion. It makes no assertion after a Stop. -/
def Ensures {action : PrefixOuter RxHistory.Event α} (rule : Rule action)
    (P : Ledger→List RxHistory.Event→Prop) (Q : α→Ledger→List RxHistory.Event→Prop) : Prop :=
  ∀ {cs h x k},P cs h→runPrefixOuter action h=(.ok x,k)→
    ∃next,rule.relation cs h x k next ∧ Q x next k

theorem reindex_ensures {action other : PrefixOuter RxHistory.Event α}
    (same : action=other) (rule : Rule action) (proof : Ensures rule P Q) :
    Ensures (reindex same rule) P Q := by
  intro cs h x k hi run
  exact proof hi (same ▸ run)

theorem pure_ensures (x : α) (step : ∀cs h,P cs h→Q x cs h) : Ensures (pure x) P Q := by
  intro cs h y k hi run
  simp only [runPrefixOuter_pure,Prod.mk.injEq,Except.ok.injEq] at run
  obtain ⟨rfl,rfl⟩ := run
  exact ⟨cs,⟨rfl,rfl,rfl⟩,step cs h hi⟩

theorem stopped_ensures (reason : Nat × Stop) : Ensures (stopped (α:=α) reason) P Q := by
  intro cs h x k hi run
  cases run

theorem bind_ensures {action : PrefixOuter RxHistory.Event α} {nextAction : α→PrefixOuter RxHistory.Event β}
    {first : Rule action} {next : ∀x,Rule (nextAction x)}
    (a : Ensures first P Q) (b : ∀x,Ensures (next x) (Q x) R) : Ensures (bind first next) P R := by
  intro cs h y k hi run
  rw [runPrefixOuter_bind] at run
  cases start : runPrefixOuter action h with
  | mk result j=>
    rw [start] at run
    cases result with
    | error reason=>cases run
    | ok x=>
      obtain ⟨middle,front,entry⟩ := a hi start
      obtain ⟨final,tail,entry'⟩ := b x entry run
      exact ⟨final,⟨x,j,middle,front,tail⟩,entry'⟩

theorem runAt_ensures (index : Nat) (w : World) {action : RxHistory.Obs α}
    (rule : ConservationSource.Rule action) (established : HolderTrafficDispatch.Established rule loans) :
    Ensures (runAt index w rule) (fun cs h=>HolderEntry.Inv cs loans h w)
      (fun out next k=>HolderEntry.Inv next loans k out.2) := by
  intro cs h out k hi run
  rw [runAtPrefix_run] at run
  cases actual : runPrefix action w h with
  | mk result j=>
    rw [actual] at run
    cases result with
    | error reason=>cases run
    | ok value=>
      cases run
      exact established hi actual

/-- The finite source loop retains its actual returned accumulator, including
early done. Each body receives exactly the prior body's returned ledger. -/
theorem forIn_ensures (items : List γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,Rule (action item acc))
    (I : β→Ledger→List RxHistory.Event→Prop)
    (body : ∀item acc,Ensures (rules item acc) (I acc)
      (fun step=>I (match step with | .done x=>x | .yield x=>x))) :
    Ensures (forIn items initial action rules) (I initial) I := by
  induction items generalizing initial with
  | nil=>exact pure_ensures initial (fun _ _ hi=>hi)
  | cons item tail ih=>
    apply reindex_ensures
    apply bind_ensures (body item initial)
    intro step
    cases step with
    | done result=>exact pure_ensures result (fun _ _ hi=>hi)
    | yield result=>exact ih result

theorem array_ensures (items : Array γ) (initial : β)
    (action : γ→β→PrefixOuter RxHistory.Event (ForInStep β))
    (rules : ∀item acc,Rule (action item acc))
    (I : β→Ledger→List RxHistory.Event→Prop)
    (body : ∀item acc,Ensures (rules item acc) (I acc)
      (fun step=>I (match step with | .done x=>x | .yield x=>x))) :
    Ensures (array items initial action rules) (I initial) I := by
  apply reindex_ensures
  exact forIn_ensures items.toList initial action rules I body

end Leanux.Proofs.WG.Queues.RxCredits.ConservationOuter
