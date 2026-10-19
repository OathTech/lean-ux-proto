import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixContracts
import Leanux.Proofs.Logged.WGPrefix

/-! Native state and ambient composition keeps the additional certificate
through bind, finite loops and the existing product observer adapter. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix
open Leanux Leanux.Proofs.Logged

def WithState (P : List E→Outer→Inner→Prop) (Safe : List E→Prop)
    (h : List E) (w : Outer) (a : Inner) : Prop := P h w a ∧ All Safe h

abbrev StateEnsures (P : List E→Outer→Inner→Prop) (Safe : List E→Prop)
    (body : StatePrefixT E Outer Inner α) (Q : α→List E→Outer→Inner→Prop) : Prop :=
  StatePrefixEnsures (WithState P Safe) (All Safe) body (fun value=>WithState (Q value) Safe)

variable {P : List E→Outer→Inner→Prop} {Safe : List E→Prop}
variable {Q : α→List E→Outer→Inner→Prop} {R : β→List E→Outer→Inner→Prop}
variable {body : StatePrefixT E Outer Inner α} {next : α→StatePrefixT E Outer Inner β}

theorem StateEnsures.bind (head : StateEnsures P Safe body Q)
    (tail : ∀ x, StateEnsures (Q x) Safe (next x) R) :
    StateEnsures P Safe (body >>= next) R := StatePrefixEnsures.bind head tail

theorem StateEnsures.pure (value : α) (post : ∀ h w a, P h w a→Q value h w a) :
    StateEnsures P Safe (pure value) Q :=
  StatePrefixEnsures.pure value (fun _ _ _ before=>before.2)
    (fun h w a before=>⟨post h w a before.1,before.2⟩)

theorem StateEnsures.lift (native : StateT Outer (StateT Inner (Except Stop)) α)
    (post : ∀ h w a value v b, P h w a→(native.run w).run a=.ok ((value,v),b)→Q value h v b) :
    StateEnsures P Safe (liftStatePrefix native) Q :=
  StatePrefixEnsures.lift native (fun _ _ _ before=>before.2)
    (fun h w a value v b before run=>⟨post h w a value v b before.1 run,before.2⟩)

theorem StateEnsures.emit {Post : Unit→List E→Outer→Inner→Prop} (event : E)
    (safe : ∀ h w a, P h w a→Safe (h++[event]))
    (post : ∀ h w a, P h w a→Post () (h++[event]) w a) :
    StateEnsures P Safe (emitStatePrefix event) Post := by
  apply StatePrefixEnsures.emit
  · intro h w a before
    exact before.2.append (Cuts.singleton before.2.last (safe h w a before.1))
  · intro h w a before
    exact ⟨post h w a before.1,before.2.append (Cuts.singleton before.2.last (safe h w a before.1))⟩

theorem StateEnsures.forIn (xs : List α) (initial : β)
    (action : α→β→StatePrefixT E Outer Inner (ForInStep β)) (I : β→List E→Outer→Inner→Prop)
    (checked : ∀ value acc, StateEnsures (I acc) Safe (action value acc) (fun step=>I step.value)) :
    StateEnsures (I initial) Safe (forIn xs initial action) I :=
  StatePrefixEnsures.forInInvariant xs initial action (fun acc=>WithState (I acc) Safe) (All Safe)
    (fun _ _ _ _ before=>before.2) checked

/-- An old native endpoint contract needs its own internal journal-cut proof.
The premise covers the actual output of normal and stopped executions. -/
theorem StateEnsures.of_cuts (endpoint : StatePrefixEnsures P Safe body Q)
    (cuts : ∀ w a h, P h w a→∃ suffix,
      (runStatePrefix body w a h).2=h++suffix ∧ Cuts Safe h suffix) :
    StateEnsures P Safe body Q := by
  intro w a h before
  obtain ⟨suffix,extended,_,kept⟩ := endpoint w a h before.1
  obtain ⟨added,equation,certified⟩ := cuts w a h before.1
  have all : All Safe (runStatePrefix body w a h).2 := equation ▸ before.2.append certified
  refine ⟨suffix,extended,all,?_⟩
  cases result : (runPrefix (body.run w) a h).1 with
  | error reason => trivial
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    rw [result] at kept
    exact ⟨kept,all⟩

/-- The actual WG adapter retains the same result, world and complete event
prefix; this transports an established certificate, not an erased history. -/
theorem StateEnsures.liftWG {P : List E→WGWorld→Ambient→Prop}
    {Q : α→List E→WGWorld→Ambient→Prop} {body : WGPrefix E α}
    (checked : StateEnsures P Safe body Q) :
    Ensures (fun h (w : World)=>P h w.wg w.ambient) Safe (liftWGObserver body)
      (fun value h w=>Q value h w.wg w.ambient) :=
  StatePrefixEnsures.liftWGObserver checked

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix
