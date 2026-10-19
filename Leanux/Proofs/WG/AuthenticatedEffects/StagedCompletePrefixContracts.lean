import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixHistory

/-! Source contracts carry the prefix certificate beside the native endpoint
invariant. Existing endpoint contracts need an independent internal-cut proof
before they can be upgraded. Nothing reconstructs earlier native worlds. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix
open Leanux Leanux.Proofs.Logged

def With (P : List E→State→Prop) (Safe : List E→Prop) (h : List E) (w : State) : Prop :=
  P h w ∧ All Safe h

abbrev Ensures (P : List E→State→Prop) (Safe : List E→Prop)
    (body : PrefixT E State α) (Q : α→List E→State→Prop) : Prop :=
  PrefixEnsures (With P Safe) (All Safe) body (fun value=>With (Q value) Safe)

variable {P : List E→State→Prop} {Safe : List E→Prop}
variable {Q : α→List E→State→Prop} {R : β→List E→State→Prop}
variable {body : PrefixT E State α} {next : α→PrefixT E State β}

theorem Ensures.bind (head : Ensures P Safe body Q) (tail : ∀ x, Ensures (Q x) Safe (next x) R) :
    Ensures P Safe (body >>= next) R := PrefixEnsures.bind head tail

theorem Ensures.pure (value : α) (post : ∀ h w, P h w→Q value h w) :
    Ensures P Safe (pure value) Q :=
  PrefixEnsures.pure (fun _ _ before=>before.2)
    (fun h w before=>⟨post h w before.1,before.2⟩)

theorem Ensures.lift (native : StateT State (Except Stop) α)
    (post : ∀ h w value v, P h w→native.run w=.ok (value,v)→Q value h v) :
    Ensures P Safe (liftPrefix native) Q :=
  PrefixEnsures.lift native (fun _ _ before=>before.2)
    (fun h w value v before run=>⟨post h w value v before.1 run,before.2⟩)

/-- The new singleton must be safe at its actual emitter entry. The prior
certificate accounts for the earlier positions, independently of the new one. -/
theorem Ensures.emit {Post : Unit→List E→State→Prop} (event : E)
    (safe : ∀ h w, P h w→Safe (h++[event]))
    (post : ∀ h w, P h w→Post () (h++[event]) w) :
    Ensures P Safe (emitPrefix event) Post := by
  intro w h before
  have all := before.2.append (Cuts.singleton before.2.last (safe h w before.1))
  exact ⟨[event],rfl,all,post h w before.1,all⟩

theorem Ensures.consequence (checked : Ensures P Safe body Q)
    (pre : ∀ h w, P' h w→P h w) (post : ∀ x h w, Q x h w→Q' x h w) :
    Ensures P' Safe body Q' :=
  PrefixEnsures.consequence checked (fun h w before=>⟨pre h w before.1,before.2⟩)
    (fun x h w after=>⟨post x h w after.1,after.2⟩)

/-- Endpoint safety is insufficient here. The additional premise certifies
every newly appended cut of this very execution, including stopped outcomes. -/
theorem Ensures.of_cuts (endpoint : PrefixEnsures P Safe body Q)
    (cuts : ∀ w h, P h w→∃ suffix, (runPrefix body w h).2=h++suffix ∧ Cuts Safe h suffix) :
    Ensures P Safe body Q := by
  intro w h before
  obtain ⟨suffix,extended,_,kept⟩ := endpoint w h before.1
  obtain ⟨added,equation,certified⟩ := cuts w h before.1
  have all : All Safe (runPrefix body w h).2 := equation ▸ before.2.append certified
  refine ⟨suffix,extended,all,?_⟩
  cases result : (runPrefix body w h).1 with
  | error reason => trivial
  | ok out =>
    rcases out with ⟨value,v⟩
    rw [result] at kept
    exact ⟨kept,all⟩

theorem Ensures.forIn (xs : List α) (initial : β)
    (action : α→β→PrefixT E State (ForInStep β)) (I : β→List E→State→Prop)
    (checked : ∀ value acc, Ensures (I acc) Safe (action value acc) (fun step=>I step.value)) :
    Ensures (I initial) Safe (forIn xs initial action) I :=
  PrefixEnsures.forInInvariant xs initial action (fun acc=>With (I acc) Safe) (All Safe)
    (fun _ _ _ before=>before.2) checked

/-- Every output prefix is exposed regardless of the final outcome. This
statement asserts no native endpoint for an internal stopped computation. -/
theorem Ensures.output (checked : Ensures P Safe body Q) (before : P h w)
    (history : All Safe h) : All Safe (runPrefix body w h).2 :=
  (checked w h ⟨before,history⟩).choose_spec.2.1

theorem Ensures.at_prefix (checked : Ensures P Safe body Q) (before : P h w)
    (history : All Safe h) (position : (runPrefix body w h).2=earlier++later) : Safe earlier :=
  (checked.output before history).at_prefix position

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix
