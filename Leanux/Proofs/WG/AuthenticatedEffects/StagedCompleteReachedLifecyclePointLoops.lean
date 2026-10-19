import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointContract

/-! Empty/end, early done, continued yield, and stopped cases for the literal
finite ranges. The list witness contains every actual source step in order. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

variable {body : ι → σ → PrefixM Event (ForInStep σ)}
variable {positions : List ι}

theorem listShape_nil (initial : σ) (shapes : ∀ index acc, Shape (body index acc)) :
    listShape [] initial body shapes = .pure initial := rfl

noncomputable def consShape (index : ι) (rest : List ι) (initial : σ)
    (shapes : ∀ index acc, Shape (body index acc)) :
    Shape (forIn (index :: rest) initial body) :=
  (List.forIn_cons body index rest initial).symm ▸
    Shape.bind (shapes index initial) (fun decision => match decision with
      | .done final => .pure final
      | .yield next => listShape rest next body shapes)

theorem listShape_cons (index : ι) (rest : List ι) (initial : σ)
    (shapes : ∀ index acc, Shape (body index acc)) :
    listShape (index :: rest) initial body shapes = consShape index rest initial shapes := rfl

theorem Point.source_cast {α : Type} {left right : PrefixM Event α}
    (same : left = right) {shape : Shape left}
    (point : Point inside shape w h site u middle) :
    Point inside (same ▸ shape) w h site u middle := by
  cases same
  exact point

theorem Point.source_mpr {α : Type} {left right : PrefixM Event α}
    (same : left = right) {shape : Shape right}
    (point : Point inside shape w h site u middle) :
    Point inside ((congrArg Shape same).mpr shape) w h site u middle := by
  cases same
  exact point

inductive LoopExecution (shapes : ∀ index acc, Shape (body index acc)) :
    List ι → σ → World → History → Result σ → History → Prop where
  | nil : LoopExecution shapes [] acc w h (.ok (acc,w)) h
  | stopped (current : Execution (shapes index acc) w h (.error reason) last) :
      LoopExecution shapes (index :: rest) acc w h (.error reason) last
  | done (current : Execution (shapes index acc) w h (.ok (.done final,u)) last) :
      LoopExecution shapes (index :: rest) acc w h (.ok (final,u)) last
  | yielded (current : Execution (shapes index acc) w h (.ok (.yield next,u)) middle)
      (remaining : LoopExecution shapes rest next u middle result last) :
      LoopExecution shapes (index :: rest) acc w h result last

theorem LoopExecution.run {shapes : ∀ index acc, Shape (body index acc)} (trace : LoopExecution shapes positions acc w h result last) :
    runPrefix (forIn positions acc body) w h = (result,last) := by
  induction trace with
  | nil => rfl
  | stopped current => rw [List.forIn_cons,runPrefix_bind,current.run]
  | done current => rw [List.forIn_cons,runPrefix_bind,current.run]; rfl
  | yielded current remaining ih => rw [List.forIn_cons,runPrefix_bind,current.run]; exact ih

theorem loop_cases (shapes : ∀ index acc, Shape (body index acc))
    (performed : runPrefix (forIn positions acc body) w h = (result,last)) :
    LoopExecution shapes positions acc w h result last := by
  induction positions generalizing acc w h with
  | nil => simp only [List.forIn_nil,runPrefix_pure] at performed; cases performed; exact .nil
  | cons index rest ih =>
      rw [List.forIn_cons,runPrefix_bind] at performed
      cases current : runPrefix (body index acc) w h with
      | mk out middle =>
          rw [current] at performed
          cases out with
          | error reason => cases performed; exact .stopped (execution_cases _ current)
          | ok pair =>
              obtain ⟨decision,u⟩ := pair
              cases decision with
              | done final =>
                  simp only [runPrefix_pure] at performed
                  cases performed
                  exact .done (execution_cases _ current)
              | yield next =>
                  exact .yielded (execution_cases _ current) (ih performed)

/-- Every point of an actually entered list item lifts through the original
completed yield prefix. An early done has no recursive continuation constructor. -/
inductive LoopVisit (shapes : ∀ index acc, Shape (body index acc)) :
    List ι → σ → World → History → ι → σ → World → History → Prop where
  | here : LoopVisit shapes (index :: rest) acc w h index acc w h
  | after {currentState : σ} (leading : runPrefix (body index acc) w h = (.ok (.yield next,u),middle))
      (later : LoopVisit shapes rest next u middle selected currentState v last) :
      LoopVisit shapes (index :: rest) acc w h selected currentState v last

theorem LoopVisit.point {shapes : ∀ index acc, Shape (body index acc)} {currentState : σ} (visit : LoopVisit shapes positions acc w h index currentState u middle)
    (point : Point inside (shapes index currentState) u middle site v last) :
    ∃ enclosingSite, Point inside (listShape positions acc body shapes) w h enclosingSite v last := by
  induction visit with
  | here =>
      rw [listShape_cons]
      refine ⟨.left site,?_⟩
      exact Point.source_cast (List.forIn_cons ..).symm (.left _ point)
  | after leading later ih =>
      obtain ⟨enclosingSite,lifted⟩ := ih point
      rw [listShape_cons]
      refine ⟨.right enclosingSite,?_⟩
      exact Point.source_cast (List.forIn_cons ..).symm (.right _ _ leading lifted)

theorem LoopVisit.entry {shapes : ∀ index acc, Shape (body index acc)} {currentState : σ} (visit : LoopVisit shapes positions acc w h index currentState u middle) :
    ∃ site, Point inside (listShape positions acc body shapes) w h site u middle :=
  visit.point (.entry _)

/-- A visit supplies the original ordered prefix, its actual successful run,
and the still-unexecuted list suffix. No completed enclosing run is assumed. -/
theorem LoopVisit.prefix {shapes : ∀ index acc, Shape (body index acc)} {currentState : σ}
    (visit : LoopVisit shapes positions acc w h index currentState u middle) :
    ∃ before after, positions = before ++ index :: after ∧
      runPrefix (forIn before acc body) w h = (.ok (currentState,u),middle) := by
  induction visit with
  | here => exact ⟨[],_,rfl,rfl⟩
  | @after index acc w h next u middle rest selected final v last leading later ih =>
      obtain ⟨before,after,equal,performed⟩ := ih
      refine ⟨index :: before,after,?_,?_⟩
      · simp only [List.cons_append,equal]
      · rw [List.forIn_cons,runPrefix_bind,leading]
        exact performed

theorem LoopVisit.member {shapes : ∀ index acc, Shape (body index acc)} {currentState : σ}
    (visit : LoopVisit shapes positions acc w h index currentState u middle) : index ∈ positions := by
  obtain ⟨before,after,equal,_⟩ := visit.prefix
  rw [equal]
  simp


end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
