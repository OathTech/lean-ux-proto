import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointCanonical

/-! Every original normal or stopped result decomposes through the fixed
source. Right-hand binds require the literal successful left-hand execution;
failed calls have history but no returned WG world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.Proofs.Logged

abbrev Outcome (α : Type) := Except Stop ((α×WGWorld)×Ambient)

inductive Execution : {E α : Type} → {action : WGPrefix E α} → Shape action →
    WGWorld → Ambient → List E → Outcome α → List E → Prop where
  | pure {E α : Type} (value : α) (w : WGWorld) (a : Ambient) (h : List E) :
      Execution (.pure value) w a h (.ok ((value,w),a)) h
  | quiet {E α : Type} (body : WG.M α) (frame : Leanux.Proofs.Framing.SameView StagedEntry.view body)
      {w : WGWorld} {a : Ambient} {h last : List E} {result : Outcome α}
      (performed : runWGPrefix (liftWGPrefix body) w a h=(result,last)) :
      Execution (.quiet body frame) w a h result last
  | access {E α : Type} {body : WGPrefix E α} (token : Access body)
      {w : WGWorld} {a : Ambient} {h last : List E} {result : Outcome α}
      (performed : runWGPrefix body w a h=(result,last)) : Execution (.access token) w a h result last
  | stopped {E α β : Type} {body : WGPrefix E α} {next : α→WGPrefix E β}
      (head : Shape body) (tail : ∀value,Shape (next value))
      {w : WGWorld} {a : Ambient} {h last : List E} {reason : Stop}
      (leading : Execution head w a h (.error reason) last) :
      Execution (.bind head tail) w a h (.error reason) last
  | continued {E α β : Type} {body : WGPrefix E α} {next : α→WGPrefix E β}
      (head : Shape body) (tail : ∀value,Shape (next value))
      {w u : WGWorld} {a c : Ambient} {h middle last : List E} {value : α} {result : Outcome β}
      (leading : Execution head w a h (.ok ((value,u),c)) middle)
      (remaining : Execution (tail value) u c middle result last) :
      Execution (.bind head tail) w a h result last
  | focus {E F α : Type} {body : WGPrefix E α} (encode : E→F) (decode : F→Option E)
      (inverse : ∀event,decode (encode event)=some event) (shape : Shape body)
      {w : WGWorld} {a : Ambient} {h : List F} {middle : List E} {result : Outcome α}
      (trace : Execution shape w a (h.filterMap decode) result middle) :
      Execution (.focus encode decode inverse shape) w a h result
        (h++(middle.drop (h.filterMap decode).length).map encode)
  | receiptStopped {E α : Type} {body : WGPrefix E α} (shape : Shape body) (record : WGRunWitness α→E)
      {w : WGWorld} {a : Ambient} {h last : List E} {reason : Stop}
      (trace : Execution shape w a h (.error reason) last) :
      Execution (.receipt shape record) w a h (.error reason) last
  | receiptReturned {E α : Type} {body : WGPrefix E α} (shape : Shape body) (record : WGRunWitness α→E)
      {w v : WGWorld} {a b : Ambient} {h middle : List E} {value : α}
      (trace : Execution shape w a h (.ok ((value,v),b)) middle) :
      Execution (.receipt shape record) w a h (.ok ((value,v),b))
        (middle++[record ⟨value,w,v,a,b⟩])

theorem Execution.run {E α : Type} {action : WGPrefix E α} {shape : Shape action}
    {w : WGWorld} {a : Ambient} {h last : List E} {result : Outcome α}
    (trace : Execution shape w a h result last) : runWGPrefix action w a h=(result,last) := by
  induction trace with
  | pure => rfl
  | quiet body frame performed => exact performed
  | access token performed => exact performed
  | stopped head tail trace ih =>
      change runStatePrefix _ _ _ _ = _
      rw [runStatePrefix_bind]
      change runStatePrefix _ _ _ _ = _ at ih
      rw [ih]
  | continued head tail leading remaining ihLeading ihRemaining =>
      change runStatePrefix _ _ _ _ = _
      rw [runStatePrefix_bind]
      change runStatePrefix _ _ _ _ = _ at ihLeading
      rw [ihLeading]
      exact ihRemaining
  | focus encode decode inverse shape trace ih =>
      change ((runWGPrefix _ _ _ _).1,_++((runWGPrefix _ _ _ _).2.drop _).map _)=_
      rw [ih]
  | receiptStopped shape record trace ih => rw [runWGPrefix_receiptWGObserved,ih]
  | receiptReturned shape record trace ih => rw [runWGPrefix_receiptWGObserved,ih]

theorem execution_cases {E α : Type} {action : WGPrefix E α} (shape : Shape action)
    {w : WGWorld} {a : Ambient} {h last : List E} {result : Outcome α}
    (performed : runWGPrefix action w a h=(result,last)) : Execution shape w a h result last := by
  induction shape generalizing w a with
  | pure value => cases performed; exact .pure _ _ _ _
  | quiet body frame => exact .quiet body frame performed
  | access token => exact .access token performed
  | @bind E α β body next head tail ihHead ihTail =>
      change runStatePrefix _ w a h = _ at performed
      rw [runStatePrefix_bind] at performed
      cases leading : runStatePrefix body w a h with
      | mk out middle =>
          rw [leading] at performed
          cases out with
          | error reason => cases performed; exact .stopped head tail (ihHead leading)
          | ok out => obtain ⟨⟨value,u⟩,c⟩:=out; exact .continued head tail (ihHead leading) (ihTail value performed)
  | @focus E F α body encode decode inverse shape ih =>
      change ((runWGPrefix body w a (h.filterMap decode)).1,_++((runWGPrefix body w a (h.filterMap decode)).2.drop _).map _)=_ at performed
      cases leading : runWGPrefix body w a (h.filterMap decode) with
      | mk out middle =>
          rw [leading] at performed
          cases performed
          exact .focus encode decode inverse shape (ih leading)
  | @receipt E α body shape record ih =>
      rw [runWGPrefix_receiptWGObserved] at performed
      cases leading : runWGPrefix body w a h with
      | mk out middle =>
          rw [leading] at performed
          cases out with
          | error reason => cases performed; exact .receiptStopped shape record (ih leading)
          | ok out => obtain ⟨⟨value,v⟩,b⟩:=out; cases performed; exact .receiptReturned shape record (ih leading)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
