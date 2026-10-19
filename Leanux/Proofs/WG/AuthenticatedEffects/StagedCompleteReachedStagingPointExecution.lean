import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointSource

/-! Finite actual executions of a fixed staging shape. Successful bind
prerequisites carry their exact worlds, clocks and histories. Stopped
branches have a reason and retained history, never a returned world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
open Leanux Leanux.WG Leanux.Proofs.Logged CausalJournal
set_option maxHeartbeats 600000

inductive Execution : {α : Type} → {action : WGPrefix Event α} →
    Shape action → WGWorld → Ambient → History → Result α → History → Prop where
  | pure (value : α) : Execution (.pure value) w a h (.ok ((value,w),a)) h
  | native (token : Native α)
      (performed : runWGPrefix (liftWGPrefix token.action) w a h=(result,last)) :
      Execution (.native token) w a h result last
  | child (token : Child action) (performed : runWGPrefix action w a h=(result,last)) :
      Execution (.child token) w a h result last
  | stopped {body : WGPrefix Event α} {next : α → WGPrefix Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value))
      (leading : Execution head w a h (.error reason) last) :
      Execution (.bind head tail) w a h (.error reason) last
  | continued {body : WGPrefix Event α} {next : α → WGPrefix Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value))
      (leading : Execution head w a h (.ok ((value,u),b)) middle)
      (remaining : Execution (tail value) u b middle result last) :
      Execution (.bind head tail) w a h result last
  | receiptStopped (record : WGRunWitness α → Event) (shape : Shape action)
      (trace : Execution shape w a h (.error reason) last) :
      Execution (.receipt record shape) w a h (.error reason) last
  | receiptReturned (record : WGRunWitness α → Event) (shape : Shape action)
      (trace : Execution shape w a h (.ok ((value,u),b)) middle) :
      Execution (.receipt record shape) w a h (.ok ((value,u),b))
        (middle++[record ⟨value,w,u,a,b⟩])
  | marked (label : Label) (trace : Execution shape w a h result last) :
      Execution (.marked label shape) w a h result last

theorem run_bind (body : WGPrefix Event α) (next : α → WGPrefix Event β) {w : WGWorld} {a : Ambient} {h : History} :
    runWGPrefix (body >>= next) w a h=
      match runWGPrefix body w a h with
      | (.error reason,last)=>(.error reason,last)
      | (.ok ((value,u),b),middle)=>runWGPrefix (next value) u b middle :=
by
  simp only [runWGPrefix,runStatePrefix_bind]
  cases runStatePrefix body w a h with
  | mk out last=>cases out with
    | error=>rfl
    | ok pair=>obtain ⟨⟨value,u⟩,b⟩:=pair; rfl

theorem Execution.run {shape : Shape action} (trace : Execution shape w a h result last) :
    runWGPrefix action w a h=(result,last) := by
  induction trace with
  | pure=>rfl
  | native token performed=>exact performed
  | child token performed=>exact performed
  | stopped head tail leading ih=>rw [run_bind,ih]
  | continued head tail leading remaining ihLeading ihRemaining=>rw [run_bind,ihLeading]; exact ihRemaining
  | receiptStopped record shape trace ih=>rw [runWGPrefix_receiptWGObserved,ih]
  | receiptReturned record shape trace ih=>rw [runWGPrefix_receiptWGObserved,ih]
  | marked label trace ih=>exact ih

theorem execution_cases (shape : Shape action)
    (performed : runWGPrefix action w a h=(result,last)) :
    Execution shape w a h result last := by
  induction shape generalizing w a h last with
  | pure value=>cases performed; exact .pure value
  | native token=>exact .native token performed
  | child token=>exact .child token performed
  | bind head tail ihHead ihTail=>
    rw [run_bind] at performed
    cases leading : runWGPrefix _ w a h with
    | mk out middle=>
      rw [leading] at performed
      cases out with
      | error reason=>cases performed; exact .stopped head tail (ihHead leading)
      | ok pair=>
        obtain ⟨⟨value,u⟩,b⟩:=pair
        exact .continued head tail (ihHead leading) (ihTail value performed)
  | receipt record shape ih=>
    rw [runWGPrefix_receiptWGObserved] at performed
    cases body : runWGPrefix _ w a h with
    | mk out middle=>
      rw [body] at performed
      cases out with
      | error reason=>cases performed; exact .receiptStopped record shape (ih body)
      | ok pair=>
        obtain ⟨⟨value,u⟩,b⟩:=pair
        cases performed
        exact .receiptReturned record shape (ih body)
  | marked label shape ih=>exact .marked label (ih performed)

theorem execution_iff (shape : Shape action) :
    Execution shape w a h result last ↔ runWGPrefix action w a h=(result,last) :=
  ⟨Execution.run,execution_cases shape⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
