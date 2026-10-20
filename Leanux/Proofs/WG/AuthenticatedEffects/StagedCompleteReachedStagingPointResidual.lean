import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointExecution
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingAmbientSource

/-! Points are positions in the fixed source witness, not arbitrary factors.
A right bind point includes the successful original left run. Receipt-body
points save the original before-world/clock in their remaining emission. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
open Leanux Leanux.WG Leanux.Proofs.Logged CausalJournal
set_option maxHeartbeats 600000

/-- Literal completed-capture suffix, before its existing journal event. -/
def pendingReceipt (record : WGRunWitness α → Event) (before : WGWorld) (clock : Ambient)
    (value : α) (after : WGWorld) (later : Ambient) : WGPrefix Event α := do
  emitStatePrefix (record ⟨value,before,after,clock,later⟩)
  pure value

def savedReceipt (record : WGRunWitness α → Event) (before : WGWorld) (clock : Ambient)
    (remaining : WGPrefix Event α) : WGPrefix Event α :=
  receiptWGObserved remaining (fun run=>record {run with before,ambientBefore:=clock})

inductive Point : {α : Type} → {action : WGPrefix Event α} → Shape action →
    WGWorld → Ambient → History → {β : Type} → WGPrefix Event β → WGWorld → Ambient → History → WGPrefix Event α → Type 1 where
  | entry (shape : Shape action) : Point shape w a h action w a h action
  | returned (shape : Shape action)
      (performed : runWGPrefix action w a h=(.ok ((value,u),b),middle)) :
      Point shape w a h (pure value) u b middle (pure value)
  | getter {α : Type} {token : Native α} (getter : Getter token)
      (point : ReadGetter.Point getter.source w a v b) :
      Point (.native token) w a h (ReadGetter.prefixRemainder point) v b h (ReadGetter.prefixRemainder point)
  | left {body : WGPrefix Event α} {next : α → WGPrefix Event β}
      {head : Shape body} (tail : ∀ value, Shape (next value)) (point : Point head w a h leaf u b middle remaining) :
      Point (.bind head tail) w a h leaf u b middle (remaining >>= next)
  | right {body : WGPrefix Event α} {next : α → WGPrefix Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value))
      (leading : runWGPrefix body w a h=(.ok ((value,v),c),prior))
      (point : Point (tail value) v c prior leaf u b middle remaining) :
      Point (.bind head tail) w a h leaf u b middle remaining
  | receiptBody (record : WGRunWitness α → Event)
      (point : Point shape w a h leaf u b middle remaining) :
      Point (.receipt record shape) w a h leaf u b middle (savedReceipt record w a remaining)
  | pending (record : WGRunWitness α → Event) (shape : Shape action)
      (performed : runWGPrefix action w a h=(.ok ((value,u),b),middle)) :
      Point (.receipt record shape) w a h (pendingReceipt record w a value u b) u b middle
        (pendingReceipt record w a value u b)
  | marked (label : Label) (point : Point shape w a h leaf u b middle remaining) :
      Point (.marked label shape) w a h leaf u b middle remaining

theorem Point.residual {shape : Shape action}
    (point : Point shape w a h leaf u b middle remaining) :
    runWGPrefix action w a h=runWGPrefix remaining u b middle := by
  induction point with
  | entry=>rfl
  | returned shape performed=>exact performed
  | getter getter point=>exact ReadGetter.prefixRemainder_run _ point
  | left tail point ih=>
    rw [run_bind,run_bind,ih]
  | right head tail leading point ih=>
    rw [run_bind,leading]
    exact ih
  | receiptBody record point ih=>
    dsimp only [savedReceipt]
    rw [runWGPrefix_receiptWGObserved,runWGPrefix_receiptWGObserved,ih]
  | pending record shape performed=>
    rw [runWGPrefix_receiptWGObserved,performed]
    rfl
  | marked label point ih=>exact ih

/-- A stopped residual retains the same reason and journal. There is no
world parameter attached to the error, nor a fabricated post-error cut. -/
theorem Point.stopped {shape : Shape action}
    (point : Point shape w a h leaf u b middle remaining)
    (failed : runWGPrefix remaining u b middle=(.error stop,last)) :
    runWGPrefix action w a h=(.error stop,last) := point.residual.trans failed

theorem Point.normal {shape : Shape action}
    (point : Point shape w a h leaf u b middle remaining)
    (returned : runWGPrefix remaining u b middle=(.ok ((value,v),c),last)) :
    runWGPrefix action w a h=(.ok ((value,v),c),last) := point.residual.trans returned

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
