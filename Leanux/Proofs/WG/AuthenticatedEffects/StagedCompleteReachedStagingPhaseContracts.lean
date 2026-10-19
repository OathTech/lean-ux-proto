import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointContract

/-! Semantic coverage follows the fixed staging tree, including the saved
before-state at a completed receipt. The pre-emission point is covered by
the body certificate; receipt admission is a separate transition. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged CausalJournal Staging.Points
set_option maxHeartbeats 600000

def Covers (E : Staging.Points.History → WGWorld → Ambient → Prop) :
    {α : Type} → {action : WGPrefix Event α} → Shape action → WGWorld → Ambient → Staging.Points.History → Prop
  | _,_,.pure _,w,a,h=>E h w a
  | _,_,.native token,w,a,h=>E h w a ∧ ∀ value u b middle,
      runWGPrefix (liftWGPrefix token.action) w a h=(.ok ((value,u),b),middle) → E middle u b
  | _,action,.child _,w,a,h=>E h w a ∧ ∀ value u b middle,
      runWGPrefix action w a h=(.ok ((value,u),b),middle) → E middle u b
  | _,_,@Shape.bind _ _ body _ head tail,w,a,h=>Covers E head w a h ∧ ∀ value u b middle,
      runWGPrefix body w a h=(.ok ((value,u),b),middle) → Covers E (tail value) u b middle
  | _,_,@Shape.receipt _ body record shape,w,a,h=>Covers E shape w a h ∧ ∀ value u b middle,
      runWGPrefix body w a h=(.ok ((value,u),b),middle) → E (middle++[record ⟨value,w,u,a,b⟩]) u b
  | _,_,.marked _ body,w,a,h=>Covers E body w a h

theorem Covers.entry {shape : Shape action} (safe : Covers E shape w a h) : E h w a := by
  induction shape with
  | pure=>exact safe
  | native=>exact safe.1
  | child=>exact safe.1
  | bind head tail ih _=>exact ih safe.1
  | receipt record body ih=>exact ih safe.1
  | marked label body ih=>exact ih safe

theorem Covers.normal {shape : Shape action} (safe : Covers E shape w a h)
    (performed : runWGPrefix action w a h=(.ok ((value,u),b),middle)) : E middle u b := by
  induction shape generalizing w a h with
  | pure returned=>cases performed; exact safe
  | native token=>exact safe.2 _ _ _ _ performed
  | child token=>exact safe.2 _ _ _ _ performed
  | bind head tail ih rest=>
    rw [run_bind] at performed
    rename_i body next
    cases leading : runWGPrefix body w a h with
    | mk out prior=>
      rw [leading] at performed
      cases out with
      | error=>cases performed
      | ok pair=>
        obtain ⟨⟨value,v⟩,c⟩:=pair
        exact rest value (safe.2 value v c prior leading) performed
  | receipt record shape ih=>
    rw [runWGPrefix_receiptWGObserved] at performed
    rename_i body
    cases leading : runWGPrefix body w a h with
    | mk out prior=>
      rw [leading] at performed
      cases out with
      | error=>cases performed
      | ok pair=>
        obtain ⟨⟨value,v⟩,c⟩:=pair
        cases performed
        exact safe.2 _ _ _ _ leading
  | marked label body ih=>exact ih safe performed

theorem Covers.point {shape : Shape action} (safe : Covers E shape w a h)
    (point : Point shape w a h leaf u b middle remaining) : E middle u b := by
  induction point with
  | entry=>exact safe.entry
  | returned shape performed=>exact safe.normal performed
  | left tail point ih=>exact ih safe.1
  | right head tail leading point ih=>exact ih (safe.2 _ _ _ _ leading)
  | receiptBody record point ih=>exact ih safe.1
  | pending record shape performed=>exact safe.1.normal performed
  | marked label point ih=>exact ih safe

theorem Covers.mono {shape : Shape action} (safe : Covers E shape w a h)
    (imp : ∀ h w a,E h w a → F h w a) : Covers F shape w a h := by
  induction shape generalizing w a h with
  | pure=>exact imp _ _ _ safe
  | native=>exact ⟨imp _ _ _ safe.1,fun x u b k run=>imp _ _ _ (safe.2 x u b k run)⟩
  | child=>exact ⟨imp _ _ _ safe.1,fun x u b k run=>imp _ _ _ (safe.2 x u b k run)⟩
  | bind head tail ih rest=>exact ⟨ih safe.1,fun x u b k run=>rest x (safe.2 x u b k run)⟩
  | receipt record body ih=>exact ⟨ih safe.1,fun x u b k run=>imp _ _ _ (safe.2 x u b k run)⟩
  | marked label body ih=>exact ih safe

theorem covers_bind {body : WGPrefix Event α} {next : α → WGPrefix Event β}
    {head : Shape body} {tail : ∀ value,Shape (next value)} (first : Covers E head w a h)
    (rest : ∀ value u b middle,runWGPrefix body w a h=(.ok ((value,u),b),middle) → Covers E (tail value) u b middle) :
    Covers E (.bind head tail) w a h := ⟨first,rest⟩

theorem covers_type_cast {left right : WGPrefix Event α}
    (types : Shape left=Shape right) (same : left=right) (shape : Shape left) :
    Covers E (cast types shape) w a h=Covers E shape w a h := by
  cases same
  rfl

theorem covers_mpr {left right : WGPrefix Event α} (same : left=right) (shape : Shape right) :
    Covers E (Eq.mpr (congrArg Shape same) shape) w a h=Covers E shape w a h := by
  cases same
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
