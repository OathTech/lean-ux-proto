import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseCoverage

/-! Child-call contexts of the fixed creation tree. Right contexts retain
their actual successful left run; continuation substitution is a consequence
of that source path and cannot introduce a new call. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateComposition
open Leanux Leanux.Proofs.Logged CausalJournal CreatePoints CreatePhase

inductive Call : {α β : Type} → {action : PrefixM Event α} → {childAction : PrefixM Event β} →
    Shape action → World → (List Event) → Child childAction → World → (List Event) →
    (PrefixM Event β → PrefixM Event α) → Type 1 where
  | here (token : Child childAction) : Call (.child token) w h token w h id
  | left {childAction : PrefixM Event α} {next : α → PrefixM Event β} {head : Shape childAction}
      (tail : ∀ value,Shape (next value)) (call : Call head w h token v middle context) :
      Call (.bind head tail) w h token v middle (fun rest=>context rest >>= next)
  | right {childAction : PrefixM Event α} {next : α → PrefixM Event β} (head : Shape childAction)
      (tail : ∀ value,Shape (next value))
      (leading : runPrefix childAction w h=(.ok (value,u),prior))
      (call : Call (tail value) u prior token v middle context) :
      Call (.bind head tail) w h token v middle context
  | marked (label : Label) (call : Call shape w h token v middle context) :
      Call (.marked label shape) w h token v middle context

theorem Call.entry {shape : Shape action} (call : Call shape w h token v middle context)
    (covered : Covers E shape w h) : E middle v := by
  induction call with
  | here=>exact covered.1
  | left tail call ih=>exact ih covered.1
  | right head tail leading call ih=>exact ih (covered.2 _ _ _ leading)
  | marked label call ih=>exact ih covered

theorem Call.resume {shape : Shape action} {token : Child childAction}
    (call : Call shape w h token v middle context)
    (child : runPrefix childAction v middle=runPrefix rest u last) :
    runPrefix action w h=runPrefix (context rest) u last := by
  induction call with
  | here=>exact child
  | left tail call ih=>rw [runPrefix_bind,runPrefix_bind,ih child]
  | right head tail leading call ih=>rw [runPrefix_bind,leading]; exact ih child
  | marked label call ih=>exact ih child

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateComposition
