import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreateCompositionCalls

/-! Atomic call contexts in the fixed creation tree. A context contains only
the original bind path and successful preceding calls. It cannot introduce
an arbitrary factorization or a replacement creation invocation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateComposition
open Leanux Leanux.Proofs.Logged CausalJournal CreatePoints CreatePhase

inductive AtomCall : {α β : Type} → {action : PrefixM Event α} →
    Shape action → World → List Event → (token : Atom β) → World → List Event →
    (PrefixM Event β → PrefixM Event α) → Type 1 where
  | here (token : Atom β) : AtomCall (.atom token) w h token w h id
  | left {body : PrefixM Event α} {next : α → PrefixM Event β} {head : Shape body}
      (tail : ∀ value,Shape (next value)) (call : AtomCall head w h token v middle context) :
      AtomCall (.bind head tail) w h token v middle (fun rest=>context rest >>= next)
  | right {body : PrefixM Event α} {next : α → PrefixM Event β} (head : Shape body)
      (tail : ∀ value,Shape (next value))
      (leading : runPrefix body w h=(.ok (value,u),prior))
      (call : AtomCall (tail value) u prior token v middle context) :
      AtomCall (.bind head tail) w h token v middle context
  | marked (label : Label) (call : AtomCall shape w h token v middle context) :
      AtomCall (.marked label shape) w h token v middle context

theorem AtomCall.entry {shape : Shape action} (call : AtomCall shape w h token v middle context)
    (covered : Covers E shape w h) : E middle v := by
  induction call with
  | here=>exact covered.1
  | left tail call ih=>exact ih covered.1
  | right head tail leading call ih=>exact ih (covered.2 _ _ _ leading)
  | marked label call ih=>exact ih covered

theorem AtomCall.resume {shape : Shape action}
    (call : AtomCall shape w h token v middle context)
    (child : runPrefix token.action v middle=runPrefix rest u last) :
    runPrefix action w h=runPrefix (context rest) u last := by
  induction call with
  | here=>exact child
  | left tail call ih=>rw [runPrefix_bind,runPrefix_bind,ih child]
  | right head tail leading call ih=>rw [runPrefix_bind,leading]; exact ih child
  | marked label call ih=>exact ih child

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateComposition
