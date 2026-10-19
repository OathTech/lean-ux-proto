import Leanux.Proofs.Logged.WGPrefix

/-! Composition algebra for a supplied monadic source decomposition. A
successful left prefix determines the state and history at its right-hand cut.
This algebra does not certify that an arbitrary extensional factorization is
one of the mirror's actual source cuts. A concrete source interval or recorded
snapshot must supply that separate provenance obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.Proofs.Logged

/-- A callback entry in the supplied bind decomposition. The right
constructor retains the successful prefix's state and journal. This predicate
alone is not a certificate of native source-site provenance. -/
inductive At {E State : Type} {β : Type} (cut : PrefixT E State β)
    (cutWorld : State) (cutHistory : List E) :
    {α : Type} → PrefixT E State α → State → List E → Prop where
  | here : At cut cutWorld cutHistory cut cutWorld cutHistory
  | left {body : PrefixT E State α} {next : α → PrefixT E State γ}
      (entry : At cut cutWorld cutHistory body w history) :
      At cut cutWorld cutHistory (body >>= next) w history
  | right {body : PrefixT E State α} {next : α → PrefixT E State γ}
      (prefixRun : runPrefix body w history = (.ok (value,v),after))
      (entry : At cut cutWorld cutHistory (next value) v after) :
      At cut cutWorld cutHistory (body >>= next) w history

/-- A failure at the reached callback is the failure of the enclosing
source, with exactly the same retained journal. -/
theorem At.failure (entry : At cut cutWorld cutHistory body w history)
    (failed : runPrefix cut cutWorld cutHistory = (.error reason,last)) :
    runPrefix body w history = (.error reason,last) := by
  induction entry with
  | here => exact failed
  | left _ ih => rw [runPrefix_bind,ih]
  | right performed _ ih => rw [runPrefix_bind,performed]; exact ih

/-- Nested source evidence composes without forgetting the native cut. -/
theorem At.trans (outer : At middle midWorld midHistory body w history)
    (inner : At cut cutWorld cutHistory middle midWorld midHistory) :
    At cut cutWorld cutHistory body w history := by
  induction outer with
  | here => exact inner
  | left _ ih => exact .left ih
  | right performed _ ih => exact .right performed ih

/-- Source equality may expose a factored callback, but equality of final
states or erasure of histories is not used as source-entry evidence. -/
theorem At.source_eq (entry : At cut cutWorld cutHistory body w history)
    (source : body = original) : At cut cutWorld cutHistory original w history :=
  source ▸ entry

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
