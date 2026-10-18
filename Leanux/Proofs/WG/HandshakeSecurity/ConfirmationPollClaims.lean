import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationPollObservation
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationClaims

namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Poll
open Leanux Leanux.WG Leanux.Proofs.Logged

private theorem silent {α : Type} (action : WG.M α) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (liftWGPrefix action : WGPrefix Receipt α) :=
  StatePrefixEnsures.lift _ (fun _ _ _ hi => hi) (fun _ _ _ _ _ _ hi _ => hi)

private theorem pure_safe {α : Type} (x : α) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (pure x : WGPrefix Receipt α) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi) (fun _ _ _ hi => hi)

private theorem safe_if {α : Type} (c : Prop) [Decidable c]
    (x y : WGPrefix Receipt α)
    (hx : StatePrefixPreserves (fun h _ _ => Valid h) Valid x)
    (hy : StatePrefixPreserves (fun h _ _ => Valid h) Valid y) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (if c then x else y) := by
  split <;> assumption

private theorem safe_list {α β : Type} (xs : List α) (b : β)
    (g : α → β → WGPrefix Receipt (ForInStep β))
    (hg : ∀ x b, StatePrefixPreserves (fun h _ _ => Valid h) Valid (g x b)) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (forIn xs b g) :=
  StatePrefixEnsures.forInInvariant xs b g (fun _ h _ _ => Valid h) Valid
    (fun _ _ _ _ hi => hi) hg

private theorem safe_range {β : Type} (r : Std.Legacy.Range) (b : β)
    (g : Nat → β → WGPrefix Receipt (ForInStep β))
    (hg : ∀ x b, StatePrefixPreserves (fun h _ _ => Valid h) Valid (g x b)) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (forIn r b g) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact safe_list _ b g hg

theorem valid_preserves (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → WG.M Unit) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (observed pid budget toStack) := by
  unfold observed sourceWith
  repeat' first
    | with_reducible exact Confirmation.valid_preserves _ _ _
    | with_reducible exact silent _
    | with_reducible exact pure_safe _
    | with_reducible apply StatePrefixEnsures.bind
    | with_reducible apply safe_if
    | with_reducible apply safe_range
    | with_reducible apply safe_list
    | (session_origin_intro_forall; try dsimp only)
    | split

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Poll
