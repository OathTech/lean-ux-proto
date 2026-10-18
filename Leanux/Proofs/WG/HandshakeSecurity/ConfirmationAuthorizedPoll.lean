import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationAuthorizationClaims
import Leanux.Proofs.WG.Keypairs.SessionOrigin

namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Authorization.Poll
open Leanux Leanux.WG Leanux.Proofs.Logged

def observed (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → WG.M Unit) :
    WGPrefix Receipt Nat :=
  Confirmation.Poll.withEligibility liftWGPrefix eligibleObserved
    (fun gro bytes => liftWGPrefix (napiGroReceive toStack gro bytes))
    (fun gro => liftWGPrefix (napiGroFlushAll toStack gro)) pid budget

private theorem lifted {α : Type} (action : WG.M α) :
    ErasesStatePrefix (liftWGPrefix action : WGPrefix Receipt α) action :=
  erasesStatePrefix_lift action

private theorem erases_if {α : Type} (c : Prop) [Decidable c]
    (x y : WGPrefix Receipt α) (a b : WG.M α)
    (hx : ErasesStatePrefix x a) (hy : ErasesStatePrefix y b) :
    ErasesStatePrefix (if c then x else y) (if c then a else b) := by
  split <;> assumption

private theorem erases_range {β : Type} (r : Std.Legacy.Range) (b : β)
    (g : Nat → β → WGPrefix Receipt (ForInStep β))
    (a : Nat → β → WG.M (ForInStep β))
    (hg : ∀ x b, ErasesStatePrefix (g x b) (a x b)) :
    ErasesStatePrefix (forIn r b g) (forIn r b a) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact erasesStatePrefix_forIn _ b g a hg

theorem erases (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → WG.M Unit) :
    ErasesStatePrefix (observed pid budget toStack) (rxPoll pid budget toStack) := by
  rw [Confirmation.Poll.eligibility_factor]
  unfold observed Confirmation.Poll.withEligibility
  repeat' first
    | with_reducible exact eligible_erases _ _
    | with_reducible exact lifted _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | with_reducible apply erases_if
    | with_reducible apply erases_range
    | with_reducible apply erasesStatePrefix_forIn
    | (session_origin_intro_forall; try dsimp only)
    | split

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
  unfold observed Confirmation.Poll.withEligibility
  repeat' first
    | with_reducible exact eligible_valid _ _
    | with_reducible exact silent _
    | with_reducible exact pure_safe _
    | with_reducible apply StatePrefixEnsures.bind
    | with_reducible apply safe_if
    | with_reducible apply safe_range
    | with_reducible apply safe_list
    | (session_origin_intro_forall; try dsimp only)
    | split

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Authorization.Poll
