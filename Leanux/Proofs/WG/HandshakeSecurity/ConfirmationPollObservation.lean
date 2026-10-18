import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationPollSource
import Leanux.Proofs.WG.Keypairs.SessionOrigin

namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Poll
open Leanux Leanux.WG Leanux.Proofs.Logged

def observed (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → WG.M Unit) :
    WGPrefix Receipt Nat :=
  sourceWith liftWGPrefix (fun pkt => liftWGPrefix (counterValidate pkt.keypair pkt.nonce))
    Confirmation.observed
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
  rw [source]
  unfold observed sourceWith
  repeat' first
    | with_reducible exact Confirmation.erases _ _ _
    | with_reducible exact lifted _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | with_reducible apply erases_if
    | with_reducible apply erases_range
    | with_reducible apply erasesStatePrefix_forIn
    | (session_origin_intro_forall; try dsimp only)
    | split

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Poll
