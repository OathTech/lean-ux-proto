import Leanux.Proofs.WG.Roaming.HandshakeOverlayInspectionBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem inspect_facts {α : Type} (observed : PrefixM RxEvent α)
    (checked : PrefixPreserves (fun h _ => RxValid h) RxValid observed) :
    Campaign2.Product.Observes (inspect observed) (fun _ => True)
      (fun entry result => ∃ audit, result = .ok (audit,entry) ∧
        ∀ attempt ∈ audit.attempts, Authenticated attempt) := by
  intro w _
  refine ⟨⟨Campaign2.Product.observeResult (runPrefix observed w []).1,
    (runPrefix observed w []).2.filterMap rxAttempt⟩,rfl,?_⟩
  exact (checked w [] (by intro r member; cases member)).choose_spec.2.1

theorem inspect_original {α : Type} (observed : PrefixM RxEvent α)
    (original : Leanux.M α) (erases : ErasesPrefix observed original) :
    (do let audit ← inspect observed; pure audit.outcome) =
      Campaign2.Product.inspect original := by
  funext w
  change (Except.ok (Campaign2.Product.observeResult (runPrefix observed w []).1,w) :
    Except Stop (Campaign2.Product.Outcome α × World)) =
    .ok (Campaign2.Product.observeResult (original.run w),w)
  rw [erases w []]

end Leanux.Proofs.WG.Roaming.HandshakeOverlay
