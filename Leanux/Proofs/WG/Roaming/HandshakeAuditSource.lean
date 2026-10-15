import Leanux.Proofs.WG.Roaming.HandshakeAuditModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux

/-- Inspect the prefix once, then its suffix at that actual concrete successor.
The inspection returns the prefix outcome even when the suffix fails. It
leaves the original entry untouched; it never reconstructs state from a view. -/
def handshakeAudit {α β : Type} (before : M α) (suffix : α → M β) :
    M (Campaign2.Outcome α × Campaign2.Outcome β) := fun w =>
  match before.run w with
  | .error err => .ok ((.error err, .error err), w)
  | .ok (candidate, atCut) =>
      .ok ((.ok (candidate, Campaign2.snapshot atCut),
        Campaign2.observeResult ((suffix candidate).run atCut)), w)

/-- Erasure of inspection data, not operational execution of the caller. -/
theorem handshakeAudit_complete {α β : Type} (before : M α) (suffix : α → M β) :
    (do let audited ← handshakeAudit before suffix; pure audited.2) =
      Campaign2.inspect (before >>= suffix) := by
  funext w
  change ((handshakeAudit before suffix) w >>= fun out =>
    Except.ok (out.1.2, out.2)) =
      Except.ok (Campaign2.observeResult ((before >>= suffix).run w), w)
  dsimp only [handshakeAudit]
  simp only [StateT.run_bind]
  cases hp : before.run w with
  | error err => rfl
  | ok pair => rcases pair with ⟨candidate, atCut⟩; rfl

/-- Prefix completeness rules out replacing the certificate with a constant. -/
theorem handshakeAudit_prefix {α β : Type} (before : M α) (suffix : α → M β) :
    (do let audited ← handshakeAudit before suffix; pure audited.1) =
      Campaign2.inspect before := by
  funext w
  change ((handshakeAudit before suffix) w >>= fun out =>
    Except.ok (out.1.1, out.2)) =
      Except.ok (Campaign2.observeResult (before.run w), w)
  dsimp only [handshakeAudit]
  cases hp : before.run w with
  | error err => rfl
  | ok pair => rcases pair with ⟨candidate, atCut⟩; rfl

/-- Total inspection, unchanged entry and all prefix outcomes; success of the
original computation is not required or asserted. -/
theorem handshakeAudit_observes {C : Type} (before : M (Option C))
    (suffix : Option C → M Unit) (facts : C → Campaign2.Snapshot → Prop)
    (nonePure : suffix none = pure ())
    (prefixFacts : Campaign2.Ensures before (fun _ => True)
      (fun candidate atCut => ∀ cut, candidate = some cut → facts cut atCut)) :
    Campaign2.Observes (handshakeAudit before suffix) (fun _ => True)
      (fun entry observed => ∃ audited, observed = .ok (audited, entry) ∧
        HandshakeAuditFacts facts audited) := by
  intro w pre
  cases hp : before.run w with
  | error err =>
    refine ⟨(.error err, .error err), ?_, rfl⟩
    change Campaign2.observeResult ((handshakeAudit before suffix) w) = _
    dsimp only [handshakeAudit]
    rw [hp]
    rfl
  | ok pair =>
    rcases pair with ⟨candidate, atCut⟩
    refine ⟨(.ok (candidate, Campaign2.snapshot atCut),
      Campaign2.observeResult ((suffix candidate).run atCut)), ?_, ?_⟩
    · change Campaign2.observeResult ((handshakeAudit before suffix) w) = _
      dsimp only [handshakeAudit]
      rw [hp]
      rfl
    · cases candidate with
      | none =>
        change Campaign2.observeResult ((suffix none).run atCut) = _
        rw [nonePure]
        rfl
      | some cut => exact prefixFacts w (some cut) atCut trivial hp cut rfl

end Leanux.Proofs.WG.Roaming
