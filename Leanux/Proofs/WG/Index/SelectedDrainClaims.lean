import Leanux.Proofs.WG.Index.SelectedDrainSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing

/-- The original work drain preserves a projected state predicate when each
actual selected callback preserves it. Membership is derived from the same
queue read/selection; no promise of successful draining is made. -/
theorem drainHandshakeSendWq_selected (P : Campaign2.State → Prop)
    (send : ∀ pid, Campaign2.Ensures (runFlushedSendWork pid)
      (fun s => P s.wg ∧ ∃ d, s.wg.device = some d ∧ pid ∈ d.sendWorkQueue)
      (fun _ s => P s.wg))
    (clear : ∀ pid, Campaign2.Ensures (runFlushedClearWork pid)
      (fun s => P s.wg ∧ ∃ d, s.wg.device = some d ∧ pid ∈ d.clearWorkQueue)
      (fun _ s => P s.wg))
    (upTo : Option PeerId) :
    Campaign2.Ensures (drainHandshakeSendWq upTo) (fun s => P s.wg)
      (fun _ s => P s.wg) := by
  intro g ambient result out after pre run
  have source := SelectedDrain.original_preserves
    (fun w => P (Campaign2.snapshot w ambient).wg)
    (by
      intro w v d pid a b invariant device member actual
      exact send pid w a () v b ⟨invariant,d,device,member⟩ actual)
    (by
      intro w v d pid a b invariant device member actual
      exact clear pid w a () v b ⟨invariant,d,device,member⟩ actual) upTo
  exact (hoare_iff_run_ambient _ _ _).mp source
    g ambient result out after pre run

end Leanux.Proofs.WG.Index
