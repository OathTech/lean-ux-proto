import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteOriginalRelease
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteNestedRelease

/-! Exact history extension for original release. Native finish failure keeps
the already-appended receipt; the equation does not require normal return. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open CausalJournal HandshakeSecurity.StagedDisposal

theorem original_appends (peer : Option PeerId) : StateAppends (CausalJournal.peerRelease peer) := by
  intro w ambient history
  change ∃ suffix, (runWGPrefix (CausalJournal.peerRelease peer) w ambient history).2 = history ++ suffix
  have equation := StagedAdmission.Front.put_run peer w ambient history
  change runWGPrefix (CausalJournal.peerRelease peer) w ambient history = _ at equation
  rw [equation]
  cases native : ((releaseCut peer).run w).run ambient with
  | error stop => exact ⟨[],by simp⟩
  | ok out =>
    obtain ⟨⟨value,g⟩,clock⟩ := out
    cases value with
    | none => exact ⟨[_],rfl⟩
    | some pair => exact ⟨[_],rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSource
