import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedDisposalFrames

/-! The actual observed disposal preserves both live and positional selections. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem peer_release (peer : Option PeerId) : StateSafe (CausalJournal.peerRelease peer) :=
  state_combine _ (Delayed.peer_release peer) (Selections.disposal_history _)

theorem staged_purge (pid : PeerId) : StateSafe (CausalJournal.stagedPurge pid) :=
  state_combine _ (Delayed.staged_purge pid) (Selections.disposal_history _)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
