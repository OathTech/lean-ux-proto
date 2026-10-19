import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteFacts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReleaseSource

/-! The nested release's access prefix is independently terminal-quiet.
This is stronger than birth-quietness and applies to stopped prefixes too. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete.Source
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open AllocatedObligation HandshakeSecurity.StagedDisposal

theorem peer_access_quiet (event : Peers.PeerEvent) :
    Quiet (TxSource.peerEncode CausalJournal.txEvent event) := by
  intro position
  rfl

theorem cut_terminal_quiet (peer : Option PeerId) (w : WGWorld) (ambient : Ambient)
    (history : List CausalJournal.Event) :
    ∃ suffix, (runWGPrefix (PeerRelease.cut peer) w ambient history).2 = history ++ suffix ∧
      ∀ event ∈ suffix, Quiet event := by
  obtain ⟨events,same⟩ := PeerRelease.cut_history peer w ambient history
  refine ⟨_,same,?_⟩
  intro event member
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
  exact peer_access_quiet original

theorem cut_complete (peer : Option PeerId) (w : WGWorld) (ambient : Ambient)
    (before : Complete history ledger) :
    Complete (runWGPrefix (PeerRelease.cut peer) w ambient history).2 ledger := by
  obtain ⟨suffix,same,quiet⟩ := cut_terminal_quiet peer w ambient history
  rw [same]
  exact before.append_quiet quiet

/-- This extends only the history of the actual call's entry witness; it
makes no claim that a stopped call returned a native world. -/
theorem cut_entry_history (peer : Option PeerId) (ambient : Ambient)
    (before : StagedEntry.Inv history ledger debts locals w) :
    StagedEntry.Inv (runWGPrefix (PeerRelease.cut peer) w ambient history).2 ledger debts locals w := by
  obtain ⟨suffix,same,quiet⟩ := PeerRelease.cut_birth_quiet peer w ambient history
  rw [same]
  exact before.views suffix quiet rfl rfl rfl rfl rfl rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete.Source
