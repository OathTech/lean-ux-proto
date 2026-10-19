import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReleaseSource

/-! Native frames at the original release observer's post-receipt suffix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.OriginalRelease
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation HandshakeSecurity.StagedDisposal

theorem store {action : WG.M α} (same : SameWGStore action) : SameView StagedEntry.view action :=
  same.of_factor (fun s => StagedEntry.view {dev := s.dev}) StagedEntry.view (fun _ => rfl)

theorem finish (pid : PeerId) (peer : Peer) :
    Preserves (Inv history ledger debts locals) (releaseFinish pid peer) :=
  StagedEntry.native (store (PeerRelease.finish_store pid peer))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.OriginalRelease
