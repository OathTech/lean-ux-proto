import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationErasure
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryAllocatedFrames

/-! Native allocation contracts for the concrete removal and staging calls
used by identity configuration. Their observation equations are exact on Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConfigurationNative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal StackOwnership

theorem staging_erases (pid : PeerId) :
    ErasesStatePrefix (Driver.stagingObserved hooks pid) (sendStagedPackets pid) := by
  apply NestedPeerRelease.projects_erases old? (Driver.staging_projects hooks_projects pid)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.staging_projects Journal.hooks_projects pid)
  rw [Driver.nonce_staging_specialization]
  exact Nonce.stagingObserved_erases pid

theorem remove_erases (peer : Option PeerId) :
    ErasesStatePrefix (Driver.removeObserved hooks peer) (peerRemove peer) := by
  apply NestedPeerRelease.projects_erases old? (Driver.remove_projects hooks_projects peer)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.remove_projects Journal.hooks_projects peer)
  rw [Driver.remove_lift Driver.nonceHooks rfl rfl]
  exact erasesStatePrefix_lift _

theorem remove_all_erases : ErasesStatePrefix (Driver.removeAllObserved hooks) peerRemoveAll := by
  apply NestedPeerRelease.projects_erases old? (Driver.removeAll_projects hooks_projects)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.removeAll_projects Journal.hooks_projects)
  rw [Driver.removeAll_lift Driver.nonceHooks rfl rfl]
  exact erasesStatePrefix_lift _

theorem staging (pid : PeerId) : Preserves Allocated (sendStagedPackets pid) :=
  AllocatedFrames.observed (TxStagingCall.erases (.send pid)) (TxStagingCall.allocation (.send pid))

theorem removal (peer : Option PeerId) : Preserves Allocated (peerRemove peer) :=
  AllocatedFrames.observed (PeerRemovalCall.erases (.remove peer)) (PeerRemovalCall.allocation (.remove peer))

theorem removal_all : Preserves Allocated peerRemoveAll :=
  AllocatedFrames.observed (PeerRemovalCall.erases .removeAll) (PeerRemovalCall.allocation .removeAll)

theorem expire (pid : PeerId) : Preserves Allocated (expireCurrentPeerKeypairs pid) :=
  AllocatedFrames.observed (expireCurrentPeerKeypairsPrefix_erases pid)
    (expireCurrentPeerKeypairsPrefix_preserves allocationAmbient allocationConfigurationDevice.index pid)

theorem clear_endpoint (pid : PeerId) : Preserves Allocated (clearPeerEndpointSrc pid) :=
  AllocatedFrames.observed (clearPeerEndpointSrcPrefix_erases pid)
    (AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec allocationAmbient (fun _ => True) pid))

theorem open_erases : ErasesStatePrefix (Driver.openObserved hooks) wgOpen := by
  apply NestedPeerRelease.projects_erases old? (Driver.open_projects hooks_projects)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.open_projects Journal.hooks_projects)
  rw [Driver.nonce_openObserved_eq]
  exact Nonce.openObserved_erases

theorem up_erases : ErasesStatePrefix (Driver.upObserved hooks) wgUp := by
  apply NestedPeerRelease.projects_erases old? (Driver.up_projects hooks_projects)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.up_projects Journal.hooks_projects)
  rw [Driver.nonce_upObserved_eq]
  exact Nonce.upObserved_erases

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConfigurationNative
