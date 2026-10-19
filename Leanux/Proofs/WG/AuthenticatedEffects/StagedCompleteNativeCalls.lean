import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationNative
import Leanux.Proofs.WG.Lifetimes.DeviceXmit
import Leanux.Proofs.WG.Lifetimes.ReceiveWorker

/-! Exact native counterparts and allocation frames for paired source calls.
Erasure transports allocation state only; it supplies no packet-history fact. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteNative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal StackOwnership

theorem keepalive_erases (pid : PeerId) :
    ErasesStatePrefix (Driver.keepaliveObserved hooks pid) (sendKeepalive pid) := by
  apply NestedPeerRelease.projects_erases old? (Driver.keepalive_projects hooks_projects pid)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.keepalive_projects Journal.hooks_projects pid)
  rw [Driver.nonce_keepaliveObserved_eq]
  exact Nonce.keepaliveObserved_erases pid

theorem transmit_erases (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ErasesStatePrefix (Driver.transmitObserved hooks family addr packets mtu) (wgXmit family addr packets mtu) := by
  apply NestedPeerRelease.projects_erases old? (Driver.transmit_projects hooks_projects family addr packets mtu)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.transmit_projects Journal.hooks_projects family addr packets mtu)
  rw [Driver.nonce_transmitObserved_eq]
  exact Nonce.transmitObserved_erases family addr packets mtu

theorem handshake_erases : ErasesStatePrefix (Driver.handshakeObserved hooks) receiveStep := by
  apply NestedPeerRelease.projects_erases old? (Driver.handshake_projects hooks_projects)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.handshake_projects Journal.hooks_projects)
  rw [Driver.nonce_handshakeObserved_eq]
  exact Nonce.Handshake.erases

theorem release_erases (peer : Option PeerId) : ErasesStatePrefix (hooks.peerRelease peer) (peerPut peer) := by
  apply NestedPeerRelease.projects_erases old? (hooks_projects.peerRelease peer)
  exact NestedPeerRelease.projects_erases Journal.nonce? (Journal.hooks_projects.peerRelease peer)
    (erasesStatePrefix_lift _)

theorem down_erases : ErasesStatePrefix (Driver.downObserved hooks) wgDown := by
  apply NestedPeerRelease.projects_erases old? (Driver.down_projects hooks_projects)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.down_projects Journal.hooks_projects)
  rw [Driver.down_lift Driver.nonceHooks rfl rfl rfl]
  exact erasesStatePrefix_lift _

theorem keepalive (pid : PeerId) : Preserves Allocated (sendKeepalive pid) :=
  AllocatedFrames.observed (TxStagingCall.erases (.keepalive pid)) (TxStagingCall.allocation (.keepalive pid))

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Preserves Allocated (wgXmit family addr packets mtu) :=
  AllocatedFrames.observed (wgXmitPrefix_erases family addr packets mtu)
    (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit family addr packets mtu)

theorem handshake : Preserves Allocated receiveStep :=
  AllocatedFrames.observed (HandshakeReceiveCall.erases .step) (HandshakeReceiveCall.allocation .step)

theorem down : Preserves Allocated wgDown :=
  AllocatedFrames.observed (DeviceControlCall.erases .down) (DeviceControlCall.allocation .down)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteNative
