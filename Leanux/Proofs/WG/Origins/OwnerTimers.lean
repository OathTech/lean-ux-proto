import Leanux.Proofs.WG.Origins.OwnerTransmit
import Leanux.Proofs.WG.Origins.JointOwnerDevice

/-! Actual timer callbacks retain receiving-owner bounds. Queue refusal keeps
its original duplicate-reference payment and no callback totality is assumed. -/
namespace Leanux.Proofs.WG.OwnerTimers
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues OwnerBounds OwnerControls OwnerLifecycle

theorem timerCallback_preserves (pid : PeerId) (timer : PeerTimer) :
    Preserves Carrier (timerCallback pid timer) := by
  cases timer <;> simp only [timerCallback]
  all_goals first
    | unfold expiredRetransmitHandshake
    | unfold expiredSendKeepalive
    | unfold expiredNewHandshake
    | unfold expiredZeroKeyMaterial
    | unfold expiredSendPersistentKeepalive
  all_goals try simp (config := {zeta := false}) only
    [branch,branchCmp,peekQueuedUnit,recordQueued,discard,map_const,Function.comp_def,map_eq_pure_bind]
  all_goals repeat' first
    | (allocation_release_head clearPeerEndpointSrc
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.JointOwnerDevice.«0».Leanux.Proofs.WG.JointOwnerDevice.clearEndpoint_owner) _)
    | (allocation_release_head purgeStagedPackets
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerDevice.«0».Leanux.Proofs.WG.OwnerDevice.purgeStaged_preserves) _)
    | (allocation_release_head delTimer; exact delTimer_preserves _ _)
    | (allocation_release_head modPeerTimer; exact modPeerTimer_preserves _ _ _ _)
    | (allocation_release_head sendQueuedHandshakeInitiation
       exact OwnerTransmit.sendQueuedHandshakeInitiation_preserves _ _)
    | (allocation_release_head sendKeepalive; exact OwnerPeerConfiguration.sendKeepalive_preserves _)
    | (allocation_release_head peerGet
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.JointOwnerConfiguration.«0».Leanux.Proofs.WG.JointOwnerConfiguration.peerGet_owner) _)
    | owner_control_step

theorem timerCallback_checked (pid : PeerId) (timer : PeerTimer) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver (timerCallbackPrefix pid timer))) := by
  apply OwnerChecks.native_mixed _ _ (timerCallbackPrefix_erases pid timer)
    (TimerCallbackCall.allocation (.dispatch pid timer)) (Origins.Retaining.timerCallback_material pid timer)
    (CurrentDeferred.timerCallback_preserves pid timer)
  intro history
  exact hoare_consequence (timerCallback_preserves pid timer)
    (fun _ hi => hi.2) (fun _ _ hi => hi)

end Leanux.Proofs.WG.OwnerTimers
