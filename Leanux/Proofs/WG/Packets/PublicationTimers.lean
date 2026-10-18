import Leanux.Proofs.WG.Packets.PublicationClear
import Leanux.Proofs.WG.Packets.PublicationHandshakeSend
import Leanux.Proofs.WG.Origins.OwnerTimers

/-! All five actual native timer callbacks retain packet publication anchors
and their epoch-scoped peer frontier. Saved peer identities and nullable
payments are carried through the original callbacks and failed records. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues PublicationCompletion
open OwnerCompletion (geometry)

private theorem keepalive_geometry (pid : PeerId) : SameView geometry (sendKeepalive pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold sendKeepalive
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head sendStagedPackets
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.staged_geometry) _).wp (fun s => s = initial))
    | completion_step initial

private theorem keepalive_peers (pid : PeerId) (initial : Option (PeerId → Option (Nat × Key))) :
    Preserves (PeersRetained initial) (sendKeepalive pid) := by
  unfold sendKeepalive
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head sendStagedPackets; exact sendStagedPackets_peers _ initial)
    | publication_peer_step initial

theorem sendKeepalive_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (sendKeepalive pid) :=
  preserves_of_geometry _ (keepalive_geometry pid) (keepalive_peers pid) history

private theorem purge_geometry (pid : PeerId) : SameView geometry (purgeStagedPackets pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold purgeStagedPackets
  repeat' completion_step initial

theorem purgeStagedPackets_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (purgeStagedPackets pid) :=
  preserves_of_configured _ ((purge_geometry pid).factor Prod.snd)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDevice.«0».Leanux.Proofs.WG.CurrentLifecycle.purgeStaged_view) pid) history

private theorem clearEndpoint_geometry (pid : PeerId) : SameView geometry (clearPeerEndpointSrc pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold clearPeerEndpointSrc dstCacheResetNow
  repeat' first
    | (rx_retention_head dstCacheReset
       exact (PublicationGeometry.dstCacheReset_geometry _).wp (fun s => s = initial))
    | completion_step initial

theorem clearPeerEndpointSrc_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (clearPeerEndpointSrc pid) :=
  preserves_of_configured _ ((clearEndpoint_geometry pid).factor Prod.snd)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.clearEndpoint_view) pid) history

theorem modPeerTimer_preserves (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (history : List RxHistory.Event) :
    Preserves (Inv history) (modPeerTimer site pid timer delay) :=
  preserves_of_configured _
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.mod_geometry) site pid timer delay).factor Prod.snd)
    (ConfiguredIdentity.modPeerTimer_view site pid timer delay) history

private theorem queued_peers (pid : PeerId) (retry : Bool)
    (initial : Option (PeerId → Option (Nat × Key))) :
    Preserves (PeersRetained initial) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' publication_peer_step initial

theorem sendQueuedHandshakeInitiation_preserves (pid : PeerId) (retry : Bool)
    (history : List RxHistory.Event) :
    Preserves (Inv history) (sendQueuedHandshakeInitiation pid retry) :=
  preserves_of_geometry _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.sendQueued_geometry) pid retry)
    (queued_peers pid retry) history

private theorem timerCallback_geometry (pid : PeerId) (timer : PeerTimer) :
    SameView geometry (timerCallback pid timer) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
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
    | (rx_retention_head clearPeerEndpointSrc; exact (clearEndpoint_geometry _).wp (fun s => s = initial))
    | (rx_retention_head purgeStagedPackets; exact (purge_geometry _).wp (fun s => s = initial))
    | (rx_retention_head delTimer
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.del_geometry) _ _).wp (fun s => s = initial))
    | (rx_retention_head modPeerTimer
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.mod_geometry) _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head sendQueuedHandshakeInitiation
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.sendQueued_geometry) _ _).wp (fun s => s = initial))
    | (rx_retention_head sendKeepalive; exact (keepalive_geometry _).wp (fun s => s = initial))
    | completion_traffic initial

private theorem timerCallback_peers (pid : PeerId) (timer : PeerTimer)
    (initial : Option (PeerId → Option (Nat × Key))) :
    Preserves (PeersRetained initial) (timerCallback pid timer) := by
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
    | (rx_retention_head clearPeerEndpointSrc
       exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured)
         ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDeferred.«0».Leanux.Proofs.WG.CurrentDeferred.clearEndpoint_view) _) initial)
    | (rx_retention_head purgeStagedPackets
       exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured)
         ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDevice.«0».Leanux.Proofs.WG.CurrentLifecycle.purgeStaged_view) _) initial)
    | (rx_retention_head delTimer
       exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured)
         (ConfiguredIdentity.delTimer_view _ _) initial)
    | (rx_retention_head modPeerTimer
       exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured)
         (ConfiguredIdentity.modPeerTimer_view _ _ _ _) initial)
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued_peers _ _ initial)
    | (rx_retention_head sendKeepalive; exact keepalive_peers _ initial)
    | publication_peer_step initial

/-- The five original cases retain their guards and nullable reference payments;
no timer validity, queued-work, liveness or drain-success assumption is added. -/
theorem timerCallback_preserves (pid : PeerId) (timer : PeerTimer)
    (history : List RxHistory.Event) : Preserves (Inv history) (timerCallback pid timer) :=
  preserves_of_geometry _ (timerCallback_geometry pid timer) (timerCallback_peers pid timer) history

theorem timerCallback_checked (pid : PeerId) (timer : PeerTimer) :
    PrefixPreserves (fun h w => OwnerChecks.Inv h w ∧ Inv h w.wg) OwnerChecks.Safe
      (RxHistory.mixed (liftWGObserver (timerCallbackPrefix pid timer))) :=
  observed_native _ _ (RxHistory.mixed_erases (liftWGObserver_erases (timerCallbackPrefix_erases pid timer)))
    (OwnerTimers.timerCallback_checked pid timer) (timerCallback_preserves pid timer)

end Leanux.Proofs.WG.PublicationFrontier
