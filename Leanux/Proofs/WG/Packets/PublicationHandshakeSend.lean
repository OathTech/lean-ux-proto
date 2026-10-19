import Leanux.Proofs.WG.Packets.PublicationSession
import Leanux.Proofs.WG.Origins.ConfiguredHandshake

/-! Native handshake transmission retains receive cells, epoch and allocation
frontiers. Source socket paths and timer decisions are unchanged. -/
namespace Leanux.Proofs.WG.PublicationGeometry
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues
open OwnerCompletion (geometry)

private theorem geometryStore {α : Type} {a : WG.M α} (h : SameWGStore a) :
    SameView geometry a :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.store) h

macro "publication_geometry_step " initial:term : tactic => `(tactic| first
  | (allocation_release_lift_from Net.M
     exact (geometryStore (liftRouting_sameWGStore _)).wp (fun s => s = $initial))
  | (allocation_release_head liftRouting
     exact (geometryStore (liftRouting_sameWGStore _)).wp (fun s => s = $initial))
  | (allocation_release_head getRouting
     exact (geometryStore (liftRouting_sameWGStore
       ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State)))).wp (fun s => s = $initial))
  | (allocation_release_lift_from IndexM
     apply hoare_liftIndex
     intro w d table hi hd
     simpa only [geometry,RxCredits.rxView,hd,Option.map_some,Option.bind_some] using hi)
  | completion_step $initial)

macro "publication_geometry_crypto " initial:term : tactic => `(tactic| first
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => geometry w = $initial))
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (fun w => geometry w = $initial))
  | (rx_retention_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp (fun w => geometry w = $initial))
  | (rx_retention_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp (fun w => geometry w = $initial))
  | (rx_retention_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (fun w => geometry w = $initial)))

theorem timersTraversal_geometry (pid : PeerId) : SameView geometry (timersTraversal pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.traversal_geometry) pid

theorem timersAnyAuthenticatedPacketSent_geometry (pid : PeerId) :
    SameView geometry (timersAnyAuthenticatedPacketSent pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold timersAnyAuthenticatedPacketSent
  repeat' first
    | (rx_retention_head delTimer
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.del_geometry) _ _).wp (fun s => s = initial))
    | publication_geometry_step initial

theorem timersHandshakeInitiated_geometry (pid : PeerId) :
    SameView geometry (timersHandshakeInitiated pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold timersHandshakeInitiated modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (fun w => geometry w = initial))
    | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => geometry w = initial))
    | (rx_retention_head armTimer
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.arm_geometry) _ _ _ _).wp (fun s => s = initial))
    | publication_geometry_step initial

theorem dstCacheReset_geometry (pid : PeerId) : SameView geometry (dstCacheReset pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' publication_geometry_step initial

theorem createInitiation_geometry (pid : PeerId) : SameView geometry (createInitiation pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first | publication_geometry_crypto initial | publication_geometry_step initial

theorem addMacToPacket_geometry (pid : PeerId) (msg : List UInt8) :
    SameView geometry (addMacToPacket pid msg) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first | publication_geometry_crypto initial | publication_geometry_step initial

theorem dstCacheGet_geometry (pid : PeerId) (gen : Nat) : SameView geometry (dstCacheGet pid gen) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold dstCacheGet
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' publication_geometry_step initial

theorem dstCacheSet_geometry (pid : PeerId) (src gen dev : Nat) : SameView geometry (dstCacheSet pid src gen dev) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold dstCacheSet
  repeat' publication_geometry_step initial

theorem tunnelXmit_geometry (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView geometry ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact (geometryStore (loopbackSend_kernel _ _)).wp (fun s => s = initial))
    | (rx_retention_head socketPort
       exact (geometryStore (socketPort_sameStore _)).wp (fun s => s = initial))
    | publication_geometry_step initial

private theorem send4ClearSrc_geometry cache : SameView geometry (send4ClearSrcSource cache) := by
  intro initial
  unfold send4ClearSrcSource
  change Preserves (fun w => geometry w = initial) _
  repeat' first
    | publication_geometry_step initial

private theorem send4Finish_geometry e bytes ds exactRx route : SameView geometry (send4FinishSource e bytes ds exactRx route) := by
  intro initial
  unfold send4FinishSource
  change Preserves (fun w => geometry w = initial) _
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact (tunnelXmit_geometry _ _ _ _ _).wp (fun t => t = initial))
    | publication_geometry_step initial

private theorem send4RouteDone_geometry e cache bytes ds exactRx gen fallback rt :
    SameView geometry (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  intro initial
  unfold send4RouteDoneSource
  change Preserves (fun w => geometry w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact (dstCacheSet_geometry _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_geometry _ _ _ _ _).wp (fun t => t = initial))
    | publication_geometry_step initial

private theorem send4Retry_geometry e cache bytes ds exactRx gen fallback srcIf rt :
    SameView geometry (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  intro initial
  unfold send4RetrySource
  change Preserves (fun w => geometry w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_geometry _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_geometry _).wp (fun t => t = initial))
    | (rx_retention_head send4RouteDoneSource; exact (send4RouteDone_geometry _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | publication_geometry_step initial

private theorem send4Miss_geometry e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView geometry (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  intro initial
  unfold send4MissSource
  change Preserves (fun w => geometry w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_geometry _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_geometry _).wp (fun t => t = initial))
    | (rx_retention_head send4RetrySource; exact (send4Retry_geometry _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | publication_geometry_step initial

private theorem send4AfterCache_geometry e cache bytes ds exactRx gen saddr srcIf route :
    SameView geometry (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  intro initial
  unfold send4AfterCacheSource
  change Preserves (fun w => geometry w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact (send4Miss_geometry _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_geometry _ _ _ _ _).wp (fun t => t = initial))
    | publication_geometry_step initial

theorem send4_geometry e cache bytes ds exactRx : SameView geometry (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  intro initial
  unfold send4Source
  change Preserves (fun w => geometry w = initial) _
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (dstCacheGet_geometry _ _).wp (fun t => t = initial))
    | (rx_retention_head send4AfterCacheSource; exact (send4AfterCache_geometry _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | publication_geometry_step initial

theorem send6_geometry (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView geometry (send6 e cache bytes ds exactRx) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (dstCacheGet_geometry _ _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_geometry _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheSet; exact (dstCacheSet_geometry _ _ _ _).wp (fun s => s = initial))
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact (tunnelXmit_geometry _ _ _ _ _).wp (fun s => s = initial))
    | publication_geometry_step initial

theorem sendBufferToPeer_geometry (pid : PeerId) (bytes : List UInt8) : SameView geometry (sendBufferToPeer pid bytes) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head send4; exact (send4_geometry _ _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head send6; exact (send6_geometry _ _ _ _ _).wp (fun s => s = initial))
    | publication_geometry_step initial

theorem sendHandshakeInitiation_geometry (pid : PeerId) : SameView geometry (sendHandshakeInitiation pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head createInitiation; exact (createInitiation_geometry _).wp (fun s => s = initial))
    | (rx_retention_head addMacToPacket; exact (addMacToPacket_geometry _ _).wp (fun s => s = initial))
    | (rx_retention_head timersTraversal; exact (timersTraversal_geometry _).wp (fun s => s = initial))
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact (timersAnyAuthenticatedPacketSent_geometry _).wp (fun s => s = initial))
    | (rx_retention_head timersHandshakeInitiated; exact (timersHandshakeInitiated_geometry _).wp (fun s => s = initial))
    | (rx_retention_head sendBufferToPeer; exact (sendBufferToPeer_geometry _ _).wp (fun s => s = initial))
    | publication_geometry_crypto initial
    | publication_geometry_step initial



end Leanux.Proofs.WG.PublicationGeometry

namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Queues

theorem sendHandshakeInitiation_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (sendHandshakeInitiation pid) :=
  preserves_of_configured _ ((PublicationGeometry.sendHandshakeInitiation_geometry pid).factor Prod.snd)
    (ConfiguredHandshake.sendHandshakeInitiation_view pid) history

theorem handshakeSendWorker_preserves (pid : PeerId) (history : List RxHistory.Event) :
    Preserves (Inv history) (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact preserves_bind (sendHandshakeInitiation_preserves pid history)
    (fun _ => peerPut_preserves (some pid) history)

end Leanux.Proofs.WG.PublicationFrontier
