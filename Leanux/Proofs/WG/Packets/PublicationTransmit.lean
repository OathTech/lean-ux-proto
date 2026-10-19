import Leanux.Proofs.WG.Packets.PublicationEncrypt
import Leanux.Proofs.WG.Packets.PublicationHandshakeSend
import Leanux.Proofs.WG.Origins.OwnerTransmit

/-! Actual TX completion and payment retain the surviving published RX
identities. Final peer deletion is permitted; worker callbacks stay product-scoped. -/
namespace Leanux.Proofs.WG.PublicationJoint
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues PublicationCompletion PublicationGeometry
open OwnerCompletion (geometry)

private theorem dataSent_geometry (pid : PeerId) : SameView geometry (timersDataSent pid) := by
  intro initial
  change Framing.Preserves (fun w => geometry w = initial) _
  unfold timersDataSent modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (fun w => geometry w = initial))
    | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => geometry w = initial))
    | (rx_retention_head armTimer
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.arm_geometry) _ _ _ _).wp (fun s => s = initial))
    | publication_geometry_step initial

private theorem fresh_geometry (pid : PeerId) : SameView geometry (keepKeyFresh pid) := by
  intro initial
  change Framing.Preserves (fun w => geometry w = initial) _
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.sendQueued_geometry) _ _).wp (fun s => s = initial))
    | publication_geometry_crypto initial
    | publication_geometry_step initial

private theorem sendSkb_geometry (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView geometry (sendSkbToPeer pid bytes ds) := by
  intro initial
  change Framing.Preserves (fun w => geometry w = initial) _
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4; exact (send4_geometry _ _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head send6; exact (send6_geometry _ _ _ _ _).wp (fun s => s = initial))
    | publication_geometry_step initial

private theorem complete_geometry (pid : PeerId) (item : List SkbId) :
    SameView geometry (createDataDone pid item) := by
  intro initial
  let P := fun w => geometry w = initial
  have read (id : SkbId) : Framing.Preserves P (getTxSkb id) := by completion_skb initial
  have traversal : Framing.Preserves P (timersTraversal pid) := (timersTraversal_geometry _).wp (fun s => s = initial)
  have authenticated : Framing.Preserves P (timersAnyAuthenticatedPacketSent pid) :=
    (timersAnyAuthenticatedPacketSent_geometry _).wp (fun s => s = initial)
  have send (bytes : List UInt8) (ds : Nat) : Framing.Preserves P (sendSkbToPeer pid bytes ds) :=
    (sendSkb_geometry _ _ _).wp (fun s => s = initial)
  have dataSent : Framing.Preserves P (timersDataSent pid) := (dataSent_geometry _).wp (fun s => s = initial)
  have fresh : Framing.Preserves P (keepKeyFresh pid) := (fresh_geometry _).wp (fun s => s = initial)
  have ambient {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  change Framing.Preserves P _
  routing_tx_source [createDataDone] using [read,traversal,authenticated,send,dataSent,fresh,ambient]

private theorem fresh_peers (pid : PeerId) (initial) :
    Framing.Preserves (PeersRetained initial) (keepKeyFresh pid) := by
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation
       exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.sendQueued_peers) _ _ initial)
    | publication_peer_step initial

private theorem complete_peers (pid : PeerId) (item : List SkbId) (initial) :
    Framing.Preserves (PeersRetained initial) (createDataDone pid item) := by
  let P := PeersRetained initial
  have configured {α : Type} {a : WG.M α} (h : SameView ConfiguredIdentity.view a) : Framing.Preserves P a :=
    (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured) h initial
  have read (id : SkbId) : Framing.Preserves P (getTxSkb id) := by
    change Framing.Preserves (PeersRetained initial) _
    unfold getTxSkb
    publication_peer_skb
  have traversal : Framing.Preserves P (timersTraversal pid) := configured (ConfiguredIdentity.timersTraversal_view _)
  have authenticated : Framing.Preserves P (timersAnyAuthenticatedPacketSent pid) :=
    configured (ConfiguredIdentity.timersAnyAuthenticatedPacketSent_view _)
  have send (bytes : List UInt8) (ds : Nat) : Framing.Preserves P (sendSkbToPeer pid bytes ds) :=
    configured ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentEnvironment.«0».Leanux.Proofs.WG.CurrentEnvironment.sendSkb_view) _ _ _)
  have dataSent : Framing.Preserves P (timersDataSent pid) :=
    configured ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentEnvironment.«0».Leanux.Proofs.WG.CurrentEnvironment.dataSent_view) _)
  have fresh : Framing.Preserves P (keepKeyFresh pid) := fresh_peers _ initial
  have ambient {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  routing_tx_source [createDataDone] using [read,traversal,authenticated,send,dataSent,fresh,ambient]

theorem createDataDone_frontier (pid : PeerId) (item : List SkbId) (history : List RxHistory.Event) :
    Framing.Preserves (PublicationFrontier.Inv history) (createDataDone pid item) :=
  PublicationFrontier.preserves_of_geometry _ (complete_geometry pid item) (complete_peers pid item) history

private theorem txStep_geometry (pid : PeerId) : SameView geometry (txStep pid) := by
  intro initial
  change Framing.Preserves (fun w => geometry w = initial) _
  unfold txStep WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head createDataDone; exact (complete_geometry _ _).wp (fun s => s = initial))
    | (rx_retention_head PrevQueue.peek
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.store)
         (prevQueuePeek_sameWGStore _)).wp (fun s => s = initial))
    | completion_skb initial
    | publication_geometry_step initial

private theorem txStep_peers (pid : PeerId) (initial) :
    Framing.Preserves (PeersRetained initial) (txStep pid) := by
  unfold txStep WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head createDataDone; exact complete_peers _ _ initial)
    | (rx_retention_head PrevQueue.peek
       exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured)
         (ConfiguredIdentity.sameWG (project := id) (prevQueuePeek_sameWGStore _)) initial)
    | publication_peer_skb
    | publication_peer_step initial

theorem txStep_frontier (pid : PeerId) (history : List RxHistory.Event) :
    Framing.Preserves (PublicationFrontier.Inv history) (txStep pid) :=
  PublicationFrontier.preserves_of_geometry _ (txStep_geometry pid) (txStep_peers pid) history

theorem txIter_frontier (pid : PeerId) (need : Leanux.M Bool) (history : List RxHistory.Event)
    (hn : Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) need) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) (txIter pid need) := by
  let P := fun w : World => PublicationFrontier.Inv history w.wg
  have step : Framing.Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    PublicationPoll.native_product _ _ (txStep_frontier pid history)
  have needSpec : Framing.Preserves P need := hn
  have ambient {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  routing_tx_source [txIter,workerIter] using [step,needSpec,ambient]

theorem txIteration (pid : PeerId) :
    Preserves (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  mixed _ _ (OwnerTransmit.txIteration pid) (txIterPrefix_erases pid (erasesPrefix_lift _))
    (fun history => txIter_frontier pid _ history
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationFrontierPoll.«0».Leanux.Proofs.WG.PublicationFrontier.product_store)
        _ (condResched_sameKernel _) history))

end Leanux.Proofs.WG.PublicationJoint
