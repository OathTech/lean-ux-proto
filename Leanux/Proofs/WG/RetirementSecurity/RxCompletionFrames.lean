import Leanux.Proofs.WG.RetirementSecurity.TxStagingFunding

/-! Native receive-completion bookkeeping retains the concrete key-holder
projection. Confirmation and staged transmission are deliberately separate:
they transfer references and cannot be justified by a bookkeeping frame. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem endpoint_ownership (pid : PeerId) (endpoint : Endpoint) :
    SameView ownershipPointView (setPeerEndpoint pid endpoint) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold setPeerEndpoint dstCacheReset requireNotPending
  simp (config := {zeta := false}) only [branch,getAmbient,hiddenJiffies]
  repeat' first
    | (rx_retention_head endpointEq; exact (ownershipPoints_kernel _ (endpointEq_sameStore _ _)).wp (· = initial))
    | ownership_source_step initial

theorem handshakeComplete_ownership (pid : PeerId) (site : HiddenSite) :
    SameView ownershipPointView (timersHandshakeComplete pid site) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold timersHandshakeComplete
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head delTimer; exact (delTimer_ownership _ _).wp (· = initial))
    | ownership_source_step initial

theorem dataReceived_ownership (pid : PeerId) :
    SameView ownershipPointView (timersDataReceived pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head modPeerTimer; exact (modPeerTimer_ownership _ _ _ _).wp (· = initial))
    | ownership_source_step initial
  all_goals exact ((modPeerTimer_ownership _ _ _ _).map (fun _ => ())).wp (· = initial)

theorem freshRx_ownership (pid : PeerId) :
    SameView ownershipPointView (keepKeyFreshRx pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head branchExpired
       exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => ownershipPointView w = initial))
    | (rx_retention_head sendQueuedHandshakeInitiation
       exact (sendQueued_ownership _ _).wp (· = initial))
    | ownership_source_step initial

theorem stats_ownership (pid : PeerId) (bytes : Nat) :
    SameView ownershipPointView (updateRxStats pid bytes) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold updateRxStats
  repeat' ownership_source_step initial

theorem dishonest_ownership (why : Dishonest) :
    SameView ownershipPointView (dishonest why) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold dishonest
  cases why <;> repeat' ownership_source_step initial

theorem prepareRest_ownership (pid : PeerId) (pkt : RxPacket) :
    SameView ownershipPointView (prepareRest pid pkt) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold prepareRest timersAnyAuthenticatedPacketReceived WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head keepKeyFreshRx; exact (freshRx_ownership _).wp (· = initial))
    | (rx_retention_head delTimer; exact (delTimer_ownership _ _).wp (· = initial))
    | (rx_retention_head timersTraversal; exact (timersTraversal_ownership _).wp (· = initial))
    | (rx_retention_head timersDataReceived; exact (dataReceived_ownership _).wp (· = initial))
    | (rx_retention_head updateRxStats; exact (stats_ownership _ _).wp (· = initial))
    | (rx_retention_head dishonest; exact (dishonest_ownership _).wp (· = initial))
    | (rx_retention_head inetEcnDecapsulate
       exact (ownershipPoints_kernel _ (inetEcnDecapsulate_sameWGStore _ _ _)).wp (· = initial))
    | ownership_source_step initial

private def borrowOwnership (s : WGStoreView × (PeerId → Option Peer)) :=
  ((fun id : KeypairId => (s.1.dev.bind fun d => d.keypairs[id]?).map fun k => (k.internalId,k.refcount)),
   s.1.dev.isSome,(fun pid => (s.2 pid).map peerOwnership),
   (fun id : SkbId => (s.1.dev.bind fun d => d.txSkbs[id]?).map (·.keypair)),
   (fun id : SkbId => (s.1.dev.bind fun d => d.rxSkbs[id]?).map (·.keypair)))

private theorem borrow_ownership_factor (w : WGWorld) :
    borrowOwnership (PeerBorrow.view w) = ownershipPointView w := by
  unfold borrowOwnership PeerBorrow.view PeerBorrow.outsidePeers PeerBorrow.resident
    ownershipPointView keyReferenceView
  simp only [wgStoreView,keyAt,ownershipAt,peerAt,packetKeyWords,
    Option.bind_map,Function.comp_def,Option.isSome_map]

theorem lookupRepay_ownership (protocol : Nat) (bytes : List UInt8) :
    SameView ownershipPointView (RxBorrow.source protocol bytes) :=
  (RxBorrow.source_frame protocol bytes).of_factor borrowOwnership ownershipPointView
    (fun w => (borrow_ownership_factor w).symm)

theorem finishRx_ownership (pid : PeerId) (ready : Packets.RxReady) :
    SameView ownershipPointView (Packets.rxFinish pid ready) := by
  rw [← rxFinishSource_eq]
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold rxFinishSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head RxBorrow.source; exact (lookupRepay_ownership _ _).wp (· = initial))
    | (rx_retention_head updateRxStats; exact (stats_ownership _ _).wp (· = initial))
    | (rx_retention_head dishonest; exact (dishonest_ownership _).wp (· = initial))
    | ownership_source_step initial

end Leanux.Proofs.WG.RetirementSecurity
