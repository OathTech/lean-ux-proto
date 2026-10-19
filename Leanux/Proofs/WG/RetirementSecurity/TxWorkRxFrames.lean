import Leanux.Proofs.WG.RetirementSecurity.TxActorStaging

/-! Receive completion retains the pending TX work queue. Key promotion and
the staged send remain separate source cuts because they transfer references
and can introduce actual packet service obligations. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem endpoint_work (pid : PeerId) (endpoint : Endpoint) : SameView queued (setPeerEndpoint pid endpoint) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold setPeerEndpoint dstCacheReset requireNotPending
  simp (config := {zeta := false}) only [branch,getAmbient,hiddenJiffies]
  repeat' first
    | (rx_retention_head endpointEq; exact (store (endpointEq_sameStore _ _)).wp (·=initial))
    | tx_work_step initial

theorem handshake_complete_work (pid : PeerId) (site : HiddenSite) :
    SameView queued (timersHandshakeComplete pid site) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold timersHandshakeComplete
  simp only [hidden]
  repeat' first
    | (rx_retention_head delTimer; exact (delTimer_work _ _).wp (·=initial))
    | tx_work_step initial

theorem data_received_work (pid : PeerId) : SameView queued (timersDataReceived pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold timersDataReceived
  simp only [branch]
  repeat' first
    | (rx_retention_head modPeerTimer; exact (modPeerTimer_work _ _ _ _).wp (·=initial))
    | tx_work_step initial
  all_goals exact ((modPeerTimer_work _ _ _ _).map (fun _=>())).wp (·=initial)

theorem fresh_rx_work (pid : PeerId) : SameView queued (keepKeyFreshRx pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold keepKeyFreshRx WG.andM
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w=>queued w=initial))
    | (rx_retention_head sendQueuedHandshakeInitiation; exact (sendQueued_work _ _).wp (·=initial))
    | tx_work_step initial

theorem stats_work (pid bytes : Nat) : SameView queued (updateRxStats pid bytes) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold updateRxStats
  repeat' tx_work_step initial

theorem dishonest_work (why : Dishonest) : SameView queued (dishonest why) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold dishonest
  cases why <;> repeat' tx_work_step initial

theorem confirmation_work (pid : PeerId) (kid : KeypairId) : SameView queued (receivedWithKeypair pid kid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold receivedWithKeypair
  simp only [branch,modifyPeer_source]
  repeat' first
    | (rx_retention_head keypairPut; exact (key_put _ _).wp (·=initial))
    | tx_work_step initial

theorem prepare_rest_work (pid : PeerId) (pkt : RxPacket) : SameView queued (prepareRest pid pkt) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold prepareRest timersAnyAuthenticatedPacketReceived WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head keepKeyFreshRx; exact (fresh_rx_work _).wp (·=initial))
    | (rx_retention_head delTimer; exact (delTimer_work _ _).wp (·=initial))
    | (rx_retention_head timersTraversal; exact (timersTraversal_work _).wp (·=initial))
    | (rx_retention_head timersDataReceived; exact (data_received_work _).wp (·=initial))
    | (rx_retention_head updateRxStats; exact (stats_work _ _).wp (·=initial))
    | (rx_retention_head dishonest; exact (dishonest_work _).wp (·=initial))
    | (rx_retention_head inetEcnDecapsulate; exact (store (inetEcnDecapsulate_sameWGStore _ _ _)).wp (·=initial))
    | tx_work_step initial

theorem lookup_repay_work (protocol : Nat) (bytes : List UInt8) : SameView queued (RxBorrow.source protocol bytes) := by
  apply (RxBorrow.source_frame protocol bytes).of_factor
    (fun s : WGStoreView×(PeerId→Option Peer)=>(s.1.dev.map (·.txWorkQueue)).getD []) queued
  intro w
  simp [PeerBorrow.view,PeerBorrow.outsidePeers,queued,wgStoreView,Option.map_map,Function.comp_def]

theorem finish_work (pid : PeerId) (ready : Packets.RxReady) : SameView queued (Packets.rxFinish pid ready) := by
  rw [←rxFinishSource_eq]
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold rxFinishSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head RxBorrow.source; exact (lookup_repay_work _ _).wp (·=initial))
    | (rx_retention_head updateRxStats; exact (stats_work _ _).wp (·=initial))
    | (rx_retention_head dishonest; exact (dishonest_work _).wp (·=initial))
    | tx_work_step initial

end Leanux.Proofs.WG.RetirementSecurity.TxWork
