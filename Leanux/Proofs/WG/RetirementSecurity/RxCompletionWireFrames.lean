import Leanux.Proofs.WG.RetirementSecurity.RxCompletionGeometry

/-! Native receive completion retains pending encryption-ring aliases and TX
packet cells outside its separately proved staged-send transfer. Confirmation
changes key slots, but cannot consume another packet's encryption work. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem endpoint_cryptWire (pid : PeerId) (endpoint : Endpoint) :
    SameView txCryptWire (setPeerEndpoint pid endpoint) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold setPeerEndpoint dstCacheReset requireNotPending
  simp (config := {zeta := false}) only [branch,getAmbient,hiddenJiffies]
  repeat' first
    | (rx_retention_head endpointEq; exact (cryptWire_store (endpointEq_sameStore _ _)).wp (· = initial))
    | crypt_wire_step initial

theorem handshakeComplete_cryptWire (pid : PeerId) (site : HiddenSite) :
    SameView txCryptWire (timersHandshakeComplete pid site) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold timersHandshakeComplete
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head delTimer; exact (delTimer_cryptWire _ _).wp (· = initial))
    | crypt_wire_step initial

theorem dataReceived_cryptWire (pid : PeerId) :
    SameView txCryptWire (timersDataReceived pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head modPeerTimer; exact (modPeerTimer_cryptWire _ _ _ _).wp (· = initial))
    | crypt_wire_step initial
  all_goals exact ((modPeerTimer_cryptWire _ _ _ _).map (fun _ => ())).wp (· = initial)

theorem freshRx_cryptWire (pid : PeerId) :
    SameView txCryptWire (keepKeyFreshRx pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head branchExpired
       exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => txCryptWire w = initial))
    | (rx_retention_head sendQueuedHandshakeInitiation
       exact (sendQueued_cryptWire _ _).wp (· = initial))
    | crypt_wire_step initial

theorem stats_cryptWire (pid : PeerId) (bytes : Nat) :
    SameView txCryptWire (updateRxStats pid bytes) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold updateRxStats
  repeat' crypt_wire_step initial

theorem dishonest_cryptWire (why : Dishonest) :
    SameView txCryptWire (dishonest why) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold dishonest
  cases why <;> repeat' crypt_wire_step initial

theorem prepareRest_cryptWire (pid : PeerId) (pkt : RxPacket) :
    SameView txCryptWire (prepareRest pid pkt) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold prepareRest timersAnyAuthenticatedPacketReceived WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head keepKeyFreshRx; exact (freshRx_cryptWire _).wp (· = initial))
    | (rx_retention_head delTimer; exact (delTimer_cryptWire _ _).wp (· = initial))
    | (rx_retention_head timersTraversal; exact (timersTraversal_cryptWire _).wp (· = initial))
    | (rx_retention_head timersDataReceived; exact (dataReceived_cryptWire _).wp (· = initial))
    | (rx_retention_head updateRxStats; exact (stats_cryptWire _ _).wp (· = initial))
    | (rx_retention_head dishonest; exact (dishonest_cryptWire _).wp (· = initial))
    | (rx_retention_head inetEcnDecapsulate
       exact (cryptWire_store (inetEcnDecapsulate_sameWGStore _ _ _)).wp (· = initial))
    | crypt_wire_step initial

theorem lookupRepay_cryptWire (protocol : Nat) (bytes : List UInt8) :
    SameView txCryptWire (RxBorrow.source protocol bytes) := by
  apply (RxBorrow.source_frame protocol bytes).of_factor
    (fun s => txCryptWire {dev := s.1.dev}) txCryptWire
  intro w
  unfold txCryptWire TxRing.nativeCell TxDisposition.txPackets
    PeerBorrow.view PeerBorrow.outsidePeers wgStoreView
  cases w.dev <;> rfl

theorem finishRx_cryptWire (pid : PeerId) (ready : Packets.RxReady) :
    SameView txCryptWire (Packets.rxFinish pid ready) := by
  rw [← rxFinishSource_eq]
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold rxFinishSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head RxBorrow.source; exact (lookupRepay_cryptWire _ _).wp (· = initial))
    | (rx_retention_head updateRxStats; exact (stats_cryptWire _ _).wp (· = initial))
    | (rx_retention_head dishonest; exact (dishonest_cryptWire _).wp (· = initial))
    | crypt_wire_step initial

theorem confirmation_cryptWire (pid : PeerId) (kid : KeypairId) :
    SameView txCryptWire (receivedWithKeypair pid kid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold receivedWithKeypair
  simp (config := {zeta := false}) only [branch,modifyPeer_source]
  repeat' first
    | (rx_retention_head keypairPut
       exact ((TxRing.keypairPut_frame _ _).product (TxDisposition.keyPut_packets _ _)).wp (· = initial))
    | crypt_wire_step initial

end Leanux.Proofs.WG.RetirementSecurity
