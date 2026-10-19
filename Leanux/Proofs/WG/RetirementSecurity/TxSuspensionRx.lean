import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionAllowedips

/-! Native authenticated receive bookkeeping, promotion and source routing
retain the actual suspended actor records. Staging uses its separately checked
allocation/publication frame. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem endpoint_eq (a : Endpoint) (b : Option Endpoint) : Keeps (endpointEq a b) := by
  suspension_source [endpointEq,WG.andM] using [branch]

theorem endpoint (pid : PeerId) (value : Endpoint) : Keeps (setPeerEndpoint pid value) := by
  suspension_source [setPeerEndpoint,requireNotPending] using [peer,branch,endpoint_eq,set_peer,cache_reset]

theorem handshake_complete (pid : PeerId) (site : HiddenSite) : Keeps (timersHandshakeComplete pid site) := by
  suspension_source [timersHandshakeComplete] using [delete,peer,set_peer,hidden]

theorem data_received (pid : PeerId) : Keeps (timersDataReceived pid) := by
  suspension_source [timersDataReceived] using [device,peer,branch,timer,set_peer]

theorem fresh_rx (pid : PeerId) : Keeps (keepKeyFreshRx pid) := by
  suspension_source [keepKeyFreshRx,WG.andM] using [peer,branch,invariant,key,expired,set_peer,queued_handshake]

theorem stats (pid bytes : Nat) : Keeps (updateRxStats pid bytes) := by
  suspension_source [updateRxStats] using [modify_device,peer,set_peer]

theorem dishonest (why : Dishonest) : Keeps (WG.dishonest why) := by
  unfold WG.dishonest
  cases why <;> suspension_source [] using [modify_device]

theorem confirmation (pid : PeerId) (kid : KeypairId) : Keeps (receivedWithKeypair pid kid) := by
  unfold receivedWithKeypair
  simp only [modifyPeer_source]
  suspension_source [] using [peer,branch,set_peer,key_put]

theorem promote_send (pid : PeerId) (kid : KeypairId) : Keeps (promoteAndSend pid kid) := by
  suspension_source [promoteAndSend] using [confirmation,branch,handshake_complete,staged]

theorem decapsulate (protocol ds : Nat) (bytes : List UInt8) : Keeps (inetEcnDecapsulate protocol ds bytes) := by
  suspension_source [inetEcnDecapsulate,inetEcnSet,ipEcnSetCe,ipEcnSetEct1,ip6EcnSetCe,ip6EcnSetEct1]
    using [branch,unsupported,invariant]

theorem prepare_rest (pid : PeerId) (pkt : RxPacket) : Keeps (prepareRest pid pkt) := by
  suspension_source [prepareRest,timersAnyAuthenticatedPacketReceived,WG.andM,WG.orM]
    using [fresh_rx,delete,traversal,branch,stats,data_received,dishonest,decapsulate]

theorem finish_rx (pid : PeerId) (ready : Packets.RxReady) : Keeps (Packets.rxFinish pid ready) := by
  rw [←rxFinishSource_eq]
  suspension_source [rxFinishSource] using [lookup_repay,branch,dishonest,stats]

theorem receive_done (pid : PeerId) (pkt : RxPacket) (value : Endpoint) : Keeps (consumeDataDone pid pkt value) := by
  rw [Packets.consumeDataDone_factor,rxPrepare_factor]
  suspension_source [] using [endpoint,promote_send,prepare_rest,finish_rx]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
