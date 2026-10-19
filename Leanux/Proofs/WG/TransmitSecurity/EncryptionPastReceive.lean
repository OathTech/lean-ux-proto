import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastReceiveFrames

/-! Authenticated receive completion may stage a reply, but cannot reintroduce
an already encrypted packet identity. All refusal, lookup and cleanup arms are
those of the original consumeDataDone action. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TxDisposition RetirementSecurity
set_option maxHeartbeats 600000

/-- Native receive completion retains the supplied historical carrier through
confirmation, reply staging, endpoint updates, timers and allowed-IP checking. -/
theorem receive (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves (Ready past active) (WG.consumeDataDone pid pkt endpoint) := by
  let P := Ready past active
  have ep := ready_endpoint (past := past) (active := active) pid
  have received := ready_received (past := past) (active := active) pid
  have staged := send (past := past) (active := active) pid
  have fresh := ready_fresh (past := past) (active := active) pid
  have complete (site : HiddenSite) : Preserves P (timersHandshakeComplete pid site) :=
    ready_frame (LiveFrontier.handshake_complete pid site) (handshake_complete pid site)
  have anyReceived : Preserves P (timersAnyAuthenticatedPacketReceived pid) :=
    ready_frame (LiveFrontier.authenticated_received pid) (del_timer pid .newHandshake)
  have traverse : Preserves P (timersTraversal pid) :=
    ready_frame (LiveFrontier.traversal pid) (traversal pid)
  have data : Preserves P (timersDataReceived pid) :=
    ready_frame (LiveFrontier.data_received pid) (data_received pid)
  have stats := ready_stats (past := past) (active := active) pid
  have dishonest := ready_dishonest (past := past) (active := active)
  have lookup := ready_lookup (past := past) (active := active)
  have pay (peer : Option PeerId) : Preserves P (peerPut peer) :=
    ready_frame (LiveFrontier.peer_put peer) (peer_put peer)
  have ecn (protocol outer : Nat) (bytes : List UInt8) : Preserves P (inetEcnDecapsulate protocol outer bytes) :=
    ready_store (inetEcnDecapsulate_sameWGStore protocol outer bytes)
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  rxstack_preserves_source [WG.consumeDataDone,WG.andM,WG.orM,branch]
    using [ep,received,staged,fresh,complete,anyReceived,traverse,data,stats,dishonest,lookup,pay,ecn,ambient]

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
