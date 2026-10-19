import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionHandshakeCore

/-! Complete native handshake receive and send paths retain suspended TX
actors, including cookie reply routing, ratelimiter records and keepalives. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem send_buffer (pid : PeerId) (msg : List UInt8) : Keeps (sendBufferToPeer pid msg) := by
  suspension_source [sendBufferToPeer] using [allocation,branch,peer,set_peer,send4_call,send6_call]

theorem session_derived (pid : PeerId) : Keeps (timersSessionDerived pid) := by
  suspension_source [timersSessionDerived] using [timer]

theorem handshake_initiated (pid : PeerId) : Keeps (timersHandshakeInitiated pid) := by
  suspension_source [timersHandshakeInitiated] using [caller_jiffies,jitter,guard,arm]

theorem send_response (pid : PeerId) : Keeps (sendHandshakeResponse pid) := by
  suspension_source [sendHandshakeResponse,timersAnyAuthenticatedPacketSent] using [clock,peer,set_peer,
    create_response,branch,invariant,add_mac,session,session_derived,traversal,delete,send_buffer]

theorem send_initiation (pid : PeerId) : Keeps (sendHandshakeInitiation pid) := by
  suspension_source [sendHandshakeInitiation,timersAnyAuthenticatedPacketSent] using [peer,expired,clock,set_peer,
    create_initiation,branch,invariant,add_mac,traversal,delete,send_buffer,handshake_initiated]

theorem send_worker (pid : PeerId) : Keeps (handshakeSendWorker pid) := by
  suspension_source [handshakeSendWorker] using [send_initiation,peer_put]

theorem clear_worker (pid : PeerId) : Keeps (queuedExpiredZeroKeyMaterial pid) := by
  suspension_source [queuedExpiredZeroKeyMaterial] using [handshake_clear,key_clear,peer_put]

theorem keepalive_prepare (pid : PeerId) : Keeps (OccurrenceHandshake.keepalivePrepare pid) := by
  suspension_source [OccurrenceHandshake.keepalivePrepare] using [peer,branch,allocation,set_peer,device]

theorem keepalive (pid : PeerId) : Keeps (sendKeepalive pid) := by
  rw [OccurrenceHandshake.keepalive_factor]
  suspension_source [] using [keepalive_prepare,staged]

theorem handshake_endpoint (pid : PeerId) (src : SkbSource) : Keeps (setPeerEndpointFromSkb pid src) := by
  suspension_source [setPeerEndpointFromSkb] using [endpoint_from,branch,endpoint,invariant]

theorem cookie_consume (msg : List UInt8) : Keeps (cookieMessageConsume msg) := by
  suspension_source [cookieMessageConsume] using [index_lookup,branch,invariant,peer,peer_put,clock,set_peer]

theorem cookie_make (src : SkbSource) : Keeps (makeCookie src) := by
  suspension_source [makeCookie] using [device,expired,clock,hidden,modify_device,branch]

theorem clock_int (site : HiddenSite) : Keeps (hiddenClock site : StateT S AmbientM Int) := by
  apply ambient
  exact (TxActorFrames.hidden site).bind (fun _=>SameView.pure _ _)

theorem ratelimiter (src : SkbSource) : Keeps (ratelimiterAllow src) := by
  suspension_source [ratelimiterAllow] using [branch,invariant,clock_int,compare,unsupported,allocation]

theorem cookie_validate (msg : List UInt8) (src : SkbSource) (check : Bool) : Keeps (cookieValidatePacket msg src check) := by
  suspension_source [cookieValidatePacket] using [device,branch,cookie_make,ratelimiter]

theorem reply_buffer (src : SkbSource) (msg : List UInt8) : Keeps (sendBufferAsReplyToSkb src msg) := by
  suspension_source [sendBufferAsReplyToSkb] using [branch,invariant,endpoint_from,allocation,send4_call,send6_call]

theorem cookie_create (index : Nat) (src : SkbSource) (mac : List UInt8) : Keeps (cookieMessageCreate index src mac) := by
  suspension_source [cookieMessageCreate] using [hidden,cookie_make,device]

theorem cookie_reply (msg : List UInt8) (src : SkbSource) : Keeps (sendHandshakeCookie msg src) := by
  suspension_source [sendHandshakeCookie] using [cookie_create,reply_buffer]

theorem after_mac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Keeps (Cookies.afterMac msg src loaded state) := by
  suspension_source [Cookies.afterMac,WG.andM,WG.orM,timersAnyAuthenticatedPacketReceived]
    using [branch,invariant,cookie_reply,consume_initiation,consume_response,handshake_endpoint,
      send_response,session,session_derived,handshake_complete,keepalive,peer,set_peer,modify_device,
      delete,traversal,peer_put]

theorem cookie_load : Keeps Cookies.loadPhase := by
  suspension_source [Cookies.loadPhase,birthdateTest] using [device,branch,compare,clock,invariant]

theorem handshake_receive (msg : List UInt8) (src : SkbSource) : Keeps (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  suspension_source [] using [branch,cookie_consume,cookie_load,cookie_validate,after_mac]

theorem receive_step : Keeps WG.receiveStep := by
  suspension_source [WG.receiveStep] using [device,branch,modify_device,handshake_receive]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
