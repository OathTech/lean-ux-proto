import Leanux.Proofs.WG.AuthenticatedEffects.Frames
import Leanux.Proofs.WG.AuthenticatedEffects.ReplyBinding
import Leanux.Proofs.WG.AuthenticatedEffects.Emission
import Leanux.Proofs.WG.AuthenticatedEffects.CryptoSizes
import Leanux.Proofs.WG.AuthenticatedEffects.CookieEmissionObservation
import Leanux.Proofs.WG.AuthenticatedEffects.SilenceFrames
import Leanux.Proofs.WG.AuthenticatedEffects.RefusalEmission
import Leanux.Proofs.WG.AuthenticatedEffects.InitiationFront
import Leanux.Proofs.WG.AuthenticatedEffects.BorrowedRefusal
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeQuietFrames

/-! T3 local cookie exception tranche. These claims establish the original
cookie-only dispatch, bounded construction/reply attempts and session frame.
Normal native receives have an actual emitted-datagram bound, source/bytes binding
and exact length 64. An erasing suffix observer retains actual append receipts
through a later Stop. Invalid MAC1 rejects with only under-load bookkeeping effects.
Native Noise refusals cannot emit or reach the receive timer/session suffix;
pre-lookup initiation refusals preserve the entire WG world, and all normal
initiation refusals restore complete peer records pointwise. Whole-run causal
closure and response peer/timer restoration remain open. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Cookies

/-- Security: qualifying invalid-MAC2 initiations and responses execute only the
original cookie-reply suffix. The continuous `FailedMac2` witness supplies the
actual under-load/MAC checks; this local claim covers both normal and Stop results. -/
theorem cookie_exception_original_path (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (h : FailedMac2 msg src w a) :
    ((receiveHandshakePacket msg src).run w).run a =
      ((sendHandshakeCookie msg src).run h.made).run (cookieReplyEntry msg h.checked) :=
  qualifying_rejected_run msg src w a kind h

/-- Security: the qualifying unauthenticated cookie exception cannot modify the
Noise/session projection on a normally completed native receive. Cookie-secret
maintenance and transmission statistics lie outside this named R6 projection. -/
theorem cookie_exception_preserves_sessions (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (h : FailedMac2 msg src w a)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    noiseView v = noiseView w := qualifying_rejected_noise msg src w v a b kind h run

/-- Security: a native cookie-reply invocation completes at most one cookie
construction, with the exact original input and source. Its receipt survives a
later Stop; this bounds construction attempts, not emitted datagrams. -/
theorem cookie_exception_one_creation (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (history : List CookieAttempt) :
    ∃ suffix, (runWGPrefix (cookieObserved msg src) w a history).2 = history ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.input = msg ∧ r.source = src ∧ r.Valid :=
  cookieObserved_receipts msg src w a history

/-- Security: the original cookie reply reaches at most one guarded socket-call
attempt, carrying exactly the supplied source and cookie bytes. Its receipt is
retained even if that socket call stops; successful emission is not assumed. -/
theorem cookie_exception_one_socket_attempt (src : SkbSource) (bytes : List UInt8)
    (w : WGWorld) (a : Ambient) (history : List ReplyAttempt) :
    ∃ suffix, (runWGPrefix (replyObserved src bytes) w a history).2 = history ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.source = src ∧ r.bytes = bytes ∧ r.Valid :=
  replyObserved_receipts src bytes w a history

/-- Security: the qualifying unauthenticated cookie exception emits at most one
actual datagram, addressed to the triggering source and carrying exactly the
original cookie construction's bytes. This is a normal native receive claim;
whole-run authenticated causal closure is a separate obligation. -/
theorem cookie_exception_transmission_bound (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (h : FailedMac2 msg src w a)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    ∃ bytes u c,
      ((cookieMessageCreate (u32le msg 4) src ((msg.drop (msg.length - 32)).take 16)).run h.made).run
        (cookieReplyEntry msg h.checked) = .ok ((bytes,u),c) ∧
      ReplyEmission src bytes w.sent v.sent :=
  qualifying_cookie_emission msg src w v a b kind h run

/-- Security: a qualifying unauthenticated cookie response emits at most one
64-byte datagram addressed to the triggering source and preserves the named
Noise/session projection. Both initiation and response dispatch arms are covered;
the actual native receive and its continuous MAC/load witness remain explicit. -/
theorem cookie_exception_fixed_width (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (h : FailedMac2 msg src w a)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    (∃ suffix, v.sent = w.sent ++ suffix ∧ suffix.length ≤ 1 ∧
      ∀ d ∈ suffix, d.addr = src.saddr ∧ d.port = src.sport ∧ d.bytes.length = 64) ∧
      noiseView v = noiseView w := by
  obtain ⟨bytes,u,c,created,suffix,eq,len,members⟩ :=
    qualifying_cookie_emission msg src w v a b kind h run
  have width := cookieMessageCreate_length _ src _ h.made u _ c bytes created
  refine ⟨⟨suffix,eq,len,?_⟩,qualifying_rejected_noise msg src w v a b kind h run⟩
  intro d mem
  obtain ⟨addr,port,data⟩ := members d mem
  exact ⟨addr,port,by simpa only [data] using width⟩

/-- Security: the actual cookie-emission observer records at most one native
append, addressed to the triggering source and exactly 64 bytes long. These
receipts survive subsequent Stop outcomes; `cookieEmitted_erases` ties the
observer to the original sender, and `qualifying_cookie_observer_erases` ties its
reached suffix to either original qualifying receive. This is a local path claim. -/
theorem cookie_exception_emission_prefix (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (history : List DatagramReceipt) :
    ∃ suffix, (runWGPrefix (cookieEmitted msg src) w a history).2 = history ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix,
        r.Valid ∧ r.endpoint.addr = src.saddr ∧ r.endpoint.port = src.sport ∧
        r.bytes.length = 64 ∧ r.ds = 0 :=
  cookieEmitted_receipts msg src w a history

/-- Security: an invalid-MAC1 handshake datagram has no peer, timer or egress
effect. The only excluded WG field is the explicit function-static under-load
timestamp; actual branch/drop records remain in Ambient. This covers both load
arms after the supplied native load-phase execution and is a normal-run claim. -/
theorem invalid_mac1_has_no_peer_timer_or_egress_effect (msg : List UInt8) (src : SkbSource)
    (w u v : WGWorld) (a b c : Ambient) (d : Device) (loaded : Bool)
    (notCookie : messageType msg ≠ MESSAGE_HANDSHAKE_COOKIE)
    (load : (loadPhase.run w).run (CounterWindow.record a .hsCookie false) =
      .ok ((loaded,u),b))
    (hd : u.dev = some d) (bad : mac1Computed d msg ≠ mac1Given msg)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),c)) :
    quietView v = quietView w :=
  receive_bad_mac1_quiet msg src w u v a b c d loaded notCookie load hd bad run

/-- Security: an initiation rejected by its native Noise consumer emits no
datagram and exits before the receive endpoint, response, session and timer
suffix. The three supplied native runs form one continuous load/MAC/Noise path;
the consumer's own reference-cleanup effects remain visible rather than assumed
away. This is a normal original receive claim. -/
theorem noise_refused_initiation_is_silent (msg : List UInt8) (src : SkbSource) (loaded : Bool)
    (w u q v : WGWorld) (a b c d : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (load : (loadPhase.run w).run (CounterWindow.record a .hsCookie false) = .ok ((loaded,u),b))
    (mac : ((cookieValidatePacket msg src loaded).run u).run b =
      .ok ((authenticatedMac loaded,q),c))
    (refused : ((consumeInitiation msg).run q).run (initiationConsumerEntry loaded c) =
      .ok ((none,v),d)) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),v),CounterWindow.record d .hsInitNoPeer true) ∧ v.sent = w.sent :=
  receive_initiation_refused_sent msg src loaded w u q v a b c d kind load mac refused

/-- Security: a response rejected by its native Noise consumer emits no
datagram and exits before the receive endpoint, session, keepalive and timer
suffix. The actual load/MAC/Noise executions are continuous; no lifetime or
initialized-state premise is needed for this egress claim, and reference cleanup
is not asserted to restore the peer projection here. -/
theorem noise_refused_response_is_silent (msg : List UInt8) (src : SkbSource) (loaded : Bool)
    (w u q v : WGWorld) (a b c d : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (load : (loadPhase.run w).run (CounterWindow.record a .hsCookie false) = .ok ((loaded,u),b))
    (mac : ((cookieValidatePacket msg src loaded).run u).run b =
      .ok ((authenticatedMac loaded,q),c))
    (refused : ((consumeResponse msg).run q).run (responseConsumerEntry loaded c) =
      .ok ((none,v),d)) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),v),CounterWindow.record d .hsRespNoPeer true) ∧ v.sent = w.sent :=
  receive_response_refused_sent msg src loaded w u q v a b c d kind load mac refused

/-- Security: an initiation rejected before public-key lookup changes no WG
state: no peer reference, timer or egress effect occurs. The original factored
prefix includes the identity, DH and static-ciphertext authentication guards;
the remaining observable changes are the actual Ambient branch/drop records. -/
theorem initiation_prelookup_refusal_has_no_effect (msg : List UInt8)
    (w u : WGWorld) (a b : Ambient)
    (front : ((initiationAuthFront msg).run w).run a = .ok ((none,u),b)) :
    ((consumeInitiation msg).run w).run a =
      .ok ((none,w),CounterWindow.record (CounterWindow.record b .consumeFailedPut true) .peerPutNull true) :=
  initiation_prelookup_refused msg w u a b front

/-- Security: a refused original initiation restores every complete peer record,
including reference counts, handshake/session state and peer timer fields, and
all seven WG-store fields outside the peer map. Actual lookup positivity and
balanced repayment prove this without an initialized-lifetime premise. TreeMap
representation, outer WG scheduling fields and Ambient records are outside this
named projection; the separate egress theorem covers sent datagrams. -/
theorem initiation_refusal_preserves_all_peers (msg : List UInt8)
    (w v : WGWorld) (a b : Ambient)
    (run : ((consumeInitiation msg).run w).run a = .ok ((none,v),b)) :
    Leanux.Proofs.Framing.PeerBorrow.view v = Leanux.Proofs.Framing.PeerBorrow.view w :=
  initiation_refusal_restores_peers msg w v a b run

/-- Security: a complete original initiation receive refused by Noise emits
no datagram and preserves every peer record, including session and timer fields.
The seven-field store projection masks only cookie-secret maintenance, the two
rate-limit tables and peer-map representation. The supplied native load/MAC/Noise
runs are continuous; outer WG scheduling and Ambient records remain outside this
store claim. -/
theorem refused_initiation_preserves_state_and_silence (msg : List UInt8) (src : SkbSource) (loaded : Bool)
    (w u q v : WGWorld) (a b c d : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (load : (loadPhase.run w).run (CounterWindow.record a .hsCookie false) = .ok ((loaded,u),b))
    (mac : ((cookieValidatePacket msg src loaded).run u).run b =
      .ok ((authenticatedMac loaded,q),c))
    (refused : ((consumeInitiation msg).run q).run (initiationConsumerEntry loaded c) =
      .ok ((none,v),d)) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),v),CounterWindow.record d .hsInitNoPeer true) ∧
      handshakeQuietView v = handshakeQuietView w ∧ v.sent = w.sent :=
  receive_initiation_refused_quiet msg src loaded w u q v a b c d kind load mac refused

end Leanux.Proofs.WG.AuthenticatedEffects
