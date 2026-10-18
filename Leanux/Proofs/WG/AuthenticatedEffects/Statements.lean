import Leanux.Proofs.WG.AuthenticatedEffects.TimerRootClaims
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeCausalReceiver
import Leanux.Proofs.WG.AuthenticatedEffects.AdmissionCompletion
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeAdmissionFacts
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeAdmissionSource
import Leanux.Proofs.WG.AuthenticatedEffects.TransportInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.TransportWorkers
import Leanux.Proofs.WG.AuthenticatedEffects.DecryptWorkerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.MacRefusal
import Leanux.Proofs.WG.AuthenticatedEffects.TransportEntryChecks
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
import Leanux.Proofs.WG.AuthenticatedEffects.CookieAcceptance
import Leanux.Proofs.WG.AuthenticatedEffects.CookieProtocol

/-! T3 local cookie exception tranche. These claims establish the original
cookie-only dispatch, bounded construction/reply attempts and session frame.
Normal native receives have an actual emitted-datagram bound, source/bytes binding
and exact length 64. An erasing suffix observer retains actual append receipts
through a later Stop. Invalid MAC1 rejects with only under-load bookkeeping effects.
Native Noise refusals cannot emit or reach the receive timer/session suffix;
pre-lookup initiation refusals preserve the entire WG world, and all normal
initiation refusals restore complete peer records pointwise. Cookie acceptance
is observed before its first state write and through a later Stop. Native response
and cookie refusals preserve complete peer protocol records, masking just the two
reference-accounting fields and deriving safe repayment from the original lookup.
Full reference restoration remains conditional; whole-run causal closure is open. -/
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

/-- Security: an incoming cookie control message cannot elicit a transmission,
whether or not its own authentication succeeds. This is the complete original
handshake receive call on normal return, without a reference-count premise. -/
theorem received_cookie_is_silent (msg : Key) (src : SkbSource) (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_COOKIE)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    v.sent = w.sent := receive_cookie_sent msg src w v a b kind run

/-- Security: cookie acceptance is an actual successful authentication event
before the original cookie-state write, with at most one event per native
consumer invocation. Erasure preserves the original result and Stop; receipt
validity contains the original check, including the saved-MAC1 guard. -/
theorem cookie_acceptance_has_native_cause (msg : Key) (w : WGWorld) (a : Ambient)
    (h : List CookieAcceptance) :
    (runWGPrefix (acceptedCookie msg) w a h).1 = ((cookieMessageConsume msg).run w).run a ∧
      ∃ suffix, (runWGPrefix (acceptedCookie msg) w a h).2 = h ++ suffix ∧
        suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.input = msg ∧ r.Valid :=
  ⟨acceptedCookie_erases msg w a h,acceptedCookie_receipts msg w a h⟩

/-- Security: a recorded cookie acceptance carries successful original XChaCha
authentication under the selected peer's cookie-decryption key and saved MAC1.
This is an execution property of the modeled primitive, not cryptographic
unforgeability. Its receipt is emitted before cookie state can be changed. -/
theorem accepted_cookie_was_authenticated (r : CookieAcceptance) (valid : r.Valid) :
    ∃ cookie d p, r.checked.value = some cookie ∧ r.checked.before.dev = some d ∧
      d.peers[r.peer]? = some p ∧ p.haveSentMac1 = true ∧
      xchachaDecrypt p.cookieDecryptionKey ((r.input.drop 8).take 24)
        ((r.input.drop 32).take 32) p.lastMac1Sent = some cookie :=
  r.authenticated valid

/-- Security: a refused response restores all peer records and their timer and
session fields when its actual successful index lookup supplies the stated
`Borrowed` loan. Discharging that concrete index-lookup premise, including its
owner-word writeback, remains an initialized-caller obligation. -/
theorem response_refusal_preserves_borrowed_state (msg : Key) (w u v : WGWorld) (d : Device)
    (owner pid : PeerId) (a b c : Ambient)
    (device : w.dev = some d) (identity : d.staticIdentity.hasIdentity = true)
    (lookup : ((indexLookup [.handshake] (u32le msg 8)).run w).run
      (CounterWindow.record a .crespNoIdentity false) = .ok ((some (.handshake owner,pid),u),b))
    (borrowed : Leanux.Proofs.Framing.PeerBorrow.Borrowed
      (Leanux.Proofs.Framing.wgStoreView w) (some pid) (Leanux.Proofs.Framing.wgStoreView u))
    (refused : ((consumeResponse msg).run w).run a = .ok ((none,v),c)) :
    Leanux.Proofs.Framing.PeerBorrow.view v = Leanux.Proofs.Framing.PeerBorrow.view w :=
  response_refusal_after_lookup msg w u v d owner pid a b c device identity lookup borrowed refused

/-- Security: every normally refused original response preserves every peer's
session, endpoint, queue and timer fields. The projection excludes only the
reference count and nullable handshake-owner word; actual index acquisition
supplies safe repayment, so no initialized-reference hypothesis is needed. -/
theorem refused_response_preserves_peer_protocol (msg : Key) (w v : WGWorld) (a b : Ambient)
    (run : ((consumeResponse msg).run w).run a = .ok ((none,v),b)) :
    peerProtocolView v = peerProtocolView w := response_refusal_protocol msg w v a b run

/-- Security: an incoming unaccepted cookie message emits no datagram and
preserves all peer protocol fields, including endpoints, sessions and timers.
Unaccepted means the erasing original-source observer recorded no successful
cookie authentication; only reference count and nullable handshake-owner word
are outside this peer projection. The native lookup supplies its own loan. -/
theorem unaccepted_cookie_preserves_peer_protocol (msg : Key) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_COOKIE)
    (unaccepted : (runWGPrefix (acceptedCookie msg) w (CounterWindow.record a .hsCookie true) []).2 = [])
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    peerProtocolView v = peerProtocolView w ∧ v.sent = w.sent :=
  receive_unaccepted_cookie_protocol msg src w v a b kind unaccepted run

/-- Security: a complete original response receive refused by Noise cannot
emit or change any peer's session, endpoint or timer fields. Its actual load,
MAC and Noise runs are continuous; the peer projection masks only reference
count and nullable handshake-owner word, allowing the named lookup bookkeeping. -/
theorem refused_response_preserves_protocol_and_silence (msg : Key) (src : SkbSource) (loaded : Bool)
    (w u q v : WGWorld) (a b c d : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (load : (loadPhase.run w).run (CounterWindow.record a .hsCookie false) = .ok ((loaded,u),b))
    (mac : ((cookieValidatePacket msg src loaded).run u).run b =
      .ok ((authenticatedMac loaded,q),c))
    (refused : ((consumeResponse msg).run q).run (responseConsumerEntry loaded c) =
      .ok ((none,v),d)) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),v),CounterWindow.record d .hsRespNoPeer true) ∧
      peerProtocolView v = peerProtocolView w ∧ v.sent = w.sent :=
  receive_response_refused_protocol msg src loaded w u q v a b c d kind load mac refused

/-- Security: a native data decrypt cannot transmit or alter any peer field.
Its only possible WG-world mutation is the named pre-authentication receiving-key
policy invalidation, which returns no plaintext. All other normal outcomes,
including ciphertext authentication refusal, preserve the full WG world. -/
theorem data_decrypt_effect_is_only_policy_retirement (pkt : RxPacket) (result : Option RxPacket)
    (w v : WGWorld) (a b : Ambient)
    (run : ((decryptPacket pkt).run w).run a = .ok ((result,v),b)) :
    (v = w ∨ result = none ∧ ∃ d k c,
      w.dev = some d ∧ d.keypairs[pkt.keypair]? = some k ∧
      ((KeyTimes.receiveReject k).run w).run (CounterWindow.record a .decNoKeypair false) =
        .ok ((true,w),c) ∧
      v = CounterWindow.store w pkt.keypair {k with receiving := {k.receiving with isValid := false}}) ∧
      Leanux.Proofs.Framing.PeerBorrow.resident (Leanux.Proofs.Framing.wgStoreView v) =
        Leanux.Proofs.Framing.PeerBorrow.resident (Leanux.Proofs.Framing.wgStoreView w) ∧ v.sent = w.sent :=
  ⟨decryptPacket_effect pkt result w v a b run,decryptPacket_peer_and_sent pkt result w v a b run⟩

/-- Security: the original decrypt worker itself cannot emit. This local
composition leaves its actual IRQ and softirq callbacks visible; whole-driver
causality must account for packets processed by those callbacks. -/
theorem data_decrypt_worker_is_silent_when_callbacks_are (softirq irq : Leanux.M Unit)
    (softirqFrame : Leanux.Proofs.Framing.SameView (fun w : World => w.wg.sent) softirq)
    (irqFrame : Leanux.Proofs.Framing.SameView (fun w : World => w.wg.sent) irq) :
    Leanux.Proofs.Framing.SameView (fun w : World => w.wg.sent) (decryptStep softirq irq) :=
  decryptStep_sent_of_callbacks softirq irq softirqFrame irqFrame

/-- Security: every actual native replay-check receipt in a poll passed the
crypted-state guard and has the publication invariant at its real input, before
any consumer effects and even before a later Stop. The publication invariant is
a visible poll-entry premise; selected-cell and initialized-driver composition
remain separate obligations, so this does not claim whole-run authentication. -/
theorem data_replay_entry_keeps_publication (pid : PeerId) (budget : Nat) (w : World)
    (prior : List Lifetimes.LifetimeEvent) (history : List Queues.RxHistory.Event)
    (hi : PublicationHistory.Inv history w.wg)
    (occurrence id : Nat) (stamp : Lifetimes.PacketStamp) (pkt : RxPacket)
    (r : Leanux.Proofs.Logged.RunWitness Bool)
    (member : Queues.RxJoint.Event.checkedCounter occurrence id stamp pkt r ∈
      (Leanux.Proofs.Logged.runPrefix (Queues.RxJoint.poll pid budget) w
        (Queues.RxJoint.seed prior)).2) :
    PublicationHistory.Inv history r.before.wg ∧ pkt.state = .crypted ∧
      r.Valid (liftWG (counterValidate pkt.keypair pkt.nonce)) :=
  TransportEntryChecks.poll_counter_entry pid budget w prior history hi occurrence id stamp pkt r member

/-- Security: the actual packet reaching the replay check comes from a
strictly earlier successful authenticated publication in the supplied poll-entry
history. The receipt retains exact selected bytes, nonce and key-slot linkage
before any endpoint/consumer effect, including when that consumer later Stops.
The initialized theorem below establishes this entry history from the fixture. -/
theorem data_poll_preconsume_authentication (pid : PeerId) (budget : Nat) (w : World)
    (prior : List Lifetimes.LifetimeEvent) (history : List Queues.RxHistory.Event)
    (hi : PublicationHistory.Inv history w.wg)
    (occurrence id : Nat) (stamp : Lifetimes.PacketStamp) (pkt : RxPacket)
    (r : Leanux.Proofs.Logged.RunWitness Bool)
    (member : Queues.RxJoint.Event.checkedCounter occurrence id stamp pkt r ∈
      (Leanux.Proofs.Logged.runPrefix (Queues.RxJoint.poll pid budget) w
        (Queues.RxJoint.seed prior)).2) :
    TransportAuthenticatedEntry.Certified history id stamp pkt r :=
  TransportAuthenticatedEntry.poll pid budget w prior history hi occurrence id stamp pkt r member

/-- Security: the original decrypt worker, including its actual IRQ and softirq
polls, retains pre-consume authentication certificates on every reached prefix.
The input owner/publication invariant is visible in `TransportChecks.Inv`; the
initialized theorem below establishes it through the outer scheduler and runner. -/
theorem decrypt_worker_retains_preconsume_authentication :
    Leanux.Proofs.Logged.PrefixPreserves TransportChecks.Inv TransportChecks.Safe
      Queues.RxHistory.decryptStep := TransportChecks.decryptStep

/-- Security: any packet reaching the actual transport replay check was
published after an earlier successful native AEAD authentication in this same
initialized run, with exact plaintext, nonce and key-slot binding. This receipt
precedes endpoint and consumer effects and survives an internally stopped
consumer. Every typed trace and both placeholder modes are covered; no caller
invariant, trace-validity or completed-consumer assumption is required. This
closes transport authentication provenance, not all T3 send-root causality. -/
theorem initialized_transport_replay_has_authenticated_source (trace : Runner.Trace)
    (placeholders : Bool) (pre post : List Queues.RxHistory.Event) (occurrence id : Nat)
    (stamp : Lifetimes.PacketStamp) (pkt : RxPacket) (r : Leanux.Proofs.Logged.RunWitness Bool)
    (position : (Leanux.Proofs.Logged.runPrefixOuter
      (Queues.RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .checkedCounter occurrence id stamp pkt r :: post) :
    TransportAuthenticatedEntry.Certified pre id stamp pkt r :=
  TransportInitialized.replay_entry trace placeholders pre post occurrence id stamp pkt r position

/-- Security: an original initiation reaches its Noise/freshness/flood acceptance
cut before any peer protocol write, with at most one native acceptance receipt.
The receipt survives a later Stop, including the consumption-clock read. This
source-local claim does not yet establish whole-driver causal inheritance. -/
theorem initiation_acceptance_has_native_cause (msg : Key) (w : WGWorld) (a : Ambient)
    (h : List InitiationAcceptance) :
    (runWGPrefix (acceptedInitiation msg) w a h).1 = ((consumeInitiation msg).run w).run a ∧
      ∃ suffix, (runWGPrefix (acceptedInitiation msg) w a h).2 = h ++ suffix ∧
        suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.input = msg ∧ r.Valid :=
  ⟨acceptedInitiation_original msg w a h,acceptedInitiation_receipts msg w a h⟩

/-- Security: an original response reaches its Noise/state-recheck acceptance
cut before its first protocol write, with at most one native acceptance receipt,
retained through a later Stop. This is a native consumer claim; deferred causal
inheritance remains a separate obligation. -/
theorem response_acceptance_has_native_cause (msg : Key) (w : WGWorld) (a : Ambient)
    (h : List ResponseAcceptance) :
    (runWGPrefix (acceptedResponse msg) w a h).1 = ((consumeResponse msg).run w).run a ∧
      ∃ suffix, (runWGPrefix (acceptedResponse msg) w a h).2 = h ++ suffix ∧
        suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.input = msg ∧ r.Valid :=
  ⟨acceptedResponse_original msg w a h,acceptedResponse_receipts msg w a h⟩

/-- Security: the acceptance observer executes the complete original handshake
receiver, including its actual MAC gate, cookie exception and successful-send
suffixes, and preserves both native state endpoints or the exact Stop. This
statement is source equivalence; validity and causal completeness of the combined
receipt stream are separate obligations. -/
theorem original_handshake_admission_observer (msg : Key) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (h : List HandshakeAdmission) :
    (runWGPrefix (receiveAdmissions msg src) w a h).1 =
      ((receiveHandshakePacket msg src).run w).run a :=
  receiveAdmissions_erases msg src w a h

/-- Security: every initiation or response admission recorded by the complete
original receiver carries its actual successful MAC validation and native Noise
acceptance check for the same bytes. Receipts precede protocol writes and survive
later Stop outcomes. This native receive-call claim needs no authentication or
initialized-state premise; propagation through deferred work remains separate. -/
theorem original_handshake_admissions_authenticated (msg : Key) (src : SkbSource)
    (w : WGWorld) (a : Ambient) :
    ∀ r ∈ (runWGPrefix (receiveAdmissions msg src) w a []).2, r.Valid := by
  obtain ⟨suffix,history,safe,_⟩ := HandshakeAdmissionFacts.receive msg src w a []
    (by intro r member; cases member)
  exact safe

/-- Security: a successful native initiation consumer returns exactly the peer
named in its own pre-write acceptance receipt. The receipt is appended after
this call's incoming history, so an older unrelated admission cannot supply it.
The native check and finish executions remain visible as separate witnesses. -/
theorem initiation_success_has_own_admission (mac : HandshakeMac)
    (w v : WGWorld) (a b : Ambient) (h : List HandshakeAdmission) (pid : PeerId)
    (success : ((consumeInitiation mac.input).run w).run a = .ok ((some pid,v),b)) :
    ∃ accepted u c,
      (runWGPrefix (admitInitiation mac) w a h).2 =
        h ++ [.initiation mac ⟨some accepted,w,u,a,c⟩] ∧ accepted.peer = pid ∧
      ((initiationAcceptedCheck mac.input).run w).run a = .ok ((some accepted,u),c) ∧
      ((initiationAcceptedFinish mac.input accepted).run u).run c = .ok ((some pid,v),b) := by
  apply admitInitiation_success mac w v a b h _ pid
  exact Prod.ext ((admitInitiation_erases mac w a h).trans success) rfl

/-- Security: a successful native response consumer returns exactly the peer
named in its own pre-write acceptance receipt. The receipt is appended after
this call's incoming history, so an older unrelated admission cannot supply it.
The native check and finish executions remain visible as separate witnesses. -/
theorem response_success_has_own_admission (mac : HandshakeMac)
    (w v : WGWorld) (a b : Ambient) (h : List HandshakeAdmission) (pid : PeerId)
    (success : ((consumeResponse mac.input).run w).run a = .ok ((some pid,v),b)) :
    ∃ accepted u c,
      (runWGPrefix (admitResponse mac) w a h).2 =
        h ++ [.response mac ⟨some accepted,w,u,a,c⟩] ∧ accepted.peer = pid ∧
      ((responseAcceptedCheck mac.input).run w).run a = .ok ((some accepted,u),c) ∧
      ((responseAcceptedFinish mac.input accepted).run u).run c = .ok ((some pid,v),b) := by
  apply admitResponse_success mac w v a b h _ pid
  exact Prod.ext ((admitResponse_erases mac w a h).trans success) rfl

/-- Security: the callback observer executes the complete original handshake
receiver with exactly its native outcome, including Stops. Each callback entry
is recorded before the operation can produce effects. Cookie handling and loan
cleanup follow their separate native paths and are not callback admissions. -/
theorem original_handshake_callback_observer (msg : Key) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (h : List HandshakeCausal.Event) :
    (runWGPrefix (HandshakeCausal.receive msg src) w a h).1 =
      ((receiveHandshakePacket msg src).run w).run a :=
  HandshakeCausal.receive_erases msg src w a h

/-- Security: every protocol callback reached by the original handshake receiver
has a strictly earlier, MAC-and-Noise-authenticated admission for the same peer
in this call. This covers response transmission, session creation, endpoint
changes, keepalive and timer callbacks even if their native operation later
Stops. No authentication or initialization premise is assumed. Propagation
through later deferred work remains a separate T3 obligation. -/
theorem original_handshake_callbacks_have_authenticated_cause
    (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (pre post : List HandshakeCausal.Event) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (position : (runWGPrefix (HandshakeCausal.receive msg src) w a []).2 =
      pre ++ .callback kind pid :: post) :
    ∃ r ∈ HandshakeCausal.roots pre, r.Valid ∧ r.ForPeer pid :=
  HandshakeCausal.callback_cause msg src w a pre post kind pid position

/-- Security: observing the receiver's native timer arms preserves the complete
original result and both native state endpoints, or the exact Stop. Each arm
receipt is emitted after its actual arm operation and survives a later Stop;
no successful arm is fabricated when that operation itself fails. -/
theorem original_handshake_timer_arm_observer (msg : Key) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (h : List TimerRoot.Event) :
    (runWGPrefix (TimerRoot.receive msg src) w a h).1 =
      ((receiveHandshakePacket msg src).run w).run a :=
  TimerRoot.receive_erases msg src w a h

/-- Security: every completed session-derived or traversal timer-arm occurrence
in the original handshake receiver has an exact native execution witness and
names its own earlier callback entry by index. That entry has a strictly earlier
MAC-and-Noise-authenticated admission for the same peer. This closes the actual
handshake-to-arm edge, including later Stops; carrying the token across timer
storage and future dispatch remains a separate obligation. -/
theorem original_handshake_timer_arms_have_authenticated_cause
    (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (pre post : List TimerRoot.Event) (r : TimerRoot.Arm)
    (position : (runWGPrefix (TimerRoot.receive msg src) w a []).2 =
      pre ++ .armed r :: post) :
    TimerRoot.Authenticated pre r :=
  TimerRoot.arm_authenticated msg src w a pre post r position

end Leanux.Proofs.WG.AuthenticatedEffects
