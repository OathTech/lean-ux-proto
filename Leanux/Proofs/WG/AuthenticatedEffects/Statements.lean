import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsProjection
import Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffectsFocus
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEffectsFrames
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerParametric
import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsErasure
import Leanux.Proofs.WG.AuthenticatedEffects.CandidateCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.CandidatePollSource
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEffects
import Leanux.Proofs.WG.AuthenticatedEffects.TransportJournalInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierOuter
import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierTraffic
import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierScheduler
import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierReceive
import Leanux.Proofs.WG.AuthenticatedEffects.TransportConfirmationEntry
import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayPoll
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerSafety
import Leanux.Proofs.WG.AuthenticatedEffects.TransportPublicationCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.TimerDispatchScope
import Leanux.Proofs.WG.AuthenticatedEffects.TimerReceiverCausality
import Leanux.Proofs.WG.AuthenticatedEffects.SendQueueCausality
import Leanux.Proofs.WG.AuthenticatedEffects.SendWorkClaims
import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootClaims
import Leanux.Proofs.WG.AuthenticatedEffects.TimerSelection
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

/-- Security: a native timer arm carries prior timer causes through every
ordinary return. A changed target receives this arm's exact occurrence receipt;
a no-change arm and all other timer slots retain their prior causes. The input
carrier is explicit and is not yet claimed for the complete initialized driver. -/
theorem native_timer_arm_transports_occurrence_causes (origin : Nat)
    (kind : HandshakeCausal.Kind) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (caller : Option UInt64) :
    Leanux.Proofs.Logged.StatePrefixPreserves (fun h w _ => TimerSlots.Carrier h w) (fun _ => True)
      (TimerRoot.arm origin kind pid timer delay caller) :=
  TimerSlots.arm_preserves origin kind pid timer delay caller

/-- Security: deletion retires the selected timer occurrence and preserves
causes for the remaining live timers. The input carrier is explicit; this
native store step does not assume that timer callbacks have already run. -/
theorem native_timer_delete_transports_occurrence_causes (pid : PeerId) (timer : PeerTimer) :
    Leanux.Proofs.Logged.StatePrefixPreserves (fun h w _ => TimerSlots.Carrier h w) (fun _ => True)
      (liftWGPrefix (delTimer pid timer) : WGPrefix TimerRoot.Event Unit) :=
  TimerSlots.delete_preserves pid timer

/-- Security: the actual wheel selector retrieves the stored cause of the
selected occurrence with exact peer, timer kind, incarnation, expiry and
queue stamp. This closes the selector's local obligation under the named
carrier; initialization and transport through all native callers remain open. -/
theorem native_timer_selection_retains_occurrence_cause (h : List TimerRoot.Event)
    (w : WGWorld) (d : Device) (device : w.dev = some d) (carrier : TimerSlots.Carrier h w)
    (j : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (selected : TimerWheel.nextDue d j = some (pid,timer,entry)) :
    ∃ stamp expires, TimerSlots.HasCause h pid timer stamp expires entry :=
  TimerSlots.nextDue_cause h w d device carrier j pid timer entry selected

/-- Security: observing actual work creation in the complete handshake receiver
preserves its native result and both state endpoints, including Stops. Receipts
for completed queue appends and data submissions survive a later Stop. -/
theorem original_handshake_work_observer (msg : Key) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (h : List TimerRoot.Event) :
    (runWGPrefix (WorkRoot.receive msg src) w a h).1 =
      ((receiveHandshakePacket msg src).run w).run a :=
  WorkRoot.receive_erases msg src w a h

/-- Security: every observed handshake-work queue append in the complete native
receiver is its actual append operation and has its own indexed, earlier
MAC-and-Noise-authenticated callback cause. The claim covers later Stops;
forwarding the occurrence through deferred execution remains separate. -/
theorem original_handshake_work_queue_has_authenticated_cause
    (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (pre post : List TimerRoot.Event) (r : TimerRoot.Queued)
    (position : (runWGPrefix (WorkRoot.receive msg src) w a []).2 =
      pre ++ .queued r :: post) :
    r.Native ∧ WorkRoot.AuthenticatedAt pre r.origin r.kind r.peer ∧
      r.run.after.dev = r.run.before.dev.map
        (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [r.peer]}) := by
  obtain ⟨native,cause⟩ := WorkRoot.queued_authenticated msg src w a pre post r position
  exact ⟨native,cause,WorkRoot.queued_native_append r native⟩

/-- Security: every observed data submission from the complete native handshake
receiver executes the original createData on exactly the recorded peer and
packet identifiers, under its own indexed authenticated callback cause. This
records a submission, which may drop packets; it does not assert successful
queueing, encryption or transmission of every item. -/
theorem original_handshake_data_submission_has_authenticated_cause
    (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (pre post : List TimerRoot.Event) (r : TimerRoot.Submitted)
    (position : (runWGPrefix (WorkRoot.receive msg src) w a []).2 =
      pre ++ .submitted r :: post) :
    r.Native ∧ WorkRoot.AuthenticatedAt pre r.origin r.kind r.peer :=
  WorkRoot.submitted_authenticated msg src w a pre post r position

/-- Security: a completed native handshake-work append creates one fresh
causal ticket for its journal position and preserves every existing occurrence.
The live-device and input-carrier obligations remain explicit; a native
modifyDev on an absent device cannot manufacture an actual queued occurrence. -/
theorem native_handshake_queue_append_transports_occurrence_causes
    (h : List TimerRoot.Event) (tickets : List SendWorkCauses.Ticket) (r : TimerRoot.Queued)
    (carrier : SendWorkCauses.Carrier h tickets r.run.before)
    (native : r.Native) (device : r.run.before.dev.isSome) :
    SendWorkCauses.Carrier (h ++ [.queued r]) (tickets ++ [⟨h.length,r⟩]) r.run.after :=
  carrier.enqueue r native device

/-- Security: the dispatch observer records the actual native queued-peer
selection before dequeue and execution. It preserves the complete original
runOneSendWorker result, including any later Stop inside the worker. -/
theorem original_handshake_work_dispatch_observer :
    ErasesPrefix SendWorkCauses.dispatch Env.runOneSendWorker :=
  SendWorkCauses.dispatch_erases

/-- Security: a completed native handshake-work dispatch consumes the first
matching queue occurrence and preserves the ordered, distinct tickets for all
remaining occurrences, including duplicate peer identifiers. The queue carrier
is an explicit input, not yet a whole-driver initialized invariant. -/
theorem original_handshake_work_dispatch_transports_occurrence_causes
    (h : List TimerRoot.Event) (tickets : List SendWorkCauses.Ticket) (w v : World)
    (carrier : SendWorkCauses.Carrier h tickets w.wg) (r : RunWitness PeerId)
    (reached : r ∈ (runPrefix SendWorkCauses.dispatch w []).2)
    (run : (runPrefix SendWorkCauses.dispatch w []).1 = .ok ((),v)) :
    ∃ ticket rest, SendWorkCauses.Selected tickets r.value ticket rest ∧ ticket.Valid h ∧
      SendWorkCauses.Carrier h rest v.wg :=
  SendWorkCauses.dispatch_completed w v carrier r reached run

/-- Security: the native selected handshake-work occurrence inherits its own
indexed authenticated receiver callback, even when the later worker Stops.
This joins the actual receiver and dispatcher source cuts under the explicit
ordered queue carrier; initialization and intervening driver transport remain
open and are not replaced by a prior admission for the same peer. -/
theorem original_handshake_work_dispatch_inherits_occurrence_cause
    (msg : Key) (src : SkbSource) (before : WGWorld) (ambient : Ambient)
    (w : World) (tickets : List SendWorkCauses.Ticket)
    (carrier : SendWorkCauses.Carrier
      (runWGPrefix (WorkRoot.receive msg src) before ambient []).2 tickets w.wg)
    (r : RunWitness PeerId) (reached : r ∈ (runPrefix SendWorkCauses.dispatch w []).2) :
    ∃ ticket rest pre post,
      SendWorkCauses.Selected tickets r.value ticket rest ∧ ticket.peer = r.value ∧
      (runWGPrefix (WorkRoot.receive msg src) before ambient []).2 = pre ++ .queued ticket.receipt :: post ∧
      pre.length = ticket.index ∧
      WorkRoot.AuthenticatedAt pre ticket.receipt.origin ticket.receipt.kind ticket.peer :=
  SendWorkCauses.dispatch_authenticated msg src before ambient w tickets carrier r reached

/-- Security: the exact native handshake queueing source preserves the ordered
causal inventory, creating tickets only for its actual queue append. Freshness,
dead-peer and already-pending exits keep their native behavior and existing
queue causes. The input inventory is explicit. -/
theorem original_handshake_queueing_transports_inventory (origin : Nat)
    (kind : HandshakeCausal.Kind) (pid : PeerId) (retry : Bool) :
    SendWorkCauses.Preserves (WorkRoot.queued origin kind pid retry) :=
  SendWorkCauses.queued_preserves origin kind pid retry

/-- Security: the exact native staging path preserves handshake-work causes
through key checks, nonce reservation, allocation, submission and drops. Each
new handshake-work occurrence receives its own receipt ticket; crypt/TX queues
are outside this specifically named handshake-work inventory. -/
theorem original_staging_transports_handshake_work_inventory (origin : Nat)
    (kind : HandshakeCausal.Kind) (pid : PeerId) :
    SendWorkCauses.Preserves (WorkRoot.staging origin kind pid) :=
  SendWorkCauses.staging_preserves origin kind pid

/-- Security: the original keepalive source transports the ordered handshake
work inventory through its real allocation and staging branches. Together with
the receiver's callback proof this discharges its concrete work-creation edge;
whole-driver initialization and crypt-work provenance remain separate. -/
theorem original_keepalive_transports_handshake_work_inventory (origin : Nat) (pid : PeerId) :
    SendWorkCauses.Preserves (WorkRoot.keepalive origin pid) :=
  SendWorkCauses.keepalive_preserves origin pid

/-- Security: the complete original handshake receiver transports every
ordered handshake-work occurrence and its journal ticket through actual native
callbacks, including reference releases. The input inventory is explicit;
no ownership hypothesis is needed for this queue projection. -/
theorem original_receiver_transports_handshake_work_inventory (msg : Key) (src : SkbSource) :
    SendWorkCauses.Preserves (WorkRoot.receive msg src) :=
  SendWorkCauses.receive_preserves msg src

/-- Security: starting with an empty handshake-work queue, every occurrence
remaining after the original receiver completes has a distinct native append
receipt in that same receiver's journal. This derives the output inventory
from the native receive execution rather than assuming it. -/
theorem original_receiver_initializes_handshake_work_inventory
    (msg : Key) (src : SkbSource) (w v : WGWorld) (a b : Ambient)
    (empty : SendWorkCauses.queue w = [])
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    ∃ tickets, SendWorkCauses.Carrier (runWGPrefix (WorkRoot.receive msg src) w a []).2 tickets v :=
  SendWorkCauses.receive_from_empty msg src w v a b empty run

/-- Security: a native handshake-work dispatch immediately following a completed
native receive from an empty queue inherits its selected occurrence's own earlier
authenticated callback. The dispatch receipt precedes worker execution, retaining
this cause through an internal Stop. This concrete two-operation claim assumes
no output carrier; transport through intervening driver actions remains separate. -/
theorem original_receiver_then_worker_inherits_authenticated_occurrence
    (msg : Key) (src : SkbSource) (before : WGWorld) (ambient : Ambient) (w : World)
    (empty : SendWorkCauses.queue before = [])
    (received : ((receiveHandshakePacket msg src).run before).run ambient = .ok (((),w.wg),w.ambient))
    (r : RunWitness PeerId) (reached : r ∈ (runPrefix SendWorkCauses.dispatch w []).2) :
    ∃ tickets ticket rest pre post,
      SendWorkCauses.Carrier (runWGPrefix (WorkRoot.receive msg src) before ambient []).2 tickets w.wg ∧
      SendWorkCauses.Selected tickets r.value ticket rest ∧ ticket.peer = r.value ∧
      (runWGPrefix (WorkRoot.receive msg src) before ambient []).2 = pre ++ .queued ticket.receipt :: post ∧
      pre.length = ticket.index ∧
      WorkRoot.AuthenticatedAt pre ticket.receipt.origin ticket.receipt.kind ticket.peer :=
  SendWorkCauses.receiver_then_dispatch_authenticated msg src before ambient w empty received r reached

/-- Security: a timer scope retains its selected live wheel occurrence's
cause before validation, deletion and callback, even if that suffix Stops.
The caller's actual saved-device equality, successful nextDue selection and
input timer carrier are explicit; shared-driver initialization remains open. -/
theorem selected_timer_scope_retains_occurrence_cause
    (record : TimerDispatch.Selection → E) (d : Device) (j : UInt64) (pid : PeerId)
    (timer : PeerTimer) (entry : WheelEntry) {body : PrefixM E α} (appends : Appends body)
    (w : World) (h : List E) (roots : List TimerRoot.Event)
    (saved : w.wg.dev = some d) (selected : TimerWheel.nextDue d j = some (pid,timer,entry))
    (carrier : TimerSlots.Carrier roots w.wg) :
    ∃ suffix, (runPrefix (TimerDispatch.scope record d j pid timer entry body) w h).2 =
      h ++ record ⟨d,j,pid,timer,entry,w⟩ :: suffix ∧
      TimerDispatch.Selection.Valid ⟨d,j,pid,timer,entry,w⟩ ∧
      TimerDispatch.Selection.Cause roots ⟨d,j,pid,timer,entry,w⟩ :=
  TimerDispatch.scope_entry_cause record d j pid timer entry appends w h roots saved selected carrier

/-- Security: the complete native handshake receiver preserves the provenance
of every live timer occurrence. Actual arms record their cause, deletion retires
the occurrence, and all other callbacks retain its incarnation, expiry and full
wheel entry. The incoming carrier is explicit; driver initialization is separate. -/
theorem original_receiver_transports_timer_inventory (msg : Key) (src : SkbSource) :
    TimerInventory.Preserves (WorkRoot.receive msg src) :=
  TimerInventory.receive_preserves msg src

/-- Security: every timer arm in the combined native receiver journal names
its own earlier authenticated callback, including arms preceding an internal
Stop. This is the actual arm occurrence, not an older admission for the peer. -/
theorem original_combined_receiver_timer_arms_have_authenticated_cause
    (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (pre post : List TimerRoot.Event) (r : TimerRoot.Arm)
    (position : (runWGPrefix (WorkRoot.receive msg src) w a []).2 = pre ++ .armed r :: post) :
    r.Native ∧ WorkRoot.AuthenticatedAt pre r.origin r.kind r.peer :=
  WorkTimer.armed_authenticated msg src w a pre post r position

/-- Security: a timer selected immediately after a completed native receiver
from an empty wheel inherits the exact occurrence's own authenticated arm.
No output carrier is assumed. Transport across intervening driver actions and
fixture-rooted preexisting timers remains a separate initialized obligation. -/
theorem original_receiver_then_timer_inherits_authenticated_occurrence
    (msg : Key) (src : SkbSource) (before : WGWorld) (ambient : Ambient)
    (r : TimerDispatch.Selection) (empty : TimerInventory.NoPending before)
    (received : ((receiveHandshakePacket msg src).run before).run ambient =
      .ok (((),r.before.wg),r.before.ambient)) (selected : r.Valid) :
    ∃ stamp expires arm pre post,
      TimerSlots.Pending r.before.wg r.peer r.timer stamp expires r.entry ∧
      (runWGPrefix (WorkRoot.receive msg src) before ambient []).2 = pre ++ .armed arm :: post ∧
      arm.Native ∧ TimerSlots.Changed arm ∧ arm.peer = r.peer ∧ arm.timer = r.timer ∧
      TimerSlots.Pending arm.run.after r.peer r.timer stamp expires r.entry ∧
      WorkRoot.AuthenticatedAt pre arm.origin arm.kind arm.peer :=
  TimerInventory.receiver_then_selection_authenticated msg src before ambient r empty received selected

/-- Security: the shared driver's actual decrypt preparation preserves the
packet/stamp carrier tying each crypted packet to an earlier successful AEAD
publication. This local contract assumes that carrier on entry; preservation
through the remaining common-driver actions is a separate obligation. -/
theorem shared_prepare_retains_publication (record : TransportDriver.OriginEvent → E)
    (decode : E → Option TransportDriver.OriginEvent)
    (inverse : ∀ event, decode (record event) = some event) :
    PrefixPreserves (fun h w => TransportPublication.Inv (h.filterMap decode) w.wg)
      (fun _ => True) (TransportDriver.prepare record decode) :=
  TransportPublication.prepare_preserves record decode inverse

/-- Security: a packet carried by an actual successful decrypt/publication has
native AEAD evidence for its exact bytes, key slot and nonce, before any later
consume effects. The publication carrier is explicit; this does not assume or
claim that the enclosing shared driver already preserves it. -/
theorem shared_publication_authenticated {id : SkbId}
    (anchor : TransportPublication.Anchor history id pkt w) :
    ∃ pre post, ∃ (r : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
      history = pre ++ .receipt (.decrypt id r) :: post ∧
      PublicationIdentity.Published id r out pid published ambient ∧ pkt = {out with state := .crypted} ∧
      ∃ d k, r.before.dev = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
        d.keypairs[r.value.1.keypair]? = some k ∧ k.receiving.isValid = true ∧
        pkt.keypair = r.value.1.keypair ∧ pkt.nonce = u64le r.value.1.bytes 8 ∧
        aeadDecrypt k.receiving.key (counterNonce pkt.nonce) (r.value.1.bytes.drop 16) [] = some pkt.bytes :=
  anchor.authenticated

/-- Security: the shared native handshake worker preserves actual earlier
handshake authentication for every observed peer callback, including retained
prefixes before a Stop. Its supplied session and keepalive observers preserve
that same history; no hypothesis grants an authentication root to this worker. -/
theorem shared_handshake_callbacks_authenticated
    (session : PeerId → WGPrefix HandshakeCausal.Event Bool)
    (keepalive : PeerId → WGPrefix HandshakeCausal.Event Unit)
    (hs : ∀ pid, HandshakeCausal.Preserves (session pid))
    (hk : ∀ pid, HandshakeCausal.Preserves (keepalive pid)) :
    HandshakeCausal.Preserves (HandshakeWorker.observed id some session keepalive) :=
  HandshakeWorker.HistorySafety.observed_preserves session keepalive hs hk

/-- Security: each indexed native replay receipt in this actual poll is tied
to the selected crypted packet's earlier successful AEAD publication, including
receipts retained before a later Stop. The entry publication carrier and the
consumer/GRO carrier contracts are explicit local obligations; initialized
shared-driver transport is not claimed by this theorem. -/
theorem shared_poll_replay_receipts_authenticated
    (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (inverse : ∀ r, replay (record r) = some r) (quiet : ∀ r, origin (record r) = none)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (receive : GroState → List UInt8 → PrefixM E GroState) (flush : GroState → PrefixM E Unit)
    (hc : ∀ pid pkt ep, TransportReplay.Preserves (origin := origin) (replay := replay) (consume pid pkt ep))
    (hr : ∀ gro bytes, TransportReplay.Preserves (origin := origin) (replay := replay) (receive gro bytes))
    (hf : ∀ gro, TransportReplay.Preserves (origin := origin) (replay := replay) (flush gro))
    (pid : PeerId) (budget : Nat) :
    TransportReplay.Preserves (origin := origin) (replay := replay)
      (IndexedPoll.sourceWith (fun a => liftPrefix (liftWG a)) (TransportDriver.counter record)
        consume receive flush pid budget) :=
  TransportReplay.poll_checked origin replay record inverse quiet consume receive flush hc hr hf pid budget

/-- Security: a certified native replay receipt has its own strictly earlier
authentication publication in the same journal, rather than an unrelated
completed consumer. Safety of that journal is the visible local premise. -/
theorem shared_replay_has_prior_authentication
    (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (history pre post : List E) (event : E)
    (r : TransportDriver.Replay) (safe : TransportReplay.Safe origin replay history)
    (position : history = pre ++ event :: post) (recorded : replay event = some r) :
    TransportReplay.Certified (pre.filterMap origin) r :=
  TransportReplay.replay_authenticated safe position recorded

/-- Security: the actual shared poll supplies confirmation only with its own
immediately preceding successful replay receipt and prior AEAD publication for
the same peer and keypair. This local claim keeps neutral candidate markers,
the concrete confirmation/tail/GRO contracts and its entry carrier explicit. -/
theorem shared_poll_supplies_authenticated_confirmation
    (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (hooks : TransmitSecurity.Driver.Hooks E)
    (inverse : ∀ r, replay (record r) = some r) (quiet : ∀ r, origin (record r) = none)
    (counter : hooks.counterCheck = TransportDriver.counter record)
    (enter : hooks.candidateEnter = fun _ _ => pure 0)
    (leave : hooks.candidateLeave = fun _ => pure ())
    (hc : ∀ pid kid, PrefixEnsures (TransportReplay.ConfirmationInput origin replay record pid kid)
      (TransportReplay.Safe origin replay) (liftWGObserver (hooks.confirmation pid kid))
        (fun _ => TransportReplay.Inv origin replay))
    (ht : ∀ pid pkt value, TransportReplay.Preserves (origin := origin) (replay := replay)
      (liftWGObserver (TransmitSecurity.Driver.receiveTailObserved hooks pid pkt value)))
    (toStack : List (List UInt8) → PrefixM E Unit)
    (hr : ∀ gro bytes, TransportReplay.Preserves (origin := origin) (replay := replay)
      (napiGroReceivePrefix toStack gro bytes))
    (hf : ∀ gro, TransportReplay.Preserves (origin := origin) (replay := replay)
      (napiGroFlushAllPrefix toStack gro))
    (pid : PeerId) (budget : Nat) :
    TransportReplay.Preserves (origin := origin) (replay := replay)
      (TransmitSecurity.Driver.pollObserved hooks pid budget toStack) :=
  TransportReplay.shared_poll_authorized hooks inverse quiet counter enter leave hc ht toStack hr hf pid budget

/-- Security: at that concrete confirmation-entry cut, the journal's last
receipt is a successful native replay check on this peer and keypair, certified
against an earlier successful AEAD publication. This extracts the explicit
caller premise; it does not manufacture initialized provenance. -/
theorem shared_confirmation_entry_has_current_authentication
    (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (record : TransportDriver.Replay → E)
    (input : TransportReplay.ConfirmationInput origin replay record pid kid history w) :
    ∃ pre r, history = pre ++ [record r] ∧ r.packet.peer = pid ∧ r.packet.keypair = kid ∧
      r.run.value = true ∧ TransportReplay.Certified (pre.filterMap origin) r :=
  TransportReplay.confirmation_input_authenticated input

/-- Security: actual UDP admission cannot manufacture a crypted packet's
prior-authentication certificate. Fresh and overwritten ingress slots are
uncrypted or dead; each surviving crypted packet retains its exact publication
anchor and allocation stamp. The entry packet carrier is explicit. -/
theorem original_ingress_retains_packet_authentication (msg : List UInt8) (src : SkbSource)
    (history : List TransportDriver.OriginEvent) :
    Leanux.Proofs.Framing.Preserves (TransportPublication.Inv history) (WG.wgReceive msg src) :=
  TransportPublication.wgReceive_preserves msg src history

/-- Security: the shared staging path retains the RX authentication carrier
and an additional event-order property through its concrete native actions.
Selection, reservation, allocation and creation callback contracts remain
visible; this source composition does not claim initialized driver closure. -/
theorem shared_staging_retains_packet_authentication (extra : List E → Prop)
    (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (hooks : TransmitSecurity.Driver.Hooks E)
    (callbacks : TransportCarrier.StagingSafe extra origin replay hooks) (pid : PeerId) :
    TransportCarrier.StateSafe extra origin replay (TransmitSecurity.Driver.stagingObserved hooks pid) :=
  TransportCarrier.staging callbacks pid

/-- Security: all five actual timer callback paths retain packet-authentication
anchors and the supplied event-order property; they cannot turn an unrelated
RX packet into authenticated material. This local statement retains the shared
staging callback contracts and entry carrier. -/
theorem shared_timers_retain_packet_authentication (extra : List E → Prop)
    (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (hooks : TransmitSecurity.Driver.Hooks E)
    (callbacks : TransportCarrier.StagingSafe extra origin replay hooks) (pid : PeerId) (timer : PeerTimer) :
    TransportCarrier.StateSafe extra origin replay (TransmitSecurity.Driver.timerObserved hooks pid timer) :=
  TransportCarrier.timer callbacks pid timer

/-- Security: real draining workers, copied scheduler trials and NAPI dispatch
retain the same packet-authentication carrier and additional event-order
property. The actual worker callback contracts remain visible; no final-state
or unrelated observer history supplies the missing initialized closure. -/
theorem shared_scheduler_retains_packet_authentication (extra : List E → Prop)
    (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (hooks : TransmitSecurity.Driver.Hooks E)
    (callbacks : TransportCarrier.WorkerSafe extra origin replay hooks) (stack : Option Worker) :
    TransportCarrier.ProductSafe extra origin replay (TransmitSecurity.Driver.scheduleObserved hooks stack) :=
  TransportCarrier.schedule callbacks stack

/-- Security: both actual timer-pass modes preserve authenticated RX packet
origins and the supplied same-history ordering property through callbacks,
queued key clearing and interleaved send/crypt workers. Callback contracts are
explicit; this does not yet assert initialized whole-run causal closure. -/
theorem shared_timer_passes_retain_packet_authentication (extra : List E → Prop)
    (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (hooks : TransmitSecurity.Driver.Hooks E)
    (callbacks : TransportCarrier.DeferredSafe extra origin replay hooks) (j : UInt64) :
    TransportCarrier.ProductSafe extra origin replay (TransmitSecurity.Driver.timersObserved hooks j) ∧
    TransportCarrier.ProductSafe extra origin replay (TransmitSecurity.Driver.placeholderTimersObserved hooks j) :=
  ⟨TransportCarrier.timers callbacks j,TransportCarrier.placeholderTimers callbacks j⟩

/-- Security: an initialized shared-driver run retains certified native replay
receipts and the supplied event-order property through every syscall, worker,
timer mode and indexed Stop. This generic composition exposes all concrete
callback obligations; the Journal specialization remains a separate claim. -/
theorem shared_initialized_authentication_carrier (extra : List E → Prop)
    (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (hooks : TransmitSecurity.Driver.Hooks E)
    (callbacks : TransportCarrier.DeferredSafe extra origin replay hooks)
    (front : ∀ family addr packets mtu, TransportCarrier.StateSafe extra origin replay
      (hooks.front family addr packets mtu))
    (empty : extra []) (trace : Runner.Trace) (placeholders : Bool) :
    TransportReplay.Safe origin replay
      (runPrefixOuter (TransmitSecurity.Driver.executeObserved hooks trace placeholders) []).2 ∧
    extra (runPrefixOuter (TransmitSecurity.Driver.executeObserved hooks trace placeholders) []).2 :=
  TransportCarrier.initialized callbacks front empty trace placeholders

/-- Security: every replay-check receipt in an initialized combined journal
belongs to its actual selected CRYPTED packet and carries a strictly earlier
successful native AEAD publication. Failed outer runs retain the same fact;
there is no callback, packet-validity or initialized-state premise. -/
theorem initialized_replay_has_authenticated_packet (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List TransmitSecurity.Journal.Event) (r : TransportDriver.Replay)
    (position : (runPrefixOuter (TransmitSecurity.Journal.execute trace placeholders) []).2 =
      pre ++ TransmitSecurity.Journal.Event.replay r :: post) :
    TransportReplay.Certified (pre.filterMap TransmitSecurity.Journal.origin?) r :=
  TransportReplay.replay_authenticated (TransportJournal.initialized trace placeholders) position rfl

/-- Security: every native responder-confirmation call observed in the
initialized combined journal follows the immediately preceding successful
replay check for that peer and key, certified by an earlier native AEAD
publication. The result includes receipts before later consumer Stop and
requires no assumed authentication or callback-order contract. -/
theorem initialized_confirmation_has_authenticated_replay (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List TransmitSecurity.Journal.Event) (event : TransmitSecurity.Journal.Event)
    (pid : PeerId) (kid : KeypairId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (TransmitSecurity.Journal.execute trace placeholders) []).2 = pre ++ event :: post)
    (recorded : TransmitSecurity.Journal.responder? event = some (.confirmed pid kid r)) :
    r.Valid (receivedWithKeypair pid kid) ∧
    ∃ earlier counter, pre = earlier ++ [TransmitSecurity.Journal.Event.replay counter] ∧
      counter.packet.peer = pid ∧ counter.packet.keypair = kid ∧ counter.run.value = true ∧
      TransportReplay.Certified (earlier.filterMap TransmitSecurity.Journal.origin?) counter :=
  TransportJournal.confirmation_authenticated trace placeholders pre post event pid kid r position recorded

/-- Security: observing the current causal scope at every timer arm and
handshake queue append preserves the original timer callback's exact result and
Stop. This source bridge does not assume that a missing scope is authorized;
initialized root validity remains a separate obligation. -/
theorem scoped_timer_effects_keep_native_behavior
    (decode : E → Option (CausalScope.Event Cause))
    (recordArm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (recordQueue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (keepalive : PeerId → WGPrefix E Unit)
    (hk : ∀ pid, ErasesStatePrefix (keepalive pid) (sendKeepalive pid))
    (pid : PeerId) (timer : PeerTimer) :
    ErasesStatePrefix
      (TimerEffects.timerWith (CausalEffects.ops decode recordArm recordQueue) keepalive pid timer)
      (timerCallback pid timer) :=
  TimerEffects.timer_erases (CausalEffects.ops_erases decode recordArm recordQueue) keepalive hk pid timer

/-- Security: a causal scope is recorded at its actual full-journal position
before every event of its body, including effects preceding an internal Stop.
This positional source claim does not declare the scope's label authenticated. -/
theorem causal_scope_precedes_internal_effects (record : CausalScope.Event Cause → E)
    (cause : Cause) (body : CausalScope.Token Cause → PrefixM E α)
    (appends : ∀ token, Appends (body token)) (w : World) (h : List E) :
    ∃ suffix, (runPrefix (CausalScope.prefixScope record cause body) w h).2 =
      h ++ record (.entered ⟨h.length,cause⟩) :: suffix :=
  CausalScope.prefix_entry record cause body appends w h

/-- Security: the candidate scope brackets the actual replay check and its
conditional consumer without altering any native branch. Candidate entry is
metadata; only the subsequent successful certified replay authorizes effects. -/
theorem candidate_scope_preserves_original_poll {m : Type → Type} [Monad m] [LawfulMonad m]
    (step : {α : Type} → WG.M α → m α)
    (counter : SkbId → RxPacket → m Bool)
    (consume : PeerId → RxPacket → Endpoint → m (Option (List UInt8)))
    (receive : GroState → List UInt8 → m GroState) (flush : GroState → m Unit)
    (pid : PeerId) (budget : Nat) :
    CandidatePoll.sourceWith step (fun _ _ => pure 0) (fun _ => pure ()) counter consume receive flush pid budget =
      IndexedPoll.sourceWith step counter consume receive flush pid budget :=
  CandidatePoll.neutral step counter consume receive flush pid budget

/-- Security: the same scoped native poll preserves selected-packet AEAD
provenance and immediate successful-replay attribution for confirmation, including
retained Stop prefixes. The marker adds no authentication assumption; the
existing consumer, tail and GRO callback frames remain explicit local premises. -/
theorem scoped_candidate_retains_authenticated_confirmation
    (origin : E → Option TransportDriver.OriginEvent) (replay : E → Option TransportDriver.Replay)
    (record : TransportDriver.Replay → E)
    (replayInverse : ∀ r, replay (record r) = some r) (replayOrigin : ∀ r, origin (record r) = none)
    (responder : HandshakeSecurity.Responder.DriverCuts.Event → E)
    (decode : E → Option HandshakeSecurity.Responder.DriverCuts.Event)
    (inverse : ∀ event, decode (responder event) = some event)
    (quiet : ∀ r, HandshakeSecurity.ConfirmationTransportOrder.Unconfirmed decode (record r))
    (scopeRecord : CausalScope.Event Cause → E) (candidate : SkbId → RxPacket → Cause)
    (scopeOrigin : ∀ event, origin (scopeRecord event) = none)
    (scopeReplay : ∀ event, replay (scopeRecord event) = none)
    (scopeQuiet : ∀ event, HandshakeSecurity.ConfirmationTransportOrder.Unconfirmed decode (scopeRecord event))
    (hooks : TransmitSecurity.Driver.Hooks E)
    (confirmed : hooks.confirmation = HandshakeSecurity.ConfirmationTransportOrder.confirmation responder decode)
    (toStack : List (List UInt8) → PrefixM E Unit)
    (consumeCarrier : ∀ pid pkt ep, TransportReplay.Preserves (origin := origin) (replay := replay)
      (liftWGObserver (TransmitSecurity.Driver.consumeObserved hooks pid pkt ep)))
    (receiveCarrier : ∀ gro bytes, TransportReplay.Preserves (origin := origin) (replay := replay)
      (napiGroReceivePrefix toStack gro bytes))
    (flushCarrier : ∀ gro, TransportReplay.Preserves (origin := origin) (replay := replay)
      (napiGroFlushAllPrefix toStack gro))
    (tailOrder : ∀ pid pkt value, PrefixPreserves (HandshakeSecurity.ConfirmationTransportOrder.Base record decode) (HandshakeSecurity.ConfirmationTransportOrder.Safe record decode)
      (liftWGObserver (TransmitSecurity.Driver.receiveTailObserved hooks pid pkt value)))
    (receiveOrder : ∀ gro bytes, PrefixPreserves (HandshakeSecurity.ConfirmationTransportOrder.Base record decode) (HandshakeSecurity.ConfirmationTransportOrder.Safe record decode)
      (napiGroReceivePrefix toStack gro bytes))
    (flushOrder : ∀ gro, PrefixPreserves (HandshakeSecurity.ConfirmationTransportOrder.Base record decode) (HandshakeSecurity.ConfirmationTransportOrder.Safe record decode)
      (napiGroFlushAllPrefix toStack gro)) (pid : PeerId) (budget : Nat) :
    TransportCarrier.ProductSafe (HandshakeSecurity.ConfirmationTransportOrder.Safe record decode) origin replay
      (CandidatePoll.sourceWith (fun a => liftPrefix (liftWG a))
        (fun skb pkt => CausalScope.enterPrefix scopeRecord (candidate skb pkt))
        (CausalScope.leavePrefix scopeRecord) (TransportDriver.counter record)
        (fun pid pkt ep => liftWGObserver (TransmitSecurity.Driver.consumeObserved hooks pid pkt ep))
        (napiGroReceivePrefix toStack) (napiGroFlushAllPrefix toStack) pid budget) :=
  CandidateCarrier.scoped_shared_poll origin replay record replayInverse replayOrigin
    responder decode inverse quiet scopeRecord candidate scopeOrigin scopeReplay scopeQuiet
    hooks confirmed toStack consumeCarrier receiveCarrier flushCarrier
    tailOrder receiveOrder flushOrder pid budget

/-- Security: exposing the receive-side timer arms and handshake queue appends
preserves the exact native packet-maintenance result and Stop. Causal validity
of the supplied effect context remains an initialized-driver obligation. -/
theorem packet_effects_preserve_original_receive
    (decode : E → Option (CausalScope.Event Cause))
    (recordArm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (recordQueue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (pid : PeerId) (pkt : RxPacket) :
    ErasesStatePrefix
      (PacketEffects.prepareWith (CausalEffects.ops decode recordArm recordQueue) pid pkt)
      (Queues.RxCredits.prepareRest pid pkt) :=
  PacketEffects.prepare_erases (CausalEffects.ops_erases decode recordArm recordQueue) pid pkt

/-- Security: the callback-parametric handshake source is the existing worker
at its original cookie/MAC prefix and accepted suffix. Completed native receipts
can wrap the actual consumers and response creation before a later Stop. -/
theorem handshake_callback_source_keeps_existing_worker
    (record : HandshakeCausal.Event → E) (decode : E → Option HandshakeCausal.Event)
    (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit) :
    HandshakeWorker.observed record decode session keepalive =
      HandshakeWorker.observedWith (HandshakeWorker.observedOps record decode session keepalive) :=
  HandshakeWorker.observed_factor record decode session keepalive

/-- Security: neutral packet-maintenance callbacks are exactly the original
native action lifted once. Source factoring adds no hidden side effect or
journal event, including on a failed receive suffix. -/
theorem native_effect_callbacks_are_transparent (pid : PeerId) (pkt : RxPacket) :
    PacketEffects.prepareWith (TimerEffects.lifted : TimerEffects.Ops (WGPrefix E)) pid pkt =
      liftWGPrefix (Queues.RxCredits.prepareRest pid pkt) :=
  PacketEffects.prepare_lifted pid pkt

/-- Security: packet-maintenance receipts leave the active causal scope
unchanged; each later arm or queue append in that callback reads the same scope.
This frame does not declare the current scope authorized. -/
theorem packet_effects_retain_current_scope
    (decode : E → Option (CausalScope.Event Cause))
    (recordArm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (recordQueue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (ha : ∀ r, decode (recordArm r) = none) (hq : ∀ r, decode (recordQueue r) = none)
    (pid : PeerId) (pkt : RxPacket) :
    StateHistoryFrame decode
      (PacketEffects.prepareWith (CausalEffects.ops decode recordArm recordQueue) pid pkt) :=
  PacketEffects.prepare_frame decode (CausalEffects.ops_frames decode recordArm recordQueue decode ha hq) pid pkt

/-- Security: the effect-parametric TX completion source retains the original
packet reads, socket receipts, lifetime accesses and error paths. This exact
source factor enables causal instrumentation; it does not assert authorization. -/
theorem completion_effect_source_keeps_existing_worker (pid : PeerId) :
    CompletionEffects.stepWith CompletionEffects.native pid = TransmitSecurity.Completion.step pid :=
  CompletionEffects.step_factor pid

/-- Security: causal timer/work receipts preserve the complete original lifetime
journal, including accesses before a Stop. Every other callback and the silent
receipt projection remain explicit; causal authorization is a separate claim. -/
theorem lifetime_effect_receipts_keep_original_accesses
    (ρ : E → Option F) (base : LifetimeEffects.Ops (WGPrefix E))
    (target : LifetimeEffects.Ops (WGPrefix F)) (h : LifetimeEffects.Ops.Projects ρ base target)
    (decode : E → Option (CausalScope.Event Cause))
    (recordArm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (recordQueue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (ha : ∀ r, ρ (recordArm r) = none) (hq : ∀ r, ρ (recordQueue r) = none) (pid : PeerId) :
    StateProjectsPrefix ρ id
      (LifetimeEffects.freshWith (LifetimeEffects.decorate base decode recordArm recordQueue) pid)
      (LifetimeEffects.freshWith target pid) :=
  LifetimeEffects.fresh_projects ρ
    (LifetimeEffects.decorate_projects ρ base target h decode recordArm recordQueue ha hq) pid

end Leanux.Proofs.WG.AuthenticatedEffects
