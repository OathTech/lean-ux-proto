import Leanux.Proofs.WG.Roaming.RemoteChronologyClaims
import Leanux.Proofs.WG.Roaming.HandshakeOverlayClaims
import Leanux.Proofs.WG.Roaming.HandshakeInitializedClaims
import Leanux.Proofs.WG.Roaming.PollAuthenticationCheckClaims
import Leanux.Proofs.WG.Roaming.ReceiveStepRemoteClaims
import Leanux.Proofs.WG.Roaming.ReceiveStepSetterClaims
import Leanux.Proofs.WG.Roaming.HandshakeAttemptClaims
import Leanux.Proofs.WG.Roaming.PollAuthenticationCertificateSource
import Leanux.Proofs.WG.Roaming.RemoteBirthClaims
import Leanux.Proofs.WG.Roaming.RemoteControlClaims
import Leanux.Proofs.WG.Roaming.RemoteSilentClaims
import Leanux.Proofs.WG.Roaming.RemoteProvenanceClaims
import Leanux.Proofs.WG.Roaming.HandshakeRemoteWholeClaims
import Leanux.Proofs.WG.Roaming.ConsumptionDestinationClaims
import Leanux.Proofs.WG.Roaming.RemoteMutationFrames
import Leanux.Proofs.WG.Roaming.ReceiveIngressClaims
import Leanux.Proofs.WG.Roaming.NapiPublicationClaims
import Leanux.Proofs.WG.Roaming.ConsumeEndpointClaims
import Leanux.Proofs.WG.Roaming.CookieEndpointClaims
import Leanux.Proofs.WG.Roaming.InitiationRejectionClaims
import Leanux.Proofs.WG.Roaming.ResponseRejectionClaims
import Leanux.Proofs.WG.Roaming.RateLimitClaims
import Leanux.Proofs.WG.Roaming.InvalidMac1Claims
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Roaming.View
import Leanux.Proofs.WG.Roaming.Authentication
import Leanux.Proofs.WG.Roaming.PublicationClaims
import Leanux.Proofs.WG.Roaming.PollEndpointClaims
import Leanux.Proofs.WG.Roaming.ResponseCallProductClaims
import Leanux.Proofs.WG.Roaming.InitiationCallProductClaims
import Leanux.Proofs.WG.Roaming.HandshakeAuditClaims
import Leanux.Proofs.WG.Roaming.PollAttemptClaims

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Normal source conversion returns the exact endpoint encoded by the
packet's outer source, including the arrival interface for IPv6 link-local scope. -/
theorem original_source_endpoint (src : SkbSource) :
    Campaign2.Ensures (endpointFromSkb src) (fun _ => True)
      (fun result _ => result = some (sourceEndpoint src) ∧
        (src.family = 4 ∨ src.family = 6)) := by
  have h := (ensures_iff _ _ _).mpr (endpointFromSkb_exact src (fun _ => True))
  intro g ambient result final after _ hr
  exact (h g ambient result final after trivial hr).2

/-- With a supported address family, the endpoint setter establishes the
requested remote destination, even when endpoint_eq avoids a redundant write. -/
theorem original_set_endpoint (pid : PeerId) (e : Endpoint)
    (valid : e.family = AF_INET ∨ e.family = AF_INET6) :
    Campaign2.Ensures (setPeerEndpoint pid e) (fun _ => True)
      (fun _ w => remoteAt w pid = some (destination e)) :=
  setPeerEndpoint_destination pid e valid

/-- Clearing cached local source addresses does not roam the peer. -/
theorem original_clear_source_preserves_destination (pid : PeerId)
    (remote : Option (Nat × Nat × Nat × Nat)) :
    Campaign2.Ensures (clearPeerEndpointSrc pid) (fun w => remoteAt w pid = remote)
      (fun _ w => remoteAt w pid = remote) :=
  clearPeerEndpointSrc_destination pid remote

/-- On normal completion, the packet endpoint setter chooses that packet's
remote source. Its caller's authentication obligation is not assumed proved here. -/
theorem original_packet_source_destination (pid : PeerId) (src : SkbSource) :
    Campaign2.Ensures (setPeerEndpointFromSkb pid src) (fun _ => True)
      (fun _ w => remoteAt w pid = some (destination (sourceEndpoint src))) :=
  setPeerEndpointFromSkb_destination pid src

/-- Successful data decryption uses the resident receiving key, preserves
the source and ownership, and returns exactly the AEAD plaintext. The empty
associated data does not bind the outer source address cryptographically. -/
theorem original_decryption_authentication (pkt : RxPacket) (key : Keypair) :
    Campaign2.Ensures (decryptPacket pkt)
      (fun w => (w.wg.device.bind fun d => d.keypairs[pkt.keypair]?) = some key)
      (fun result _ => ∀ plain, result = some plain →
        plain.source = pkt.source ∧ plain.peer = pkt.peer ∧ plain.keypair = pkt.keypair ∧
        plain.nonce = u64le pkt.bytes 8 ∧
        aeadDecrypt key.receiving.key (counterNonce (u64le pkt.bytes 8))
          (pkt.bytes.drop 16) [] = some plain.bytes) :=
  decryptPacket_authenticated pkt key

/-- Every normal original decrypt step has its exact prefix observation.
If it consumed a packet, the pre-irqExit publication is CRYPTED only with
the AEAD plaintext under the key read after the initial softirq. For a
CRYPTED publication, the outer source, packet peer and keypair are preserved,
and the nonce equals the decoded counter at that cut.
Both callbacks are arbitrary and execute in the original order; no final
packet residency, peer/owner equality, endpoint effect or runner coverage is
claimed. Discarding the observation is exactly the original decryptStep,
including errors, by observedDecryptStep_erase. -/
theorem original_decrypt_publication_authentication (softirq irqExit : Leanux.M Unit) :
    Campaign2.Product.Ensures (observedDecryptStep softirq irqExit) (fun _ => True)
      (fun result _ => PublicationObservation result) :=
  observedDecryptStep_authenticated softirq irqExit

/-- A normal original poll has its actual budget-guarded first-prefix
observation. If that first iteration reaches the endpoint setter, its packet
was resident at poll entry, its peer field equals the poll peer, it is CRYPTED,
and the original
counter check returned true. Its supported outer source determines the
immediate destination. Later GRO, release and stack callbacks remain in the
original execution; no final endpoint preservation is claimed. Discarding the
observation is exactly rxPoll, including errors, by observedRxPoll_erase. -/
theorem original_poll_first_endpoint (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (observedRxPoll pid budget toStack) (fun s => s = entry)
      (fun result _ => PollEndpointObservation pid budget entry result) :=
  observedRxPoll_facts pid budget toStack entry

/-- On normal return of the original decryptStep whose irqExit callback is this rxPoll, the
publication and first-poll endpoint cuts belong to the same execution. When
the actual first endpoint packet id equals the just-published id, it carries
the AEAD plaintext under the historical key read during decryption, with the
source, peer, keypair and decoded counter preserved. Softirq and stack
callbacks remain arbitrary. This is a conditional packet-identity join, not
a queue-store invariant or Env.napiIrqExit coverage theorem; it says nothing
about inner delivery or the endpoint after later callbacks. The exact original
operation, including errors, is recovered by observedDecryptPoll_erase. -/
theorem original_publication_poll_endpoint (softirq : Leanux.M Unit) (pid : PeerId)
    (budget : Nat) (toStack : List (List UInt8) → Leanux.M Unit) :
    Campaign2.Product.Ensures (observedDecryptPoll softirq pid budget toStack) (fun _ => True)
      (fun result _ => PublicationPollObservation pid budget result) :=
  observedDecryptPoll_authenticated softirq pid budget toStack

/-- For response-kind packets, the complete original handshake caller factors
at the actual endpoint setter: no cut takes a pure suffix, while a present cut
immediately invokes the setter and retains the full original continuation.
The returned observation is exactly that same prefix/suffix execution's cut.
On normal full completion the cut records actual MAC admission, same-entry
index lookup with separately recorded owner/reference identities, both DH checks, the
specified derived AEAD key/AAD and successful empty plaintext, and the consumer's
state recheck/commit. The outer packet source is not an AEAD input. No final
endpoint preservation, initiation coverage or failed-full-call prefix completeness
is asserted. Observation erasure is unconditional, including errors, by
observedResponseHandshake_erase. -/
theorem original_response_endpoint_authentication (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Product.AgreesOn (fun _ => True) (liftWG (receiveHandshakePacket msg src))
      (Product.responseCallPrefix msg src >>= Product.responseCallSuffix msg src) ∧
    Campaign2.Product.AgreesOn (fun _ => True) (Product.observedResponseHandshake msg src)
      (Product.responseCallTranscript msg src) ∧
    Campaign2.Product.Ensures (Product.observedResponseHandshake msg src) (fun _ => True)
      (fun observed _ => Product.ResponseCallObservation msg observed) := by
  constructor
  · intro w pre
    rw [Product.receiveHandshakePacket_response msg src kind]
  · constructor
    · intro w pre
      rw [Product.observedResponseHandshake_source msg src kind]
    · exact Product.observedResponseHandshake_facts msg src kind

/-- For initiation-kind packets, the complete original caller factors at its
actual endpoint setter. A missing cut takes a pure suffix; a present cut starts
the original setter and retains response sending and the common continuation.
The observation is exactly that same prefix/suffix execution's cut. On normal
full completion, a present cut records actual MAC admission, both AEAD plaintexts
under the specified derived keys/AAD, the public-key table's first matching
lookup and acquired reference, the supplying peer reads, the memcmp replay check, signed wrapping
flood/consumption checks, and commit. No equality between the decrypted
static key and the resident peer's remoteStatic, fixed plaintext length, final
endpoint preservation or failed-full-call prefix retention is asserted. The
outer source is an argument to the actual setter, not an AEAD input. Discarding
the observation is unconditionally the original caller, including errors, by
observedInitiationHandshake_erase. -/
theorem original_initiation_endpoint_authentication (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    Campaign2.Product.AgreesOn (fun _ => True) (liftWG (receiveHandshakePacket msg src))
      (Product.initiationCallPrefix msg src >>= Product.initiationCallSuffix msg src) ∧
    Campaign2.Product.AgreesOn (fun _ => True) (Product.observedInitiationHandshake msg src)
      (Product.initiationCallTranscript msg src) ∧
    Campaign2.Product.Ensures (Product.observedInitiationHandshake msg src) (fun _ => True)
      (fun observed _ => Product.InitiationCallObservation msg observed) := by
  constructor
  · intro w pre
    rw [Product.receiveHandshakePacket_initiation msg src kind]
  · constructor
    · intro w pre
      rw [Product.observedInitiationHandshake_source msg src kind]
    · exact Product.observedInitiationHandshake_facts msg src kind

/-- Inspect the original initiation caller, retaining its actual authenticated
prefix even if the setter or later continuation errors. The two projections
are exactly the actual prefix inspection and complete original-call inspection.
The audit always returns at its unchanged entry. Prefix failure retains that
same original error; a normal no-cut prefix completes without the setter;
a present cut retains the existing authentication facts regardless of the full
call's outcome. This is total inspection, not original-call success, successful
endpoint mutation, or final endpoint preservation. The exact source factor
already ties a present cut to immediate original setter invocation. -/
theorem original_initiation_retained_authentication (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let audited ← Product.initiationHandshakeAudit msg src; pure audited.1)
      (Campaign2.Product.inspect (Product.initiationCallPrefix msg src)) ∧
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let audited ← Product.initiationHandshakeAudit msg src; pure audited.2)
      (Campaign2.Product.inspect (liftWG (receiveHandshakePacket msg src))) ∧
    Campaign2.Product.Observes (Product.initiationHandshakeAudit msg src) (fun _ => True)
      (fun entry observed => ∃ audited, observed = .ok (audited, entry) ∧
        HandshakeAuditFacts
          (fun cut atCut => cut.beforeSetter = atCut ∧ Product.InitiationCallFacts msg cut) audited) := by
  constructor
  · intro w pre
    rw [Product.initiationHandshakeAudit, Product.handshakeAudit_prefix]
  · constructor
    · intro w pre
      rw [Product.initiationHandshakeAudit_original msg src kind]
    · exact Product.initiationHandshakeAudit_facts msg src

/-- The response caller has the same failure-retaining inspection: exact
prefix and original-call outcomes, unchanged inspection entry, and the actual
authentication cut even if its original continuation fails. Error outcomes
carry no final state. A cut certifies reaching the setter, not completing its
write or preserving the endpoint afterwards; no receiver totality is claimed. -/
theorem original_response_retained_authentication (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let audited ← Product.responseHandshakeAudit msg src; pure audited.1)
      (Campaign2.Product.inspect (Product.responseCallPrefix msg src)) ∧
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let audited ← Product.responseHandshakeAudit msg src; pure audited.2)
      (Campaign2.Product.inspect (liftWG (receiveHandshakePacket msg src))) ∧
    Campaign2.Product.Observes (Product.responseHandshakeAudit msg src) (fun _ => True)
      (fun entry observed => ∃ audited, observed = .ok (audited, entry) ∧
        HandshakeAuditFacts
          (fun cut atCut => cut.beforeSetter = atCut ∧ Product.ResponseCallFacts msg cut) audited) := by
  constructor
  · intro w pre
    rw [Product.responseHandshakeAudit, Product.handshakeAudit_prefix]
  · constructor
    · intro w pre
      rw [Product.responseHandshakeAudit_original msg src kind]
    · exact Product.responseHandshakeAudit_facts msg src

/-- Inspect every attempted iteration of the original poll, retaining the
actual per-iteration entry, admission outcome and continuation outcome even
when either phase fails. Erasure is the complete original poll inspection,
including its budget test, callbacks and completion. Every reached designated
consumeDataDone endpoint-setter site has a resident packet at that iteration's
entry, matching peer, CRYPTED state, actual true counter-check result, and the
endpoint converted from that packet's supported outer source. Its cut precedes
the setter and survives a setter/cache-reset or later continuation failure.
The audit loop's head equation records each attempted iteration, including
failures; it never substitutes an empty event list for a reached setter.
This covers that original setter site only: arbitrary callback endpoint writes
are not classified. CRYPTED/counter admission is not independent AEAD provenance,
and an attempt asserts neither successful mutation, final endpoint preservation,
original-call completion nor delivery. -/
theorem original_poll_all_endpoint_attempts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let audit ← observedPollAttempts pid budget toStack; pure audit.outcome)
      (Campaign2.Product.inspect (rxPoll pid budget toStack)) ∧
    Campaign2.Product.Observes (observedPollAttempts pid budget toStack) (fun _ => True)
      (fun entry observed => ∃ audit, observed = .ok (audit, entry) ∧
        ∀ iteration ∈ audit.iterations, PollAttemptIterationFacts pid iteration) := by
  constructor
  · intro entry pre
    rw [observedPollAttempts_erase]
  · exact observedPollAttempts_facts pid budget toStack

/-- The complete original non-cookie receiver preserves the Device and all
remote destinations when the entry MAC1 comparison is invalid. -/
theorem original_invalid_mac1_preserves_endpoints (msg : List UInt8) (src : SkbSource)
    (before : Campaign2.Snapshot)
    (noncookie : messageType msg ≠ MESSAGE_HANDSHAKE_COOKIE)
    (invalid : ∀ d, before.wg.device = some d →
      blake2s 16 d.mac1Key (msg.take (msg.length - 32)) ≠
        (msg.drop (msg.length - 32)).take 16) :
    Campaign2.Ensures (receiveHandshakePacket msg src) (fun s => s = before)
      (fun _ after => after.wg.device = before.wg.device ∧
        ∀ pid, remoteAt after pid = remoteAt before pid) :=
  receiveHandshakePacket_invalid_mac1 msg src before noncookie invalid


/-- Whole non-cookie receive: an actual rate-limit refusal leaves the complete
peer map and every remote destination unchanged on normal completion. Other
MAC outcomes, including noCookie, carry no preservation conclusion here. -/
theorem original_ratelimited_preserves_endpoints (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Product.Snapshot)
    (noncookie : messageType msg ≠ MESSAGE_HANDSHAKE_COOKIE) :
    Campaign2.Product.Ensures (observedRateLimitHandshake msg src) (fun s => s = entry)
      (fun result final => RateLimitRejectionObservation entry result.1 final) :=
  receiveHandshakePacket_ratelimited msg src entry noncookie

/-- A normal response-kind receiver preserves every remote endpoint when its
same-entry receipts show MAC admission and no response-consumer result. The
original receiver, including every error, is retained by observation erasure;
cookie-reply drops are not classified as admitted consumer rejections. -/
theorem original_response_rejection_preserves_endpoints (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Product.Snapshot)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Product.Ensures (observedResponseRejection msg src) (fun s => s = entry)
      (fun receipt final => ResponseRejectionObservation entry receipt final) :=
  receiveHandshakePacket_response_rejection msg src entry kind

/-- A normal initiation-kind receiver preserves every remote endpoint when its
same-entry receipts show MAC admission and no initiation-consumer result. The
original receiver, including every error, is retained by observation erasure;
cookie-reply drops are not classified as admitted consumer rejections. -/
theorem original_initiation_rejection_preserves_endpoints (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Product.Snapshot)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    Campaign2.Product.Ensures (observedInitiationRejection msg src) (fun s => s = entry)
      (fun receipt final => InitiationRejectionObservation entry receipt final) :=
  receiveHandshakePacket_initiation_rejection msg src entry kind

/-- Every normal original type-3 handshake-receive call preserves all remote
endpoints, including valid-cookie updates and lookup/decryption refusals.
Stops remain actual Stops; this neither asserts totality nor a post-error state. -/
theorem original_cookie_message_endpoints (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Product.Snapshot)
    (kind : messageType msg = MESSAGE_HANDSHAKE_COOKIE) :
    Campaign2.Product.Ensures (liftWG (receiveHandshakePacket msg src)) (fun s => s = entry)
      (fun _ final => ∀ pid, remoteAt final.toSnapshot pid = remoteAt entry.toSnapshot pid) :=
  receiveHandshakePacket_cookie_endpoints msg src entry kind

/-- The original data admission/enqueue/cleanup call preserves every optional
peer endpoint, hence every remote destination, on normal return. Later decrypt
workers and NAPI callbacks are outside this call. All initial states remain. -/
theorem original_consume_data_endpoints (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (consumeData msg src ds) (fun s => s = entry)
      (fun _ final => responseEndpointMap final.wg.device = responseEndpointMap entry.wg.device ∧
        ∀ pid, remoteAt final pid = remoteAt entry pid) :=
  consumeData_preserves_endpoints msg src ds entry

/-- On normal return of the actual native decrypt step with Env.napiSoftirq
and Env.napiIrqExit, any observed first pre-put setter selects the published
owner. If that owner's actual publication queue head is the published packet,
the selected packet identity is derived and carries its actual earlier AEAD
plaintext. Skipped polls and every original failure remain; no final endpoint,
other poll iterations, or persistent queue authentication invariant is claimed. -/
theorem original_native_napi_publication_authentication :
    Campaign2.Product.Ensures observedNativeDecryptFirstPoll (fun _ => True)
      (fun result _ => NativePublicationOwnerObservation result) :=
  observedNativeDecryptFirstPoll_authenticated

/-- Whole UDP admission, before asynchronous worker dispatch, preserves every
optional endpoint and remote destination on normal return. No readiness/authentication premise. -/
theorem original_receive_ingress_endpoints (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (wgReceive msg src) (fun s => s = entry)
      (fun _ final => responseEndpointMap final.wg.device = responseEndpointMap entry.wg.device ∧
        ∀ pid, remoteAt final pid = remoteAt entry pid) :=
  wgReceive_preserves_endpoints msg src entry



/-- Every message kind follows the complete original handshake caller.
Erasing its observation preserves the exact original outcome, including Stops.
Normal initiation/response returns retain their actual authentication receipt
and the selected packet-source update through the full suffix; no-cut, cookie
and other normal returns preserve the whole remote map. Surviving destinations
are covered, without a peer-survival or stopped-internal-write claim. -/
theorem original_whole_handshake_remote_coverage (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← Product.observedHandshakeRemotes msg src; pure ())
      (liftWG (receiveHandshakePacket msg src)) ∧
    Campaign2.Product.Ensures (Product.observedHandshakeRemotes msg src) (fun s => s = entry)
      (fun receipt final => Product.HandshakeFinalRemotes msg src entry receipt final) := by
  constructor
  · intro w pre
    rw [Product.observedHandshakeRemotes_erase]
  · exact Product.observedHandshakeRemotes_facts msg src entry

/-- All completed initialized data consumptions, in exact history order, have
strictly earlier AEAD provenance and the packet-source destination retained
through their own full calls. Nondelivery and completed calls before a later
outer Stop are included. Failed consume prefixes, peer survival, persistence
beyond the consume and AEAD authentication of the outer source are not asserted. -/
theorem original_initialized_data_consumptions_authenticated_final
    (trace : Runner.Trace) (placeholders : Bool) :
    ∃ qs,
      Noise.ConfirmationOrder.observations trace placeholders = .ok qs ∧
      qs.Pairwise (fun a b => a.position < b.position) ∧
      qs.length = Noise.ConfirmationOrder.consumedCount
        (Noise.ConfirmationOrder.history trace placeholders) ∧
      (∀ q, q ∈ qs ↔ Noise.ConfirmationOrder.OccursAt trace placeholders q) ∧
      ∀ q ∈ qs, ∃ e : ConsumptionAuthentication,
        e.Valid trace placeholders q ∧ e.Facts q ∧ ConsumptionFinalRemotes q :=
  initialized_consumptions_authenticated_final trace placeholders

/-- A raw native consume with a supported endpoint retains the selected
destination update through the complete original continuation. This local
contract supplies no upstream authentication or peer-survival guarantee. -/
theorem original_completed_data_remote_coverage (entry : Campaign2.Snapshot)
    (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (valid : endpoint.family = AF_INET ∨ endpoint.family = AF_INET6) :
    Campaign2.Ensures (consumeDataDone pid pkt endpoint)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => RemoteRetained (updateRemote (remoteMap entry) pid (destination endpoint))
        (remoteMap s)) :=
  consumeDataDone_final_remotes entry pid pkt endpoint valid

/-- Clearing one peer's cached local addresses preserves all remote
destinations on normal return, including every other peer. -/
theorem original_clear_source_preserves_all_destinations (pid : PeerId)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (clearPeerEndpointSrc pid) (fun s => remoteMap s = remoteMap entry)
      (fun _ s => remoteMap s = remoteMap entry) := by
  intro g ambient result final after pre run
  exact ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (RemoteMutation.clear_source_destinations pid) g ambient result final after run).trans pre


/-- The actual receive worker derives its selected queue message, complete
handshake-call observation and final surviving remote destinations.
Authentication is derived for each selected roaming cause.
An empty queue returns false with the remote map unchanged. -/
theorem original_receive_step_remote_coverage (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (liftWG receiveStep) (fun s => s = entry)
      (fun value final => ∃ q : ReceiveStepRemote.Observation,
        q.Valid ∧ q.entry = entry ∧ q.finish = final ∧ q.value = value ∧ q.Facts) :=
  ReceiveStepRemote.receiveStep_observation entry

/-- Peer creation stamps the allocation and clears exactly its returned store
location's endpoint. Refusal preserves both maps. No initial freshness or
identity continuity through a cursor overwrite is assumed. -/
theorem original_peer_creation_remote_effect (key : Key) (psk : Option Key)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (peerCreate key psk) (fun s => s = entry)
      (fun result after => RemoteBirth.BirthRemoteEffect ⟨key,psk,entry,result,after⟩) :=
  RemoteBirth.peerCreate_effect key psk entry

/-- Every normal setter has the exact conditional map effect: supported
families install the requested destination, and other families preserve it. -/
theorem original_arbitrary_set_endpoint_remote_effect (entry : Campaign2.Snapshot)
    (pid : PeerId) (endpoint : Endpoint) :
    Campaign2.Ensures (setPeerEndpoint pid endpoint)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => remoteMap s = RemoteControl.setterRemotes (remoteMap entry) pid endpoint) :=
  RemoteControl.setPeerEndpoint_effect entry pid endpoint

/-- A completed native consume retains the setter's exact conditional map
through its complete suffix for every endpoint family. This is a local source
contract; initialized authentication comes from the actual poll history. -/
theorem original_arbitrary_data_remote_coverage (entry : Campaign2.Snapshot)
    (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Campaign2.Ensures (consumeDataDone pid pkt endpoint)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => RemoteRetained
        (RemoteControl.setterRemotes (remoteMap entry) pid endpoint) (remoteMap s)) :=
  RemoteControl.consumeDataDone_effect entry pid pkt endpoint

/-- Every timer callback retains each surviving remote destination on normal
return. Peer deletion and clearing of a cached local address are allowed. -/
theorem original_timer_callback_remote_retention (entry : Campaign2.Snapshot)
    (pid : PeerId) (timer : PeerTimer) :
    Campaign2.Ensures (timerCallback pid timer)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => RemoteRetained (remoteMap entry) (remoteMap s)) :=
  timerCallback_retains_remotes entry pid timer

/-- The complete zero-key worker introduces no remote destination, including
the final peer release that can delete its caller. -/
theorem original_clear_worker_remote_retention (entry : Campaign2.Snapshot) (pid : PeerId) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => RemoteRetained (remoteMap entry) (remoteMap s)) :=
  clearWorker_retains_remotes entry pid

/-- The complete outgoing handshake worker retains every surviving remote
destination through its socket, timer and final release operations. -/
theorem original_send_worker_remote_retention (entry : Campaign2.Snapshot) (pid : PeerId) :
    Campaign2.Ensures (handshakeSendWorker pid)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => RemoteRetained (remoteMap entry) (remoteMap s)) :=
  sendWorker_retains_remotes entry pid

/-- Actual transmit completion retains all surviving remote destinations,
including its key-freshness and queued-handshake continuation. -/
theorem original_tx_completion_remote_retention (entry : Campaign2.Snapshot)
    (pid : PeerId) (item : List SkbId) :
    Campaign2.Ensures (createDataDone pid item)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => RemoteRetained (remoteMap entry) (remoteMap s)) :=
  dataCompletion_retains_remotes entry pid item

/-- Every present final destination of the original initialized run has an
actual completed configuration-set, authenticated handshake, or authenticated
data-consumption origin in that same run. The source address is the selected
packet's outer source; no cryptographic binding of that outer address or
physical-write trace for stopped callbacks is asserted. -/
theorem original_initialized_final_endpoint_origins (trace : Runner.Trace)
    (placeholders : Bool) (json : Lean.Json) (final : Campaign2.Snapshot)
    (completed : RemoteProvenance.outcome trace placeholders = .ok (json,final)) :
    ∀ pid remote, remoteMap final pid = some remote →
      ∃ origin : RemoteProvenance.Origin,
        RemoteProvenance.Occurs trace placeholders origin ∧ origin.Facts pid remote :=
  RemoteProvenance.final_origins trace placeholders json final completed

/-- The final-state projection preserves the original initialized JSON outcome
and exact indexed Stop for both recorded-input modes. -/
theorem original_initialized_endpoint_outcome (trace : Runner.Trace) (placeholders : Bool) :
    (RemoteProvenance.outcome trace placeholders).map Prod.fst =
      Runner.executeTrace trace placeholders :=
  RemoteProvenance.outcome_json trace placeholders


/-- A completed receive worker selects at most one authenticated handshake
setter. The selected setter remains explicit when the remote value was
already equal; each surviving final destination has its exact map effect. -/
theorem original_receive_step_single_setter (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (liftWG receiveStep) (fun s => s = entry)
      (fun value final => ∃ q : ReceiveStepRemote.Observation,
        q.Valid ∧ q.entry = entry ∧ q.finish = final ∧ q.value = value ∧ q.Facts ∧
        RemoteRetained (ReceiveStepRemote.setterMap (remoteMap entry.toSnapshot) q.setter)
          (remoteMap final.toSnapshot) ∧
        ∀ pid remote, q.setter = some (pid,remote) → q.Cause pid remote) :=
  ReceiveStepRemote.receiveStep_setter entry

/-- The exact initiation caller records authenticated source-derived setter
attempts before invoking the setter, retaining them if the setter or later
suffix stops. The inspection preserves the original success or failure. -/
theorem original_initiation_setter_attempts (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) :
    (do let audited ← HandshakeAttempts.observeInitiation msg src; pure audited.outcome) =
      Campaign2.inspect (receiveHandshakePacket msg src) ∧
    Campaign2.Observes (HandshakeAttempts.observeInitiation msg src) (fun _ => True)
      (fun entry result => ∃ audit, result = .ok (audit,entry) ∧
        ∀ attempt ∈ audit.attempts, HandshakeAttempts.InitiationFacts msg src attempt) :=
  ⟨HandshakeAttempts.initiation_original msg src kind,HandshakeAttempts.initiation_facts msg src⟩

/-- The exact response caller records authenticated source-derived setter
attempts before invoking the setter, including attempts whose later
continuation stops, while preserving the original outcome. -/
theorem original_response_setter_attempts (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    (do let audited ← HandshakeAttempts.observeResponse msg src; pure audited.outcome) =
      Campaign2.inspect (receiveHandshakePacket msg src) ∧
    Campaign2.Observes (HandshakeAttempts.observeResponse msg src) (fun _ => True)
      (fun entry result => ∃ audit, result = .ok (audit,entry) ∧
        ∀ attempt ∈ audit.attempts, HandshakeAttempts.ResponseFacts msg src attempt) :=
  ⟨HandshakeAttempts.response_original msg src kind,HandshakeAttempts.response_facts msg src⟩


/-- Every surviving final destination is supplied by its actual latest
configuration, authenticated handshake or authenticated data setter in the
initialized driver journal. No later setter or allocation reset affects that
store location. Deletion remains allowed; stopped runs have no final state. -/
theorem original_initialized_latest_endpoint_origins (trace : Runner.Trace)
    (placeholders : Bool) (json : Lean.Json) (final : Campaign2.Snapshot)
    (completed : RemoteProvenance.outcome trace placeholders = .ok (json,final)) :
    ∀ pid remote, remoteMap final pid = some remote →
      ∃ q : RemoteChronology.LatestOrigin,
        q.Valid trace placeholders pid remote ∧ q.origin.Facts pid remote :=
  RemoteChronology.final_latest_origins trace placeholders json final completed

/-- Every reached data endpoint check in the original initialized execution
has an earlier successful decrypt and configured session certificate, even
when its consumption or enclosing runner later stops. -/
theorem original_initialized_data_check_authentication (trace : Runner.Trace)
    (placeholders : Bool) :
    ∀ q ∈ (PollAuthentication.inspection trace placeholders).checks,
      ∃ e : PollAuthentication.Authentication,
        e.Valid trace placeholders q ∧ e.Facts q :=
  PollAuthentication.inspection_authenticated trace placeholders

/-- The projected data inspection preserves the original JSON or indexed
Stop and includes exactly the checks reached at their original positions. -/
theorem original_initialized_data_check_coverage (trace : Runner.Trace)
    (placeholders : Bool) :
    (PollAuthentication.inspection trace placeholders).outcome =
      Runner.executeTrace trace placeholders ∧
    ∀ q, q ∈ (PollAuthentication.inspection trace placeholders).checks ↔
      q.Occurs trace placeholders :=
  ⟨PollAuthentication.inspection_outcome trace placeholders,
    PollAuthentication.inspection_complete trace placeholders⟩

/-- The actual ring-selected handshake receive step retains authenticated
source-derived setter attempts through any later Stop. Its inspection keeps
the exact original outcome; no completed setter or physical write is assumed. -/
theorem original_receive_step_attempt_authentication :
    (do let audit ← HandshakeOverlay.observeStep; pure audit.outcome) =
      Campaign2.Product.inspect (liftWG receiveStep) ∧
    Campaign2.Product.Observes HandshakeOverlay.observeStep (fun _ => True)
      (fun entry result => ∃ audit, result = .ok (audit,entry) ∧
        ∀ attempt ∈ audit.attempts, HandshakeOverlay.Authenticated attempt) :=
  ⟨HandshakeOverlay.step_original,HandshakeOverlay.step_facts⟩

/-- Every handshake setter attempt recorded by the original committed
scheduler callbacks has authentication tied to its actual setter peer state,
including prefixes before later Stops. Copied consistency probes remain in
the original RX projection and do not contribute attempt records here. -/
theorem original_scheduler_attempt_authentication (stack : Option Worker) :
    (do let audit ← HandshakeOverlay.observeSchedule stack; pure audit.outcome) =
      Campaign2.Product.inspect (Env.schedule stack) ∧
    Campaign2.Product.Observes (HandshakeOverlay.observeSchedule stack) (fun _ => True)
      (fun entry result => ∃ audit, result = .ok (audit,entry) ∧
        ∀ attempt ∈ audit.attempts, HandshakeOverlay.Authenticated attempt) :=
  ⟨HandshakeOverlay.schedule_original stack,HandshakeOverlay.schedule_facts stack⟩

/-- Every committed handshake setter attempt in the original initialized
execution has successful MAC/consumer authentication and the selected source
endpoint, tied to the actual setter-entry peer state, including before later
indexed Stops. No callback or invariant premise is supplied. -/
theorem original_initialized_handshake_attempt_authentication (trace : Runner.Trace)
    (placeholders : Bool) :
    ∀ q ∈ (HandshakeOverlay.initializedInspection trace placeholders).attempts,
      HandshakeOverlay.Authenticated q.attempt :=
  HandshakeOverlay.initialized_authentication trace placeholders

/-- The concrete initialized handshake observer retains the original JSON or
indexed Stop and exactly its emitted attempts at their actual positions.
Copied consistency trials remain separate from this committed history. -/
theorem original_initialized_handshake_attempt_coverage (trace : Runner.Trace)
    (placeholders : Bool) :
    (HandshakeOverlay.initializedInspection trace placeholders).outcome =
      Runner.executeTrace trace placeholders ∧
    ∀ q, q ∈ (HandshakeOverlay.initializedInspection trace placeholders).attempts ↔
      q.Occurs trace placeholders :=
  HandshakeOverlay.initialized_coverage trace placeholders

end Leanux.Proofs.WG.Roaming
