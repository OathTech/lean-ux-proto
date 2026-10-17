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

end Leanux.Proofs.WG.Roaming
