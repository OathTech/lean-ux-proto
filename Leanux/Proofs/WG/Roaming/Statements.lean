import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Roaming.View
import Leanux.Proofs.WG.Roaming.Authentication
import Leanux.Proofs.WG.Roaming.PublicationClaims
import Leanux.Proofs.WG.Roaming.PollEndpointClaims

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Normal source conversion returns the exact endpoint encoded by the
packet's outer source, including the arrival interface for IPv6 link-local scope. -/
theorem original_source_endpoint (src : SkbSource) :
    Campaign2.Ensures (endpointFromSkb src) (fun _ => True)
      (fun result _ => result = some (sourceEndpoint src) ∧
        (src.family = 4 ∨ src.family = 6)) := by
  have h := (ensures_iff _ _ _).mpr (endpointFromSkb_exact src (fun _ => True))
  intro w result w' _ hr
  exact (h w result w' trivial hr).2

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
theorem original_decrypt_publication_authentication (softirq irqExit : M Unit) :
    Campaign2.Ensures (observedDecryptStep softirq irqExit) (fun _ => True)
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
    (toStack : List (List UInt8) → M Unit) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observedRxPoll pid budget toStack) (fun s => s = entry)
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
theorem original_publication_poll_endpoint (softirq : M Unit) (pid : PeerId)
    (budget : Nat) (toStack : List (List UInt8) → M Unit) :
    Campaign2.Ensures (observedDecryptPoll softirq pid budget toStack) (fun _ => True)
      (fun result _ => PublicationPollObservation pid budget result) :=
  observedDecryptPoll_authenticated softirq pid budget toStack

end Leanux.Proofs.WG.Roaming
