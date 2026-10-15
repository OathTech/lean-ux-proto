import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Roaming.View
import Leanux.Proofs.WG.Roaming.Authentication
import Leanux.Proofs.WG.Roaming.PublicationClaims

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

end Leanux.Proofs.WG.Roaming
