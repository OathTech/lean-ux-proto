import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceAllowedIps

namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem pubkey (key : Key) : Framing.Preserves Inv (pubkeyLookup key) := public_lookup key

theorem expire (pid : PeerId) :
    Framing.Preserves Inv (expireCurrentPeerKeypairs pid) := by
  let P := Inv
  have invalid (kid : KeypairId) : Framing.Preserves P (do
      let key ← getKeypair kid
      setKeypair kid {key with sending := {key.sending with isValid := false}}) :=
    preserves_bind (read_key kid) (fun key => write_key kid _)
  have cleared := clear pid
  have reset := reset_sent pid
  have read := read_peer pid
  have effect {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  change Framing.Preserves P _
  routing_tx_source [expireCurrentPeerKeypairs,requireNotPending,branch,invariant]
    using [invalid,cleared,reset,read,effect]

theorem port (port : Nat) :
    Framing.Preserves Inv (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _)
    | (rx_retention_head socketInit; exact socket (socketInit_sameSocket _))
    | peer_reference_traffic_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
