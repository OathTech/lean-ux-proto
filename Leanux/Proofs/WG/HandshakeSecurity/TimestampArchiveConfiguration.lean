import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveAllowedIps

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem pubkey (key : Key) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (pubkeyLookup key) := by
  apply frame history _ ?_ (PeerCounter.lookup key)
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact hi.trans ((pubkeyLookup_retains_handshake key w v a b result run).freshness)

theorem expire (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (expireCurrentPeerKeypairs pid) := by
  let P := StateInv history
  have invalid (kid : KeypairId) : Framing.Preserves P (do
      let key ← getKeypair kid
      setKeypair kid {key with sending := {key.sending with isValid := false}}) :=
    preserves_bind (read_key kid history) (fun key => write_key kid _ history)
  have cleared := clear pid history
  have reset := reset_sent pid history
  have read := read_peer pid history
  have effect {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  change Framing.Preserves P _
  routing_tx_source [expireCurrentPeerKeypairs,requireNotPending,branch,invariant]
    using [invalid,cleared,reset,read,effect]

theorem port (port : Nat) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clear_endpoint _ history)
    | (rx_retention_head socketInit; exact socket (socketInit_sameSocket _) history)
    | archive_traffic_step history

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
