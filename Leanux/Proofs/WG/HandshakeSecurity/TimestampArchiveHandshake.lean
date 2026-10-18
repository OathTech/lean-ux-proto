import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveFrames

/-! The allocation-indexed timestamp archive survives all other native handshake
operations, including response consumption, key installation and rotation. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins
open ConfiguredReceive

macro "archive_handshake_step " history:term : tactic => `(tactic| first
  | (rx_retention_head indexLookup; exact lookup _ _ $history)
  | (rx_retention_head keypairPut; exact key_put _ _ $history)
  | receive_crypto (StateInv $history)
  | archive_native_step $history)

theorem response (msg : List UInt8) (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (consumeResponse msg) := by
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' archive_handshake_step history

theorem create_initiation (pid : PeerId) (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (createInitiation pid) := by
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' archive_handshake_step history

theorem create_response (pid : PeerId) (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (createResponse pid) := by
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' archive_handshake_step history

theorem create_key (peer : Option PeerId) (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (keypairCreate peer) := by
  unfold keypairCreate
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' archive_handshake_step history

theorem zero (pid : PeerId) (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (handshakeZero pid) := by
  unfold handshakeZero
  repeat' archive_handshake_step history

theorem clear (pid : PeerId) (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (handshakeClear pid) := by
  unfold handshakeClear
  repeat' first
    | (rx_retention_head handshakeZero; exact zero _ history)
    | archive_handshake_step history

theorem add_key (pid : PeerId) (kid : KeypairId) (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (addNewKeypair pid kid) := by
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' archive_handshake_step history

theorem confirm (pid : PeerId) (kid : KeypairId) (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (receivedWithKeypair pid kid) := by
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' archive_handshake_step history

theorem clear_keys (pid : PeerId) (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (keypairsClear pid) := by
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' archive_handshake_step history

theorem derive (kid : KeypairId) (initiator : Bool) (chain : List UInt8) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (deriveKeys kid initiator chain) := by
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' archive_handshake_step history

theorem session (pid : PeerId) (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (beginSession pid) := by
  unfold beginSession WG.andM
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head keypairCreate; exact create_key _ history)
    | (rx_retention_head deriveKeys; exact derive _ _ _ history)
    | (rx_retention_head handshakeZero; exact zero _ history)
    | (rx_retention_head addNewKeypair; exact add_key _ _ history)
    | archive_handshake_step history

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
