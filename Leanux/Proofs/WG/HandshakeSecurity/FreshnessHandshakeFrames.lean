import Leanux.Proofs.WG.HandshakeSecurity.FreshnessNativeFrames

/-! Native handshake operations other than accepted initiation retain the
allocation and timestamp of every surviving peer. These frames permit key
creation and rotation, without using a key-slot transition hypothesis. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Freshness
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins
open ConfiguredReceive

macro "freshness_handshake_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head indexLookup; exact lookup _ _ $initial)
  | (rx_retention_head keypairPut; exact key_put _ _ $initial)
  | receive_crypto (RetainsFreshness $initial)
  | freshness_native_step $initial)

theorem response (msg : List UInt8) : Frame (consumeResponse msg) := by
  intro initial
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' freshness_handshake_step initial

theorem create_initiation (pid : PeerId) : Frame (createInitiation pid) := by
  intro initial
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' freshness_handshake_step initial

theorem create_response (pid : PeerId) : Frame (createResponse pid) := by
  intro initial
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' freshness_handshake_step initial

theorem create_key (peer : Option PeerId) : Frame (keypairCreate peer) := by
  intro initial
  unfold keypairCreate
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' freshness_handshake_step initial

theorem zero (pid : PeerId) : Frame (handshakeZero pid) := by
  intro initial
  unfold handshakeZero
  repeat' freshness_handshake_step initial

theorem clear (pid : PeerId) : Frame (handshakeClear pid) := by
  intro initial
  unfold handshakeClear
  repeat' first
    | (rx_retention_head handshakeZero; exact zero _ initial)
    | freshness_handshake_step initial

theorem add_key (pid : PeerId) (kid : KeypairId) : Frame (addNewKeypair pid kid) := by
  intro initial
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' freshness_handshake_step initial

theorem confirm (pid : PeerId) (kid : KeypairId) : Frame (receivedWithKeypair pid kid) := by
  intro initial
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' freshness_handshake_step initial

theorem clear_keys (pid : PeerId) : Frame (keypairsClear pid) := by
  intro initial
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' freshness_handshake_step initial

theorem derive (kid : KeypairId) (initiator : Bool) (chain : List UInt8) :
    Frame (deriveKeys kid initiator chain) := by
  intro initial
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' freshness_handshake_step initial

theorem session (pid : PeerId) : Frame (beginSession pid) := by
  intro initial
  unfold beginSession WG.andM
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head keypairCreate; exact create_key _ initial)
    | (rx_retention_head deriveKeys; exact derive _ _ _ initial)
    | (rx_retention_head handshakeZero; exact zero _ initial)
    | (rx_retention_head addNewKeypair; exact add_key _ _ initial)
    | freshness_handshake_step initial

end Leanux.Proofs.WG.HandshakeSecurity.Freshness
