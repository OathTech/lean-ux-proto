import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceNativeFrames

/-! Native handshake/session reference-count preservation. Cryptographic
acceptance is irrelevant to this state invariant; every normal arm is covered. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins
open ConfiguredReceive

macro "peer_reference_handshake_step" : tactic => `(tactic| first
  | (rx_retention_head indexLookup; exact lookup _ _)
  | (rx_retention_head keypairPut; exact key_put _ _)
  | receive_crypto Inv
  | peer_reference_step)

theorem public_lookup (key : Key) : Preserves Inv (pubkeyLookup key) := by
  unfold pubkeyLookup
  simp (config := {zeta := false}) only [branch]
  repeat' peer_reference_step

theorem initiation_out (peer ret : Option PeerId) :
    Preserves Inv (RxCredits.HandshakeLoans.initiationOut peer ret) := by
  unfold RxCredits.HandshakeLoans.initiationOut
  simp (config := {zeta := false}) only [branch]
  repeat' first | rxstack_preserves_join | peer_reference_step

theorem timestamp (pid : PeerId) (old t : List UInt8) :
    Preserves Inv (timestampStep pid old t) := by
  unfold timestampStep writeTimestamp
  simp (config := {zeta := false}) only [branch]
  repeat' peer_reference_step

theorem initiation (msg : List UInt8) : Preserves Inv (consumeInitiation msg) := by
  rw [←consume_factor]
  unfold consumeWith checkedWith successWith
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head RxCredits.HandshakeLoans.initiationOut; exact initiation_out _ _)
    | (rx_retention_head pubkeyLookup; exact public_lookup _)
    | (rx_retention_head timestampStep; exact timestamp _ _ _)
    | (rx_retention_head writeEphemeral; exact update_peer _ _ (fun _ positive => positive))
    | (rx_retention_head writeMaterial; exact update_peer _ _ (fun _ positive => positive))
    | (rx_retention_head writeConsumption; exact update_peer _ _ (fun _ positive => positive))
    | (rx_retention_head writeConsumedTag; exact update_peer _ _ (fun _ positive => positive))
    | (rx_retention_head WG.orM; unfold WG.orM)
    | rxstack_preserves_join
    | peer_reference_handshake_step

theorem response (msg : List UInt8) : Preserves Inv (consumeResponse msg) := by
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' peer_reference_handshake_step

theorem create_initiation (pid : PeerId) : Preserves Inv (createInitiation pid) := by
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' peer_reference_handshake_step

theorem create_response (pid : PeerId) : Preserves Inv (createResponse pid) := by
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' peer_reference_handshake_step

theorem create_key (peer : Option PeerId) : Preserves Inv (keypairCreate peer) := by
  unfold keypairCreate
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' peer_reference_handshake_step

theorem zero (pid : PeerId) : Preserves Inv (handshakeZero pid) := by
  unfold handshakeZero
  repeat' peer_reference_handshake_step

theorem clear (pid : PeerId) : Preserves Inv (handshakeClear pid) := by
  unfold handshakeClear
  repeat' first
    | (rx_retention_head handshakeZero; exact zero _)
    | peer_reference_handshake_step

theorem add_key (pid : PeerId) (kid : KeypairId) : Preserves Inv (addNewKeypair pid kid) := by
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' peer_reference_handshake_step

theorem confirm (pid : PeerId) (kid : KeypairId) : Preserves Inv (receivedWithKeypair pid kid) := by
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' peer_reference_handshake_step

theorem clear_keys (pid : PeerId) : Preserves Inv (keypairsClear pid) := by
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' peer_reference_handshake_step

theorem derive (kid : KeypairId) (initiator : Bool) (chain : List UInt8) :
    Preserves Inv (deriveKeys kid initiator chain) := by
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' peer_reference_handshake_step

theorem session (pid : PeerId) : Preserves Inv (beginSession pid) := by
  unfold beginSession WG.andM
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head keypairCreate; exact create_key _)
    | (rx_retention_head deriveKeys; exact derive _ _ _)
    | (rx_retention_head handshakeZero; exact zero _)
    | (rx_retention_head addNewKeypair; exact add_key _ _)
    | peer_reference_handshake_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
