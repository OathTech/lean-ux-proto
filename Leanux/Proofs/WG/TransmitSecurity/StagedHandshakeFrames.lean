import Leanux.Proofs.WG.TransmitSecurity.StagedNativeFrames

/-! Handshake writes, session creation and slot rotation preserve the ordered
staged queue of every surviving peer. These frames use the actual operations
and need no key-slot transition hypothesis. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins
open ConfiguredReceive
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem conditional (p : Prop) [Decidable p] (a b : WG.M α)
    (P : WGWorld → Prop) (ha : Preserves P a) (hb : Preserves P b) :
    Preserves P (if p then a else b) := by
  by_cases h : p <;> simp only [h,↓reduceIte] <;> assumption

macro "staged_handshake_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head ite; apply conditional)
  | rxstack_preserves_join
  | (rx_retention_head indexLookup; exact lookup _ _ $initial)
  | (rx_retention_head keypairPut; exact key_put _ _ $initial)
  | receive_crypto (Retains $initial)
  | staged_native_step $initial)

theorem response (msg : List UInt8) : Frame (consumeResponse msg) := by
  intro initial
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' staged_handshake_step initial

theorem create_initiation (pid : PeerId) : Frame (createInitiation pid) := by
  intro initial
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' staged_handshake_step initial

theorem create_response (pid : PeerId) : Frame (createResponse pid) := by
  intro initial
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' staged_handshake_step initial

theorem create_key (peer : Option PeerId) : Frame (keypairCreate peer) := by
  intro initial
  unfold keypairCreate
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' staged_handshake_step initial

theorem zero (pid : PeerId) : Frame (handshakeZero pid) := by
  intro initial
  unfold handshakeZero
  repeat' staged_handshake_step initial

theorem clear (pid : PeerId) : Frame (handshakeClear pid) := by
  intro initial
  unfold handshakeClear
  repeat' first
    | (rx_retention_head handshakeZero; exact zero _ initial)
    | staged_handshake_step initial

theorem add_key (pid : PeerId) (kid : KeypairId) : Frame (addNewKeypair pid kid) := by
  intro initial
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' staged_handshake_step initial

theorem confirm (pid : PeerId) (kid : KeypairId) : Frame (receivedWithKeypair pid kid) := by
  intro initial
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' staged_handshake_step initial

theorem clear_keys (pid : PeerId) : Frame (keypairsClear pid) := by
  intro initial
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' staged_handshake_step initial

theorem derive (kid : KeypairId) (initiator : Bool) (chain : List UInt8) :
    Frame (deriveKeys kid initiator chain) := by
  intro initial
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' staged_handshake_step initial

theorem session (pid : PeerId) : Frame (beginSession pid) := by
  intro initial
  unfold beginSession WG.andM
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head keypairCreate; exact create_key _ initial)
    | (rx_retention_head deriveKeys; exact derive _ _ _ initial)
    | (rx_retention_head handshakeZero; exact zero _ initial)
    | (rx_retention_head addNewKeypair; exact add_key _ _ initial)
    | staged_handshake_step initial

theorem pubkey_lookup (key : Key) : Frame (pubkeyLookup key) := by
  intro initial
  unfold pubkeyLookup
  simp (config := {zeta := false}) only [branch]
  repeat' staged_handshake_step initial

theorem initiation (msg : List UInt8) : Frame (consumeInitiation msg) := by
  intro initial
  unfold consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head pubkeyLookup; exact pubkey_lookup _ initial)
    | staged_handshake_step initial

end Leanux.Proofs.WG.TransmitSecurity.Staged
