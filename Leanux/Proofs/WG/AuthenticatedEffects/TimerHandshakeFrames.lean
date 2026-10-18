import Leanux.Proofs.WG.AuthenticatedEffects.TimerRetentionFrames
import Leanux.Proofs.Framing.WGHandshake

/-! Actual native handshake consumers, creation and session helpers retain the
incarnation, expiry and wheel entry of every surviving timer observation. No
handshake success, ownership funding or completed-driver premise is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem choice (initial) (p : Prop) [Decidable p] (a b : WG.M α)
    (ha : p → Preserves (Retained initial) a) (hb : ¬p → Preserves (Retained initial) b) :
    Preserves (Retained initial) (if p then a else b) := by
  by_cases hp : p
  · simpa only [ite_eq_left hp] using ha hp
  · simpa only [ite_eq_right hp] using hb hp

macro "timer_handshake_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp (Retained $initial))
  | (rx_retention_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp (Retained $initial))
  | (rx_retention_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (Retained $initial))
  | (rx_retention_head messageDecrypt; exact (messageDecrypt_sameWGWorld _ _ _).wp (Retained $initial))
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (Retained $initial))
  | (rx_retention_head kdf; exact (kdf_sameWGWorld _ _ _ _).wp (Retained $initial))
  | (rx_retention_head kdfOut; exact (kdfOut_sameWGWorld _ _).wp (Retained $initial))
  | (rx_retention_head peerPut; exact peerPut_retained _ $initial)
  | (rx_retention_head peerGet; exact peerGet_retained _ $initial)
  | (rx_retention_head keypairPut; exact keypairPut_retained _ _ $initial)
  | (rx_retention_head pubkeyLookup; exact pubkeyLookup_retained _ $initial)
  | (rx_retention_head indexLookup; exact indexLookup_retained _ _ $initial)
  | (rx_retention_head ite; apply choice $initial)
  | timer_retention_step $initial
  | split
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem consumeInitiation_retained (msg : Key) (initial) :
    Preserves (Retained initial) (consumeInitiation msg) := by
  unfold consumeInitiation
  simp (config := {zeta := false}) only [WG.orM,branch,branchCmp,hiddenClock64,invariant]
  repeat' timer_handshake_step initial

theorem consumeResponse_retained (msg : Key) (initial) :
    Preserves (Retained initial) (consumeResponse msg) := by
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' timer_handshake_step initial

theorem createResponse_retained (pid : PeerId) (initial) :
    Preserves (Retained initial) (createResponse pid) := by
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' timer_handshake_step initial

theorem addMac_retained (pid : PeerId) (msg : Key) (initial) :
    Preserves (Retained initial) (addMacToPacket pid msg) := by
  unfold addMacToPacket
  simp (config := {zeta := false}) only [WG.andM,branch]
  repeat' timer_handshake_step initial

theorem deriveKeys_retained (id : KeypairId) (initiator : Bool) (ck : Key) (initial) :
    Preserves (Retained initial) (deriveKeys id initiator ck) := by
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' timer_handshake_step initial

theorem keypairCreate_retained (peer : Option PeerId) (initial) :
    Preserves (Retained initial) (keypairCreate peer) := by
  unfold keypairCreate
  simp (config := {zeta := false}) only [hiddenAlloc,branch]
  repeat' timer_handshake_step initial

theorem addKeypair_retained (pid : PeerId) (id : KeypairId) (initial) :
    Preserves (Retained initial) (addNewKeypair pid id) := by
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' timer_handshake_step initial

theorem handshakeZero_retained (pid : PeerId) (initial) :
    Preserves (Retained initial) (handshakeZero pid) := by
  unfold handshakeZero
  repeat' timer_handshake_step initial

theorem beginSession_retained (pid : PeerId) (initial) :
    Preserves (Retained initial) (beginSession pid) := by
  unfold beginSession
  simp (config := {zeta := false}) only [WG.andM,branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head keypairCreate; exact keypairCreate_retained _ initial)
    | (rx_retention_head addNewKeypair; exact addKeypair_retained _ _ initial)
    | (rx_retention_head handshakeZero; exact handshakeZero_retained _ initial)
    | (rx_retention_head deriveKeys; exact deriveKeys_retained _ _ _ initial)
    | timer_handshake_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
