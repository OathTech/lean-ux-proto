import Leanux.Proofs.WG.RetirementSecurity.KeySlotSourceFrames

/-! Native handshake consumers preserve slot liveness through actual nullable
lookup acquisition and failure payments. Replay and cryptographic guards remain
source branches; this preservation claim does not infer their authenticity. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem initiation_out (peer ret : Option PeerId) :
    Preserves (InvExcept pending) (HandshakeLoans.initiationOut peer ret) := by
  unfold HandshakeLoans.initiationOut
  simp (config := {zeta := false}) only [branch]
  repeat' key_slot_step

theorem initiation_tail (msg e ck hash : List UInt8) (peer : Option PeerId) (pid : PeerId) :
    Preserves (InvExcept pending) (HandshakeLoans.initiationTail msg e ck hash peer pid) := by
  unfold HandshakeLoans.initiationTail WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiation_out _ _)
    | receive_crypto (InvExcept pending)
    | (rx_retention_head ite
       apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | key_slot_step

theorem initiation_after_lookup (msg e ck hash : List UInt8) (peer : Option PeerId) :
    Preserves (InvExcept pending) (HandshakeLoans.initiationAfterLookup msg e ck hash peer) := by
  unfold HandshakeLoans.initiationAfterLookup
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiation_out _ _)
    | (rx_retention_head HandshakeLoans.initiationTail; exact initiation_tail _ _ _ _ _ _)
    | key_slot_step

theorem consume_initiation (msg : List UInt8) :
    Preserves (InvExcept pending) (consumeInitiation msg) := by
  rw [HandshakeLoans.consumeInitiation_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact initiation_out _ _)
    | (rx_retention_head HandshakeLoans.initiationAfterLookup; exact initiation_after_lookup _ _ _ _ _)
    | (rx_retention_head pubkeyLookup; exact pubkey _)
    | receive_crypto (InvExcept pending)
    | key_slot_step

theorem response_tail (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) :
    Preserves (InvExcept pending) (HandshakeLoans.responseTail msg identity pid) := by
  unfold HandshakeLoans.responseTail
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | receive_crypto (InvExcept pending)
    | key_slot_step

theorem consume_response (msg : List UInt8) :
    Preserves (InvExcept pending) (consumeResponse msg) := by
  rw [HandshakeLoans.consumeResponse_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.responseTail; exact response_tail _ _ _)
    | (rx_retention_head indexLookup; exact lookup _ _)
    | key_slot_step

theorem consume_cookie (msg : List UInt8) :
    Preserves (InvExcept pending) (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact lookup _ _)
    | key_slot_step


end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
