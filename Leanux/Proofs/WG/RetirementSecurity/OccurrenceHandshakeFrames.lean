import Leanux.Proofs.WG.RetirementSecurity.OccurrenceQueueContents
import Leanux.Proofs.WG.Queues.HandshakeLoans
import Leanux.Proofs.WG.Origins.ConfiguredReceive

/-! Original handshake consumption may acquire and finally release a peer.
The full TX packet store and ring are unchanged; actual empty-peer deletion
is accounted for by TX queue contents, not assumed away. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

macro "occurrence_handshake_wire " initial:term : tactic => `(tactic| first
  | (rx_retention_head peerPut; exact (peerPut_cryptWire _).wp (· = $initial))
  | (rx_retention_head peerGetMaybeZero; exact (ReceiveOccurrences.peer_get_wire _).wp (· = $initial))
  | receive_crypto (fun w => txCryptWire w = $initial)
  | occurrence_key_wire $initial)

macro "occurrence_handshake_contents " initial:term : tactic => `(tactic| first
  | (rx_retention_head peerGetMaybeZero; exact (contents_factor (ownership_queues (peerGetMaybe_ownership _))).wp (· = $initial))
  | (rx_retention_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | receive_crypto (fun w => txQueueContents w = $initial)
  | occurrence_contents_step $initial)

theorem index_lookup_wire (kinds : List IndexKind) (index : Nat) :
    SameView txCryptWire (indexLookup kinds index) := by
  intro initial
  apply (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.RxLookupHolders.«0».Leanux.Proofs.WG.RetirementSecurity.indexLookup_preserves)
  · exact ((OccurrenceKeys.index_wire) _).wp (· = initial)
  · intro owner
    exact ((ReceiveOccurrences.acquire_owner_wire) owner).wp (· = initial)

theorem index_lookup_contents (kinds : List IndexKind) (index : Nat) :
    SameView txQueueContents (indexLookup kinds index) := by
  intro initial
  apply (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.RxLookupHolders.«0».Leanux.Proofs.WG.RetirementSecurity.indexLookup_preserves)
  · exact ((fun action => contents_factor (OccurrenceKeys.index_queues action)) _).wp (· = initial)
  · intro owner
    exact ((fun owner => contents_factor (ReceiveOccurrences.acquire_owner_queues owner)) owner).wp (· = initial)

theorem pubkey_lookup_wire (key : Key) : SameView txCryptWire (pubkeyLookup key) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold pubkeyLookup
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | occurrence_handshake_wire initial

theorem initiation_out_wire (peer ret : Option PeerId) : SameView txCryptWire (HandshakeLoans.initiationOut peer ret) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold HandshakeLoans.initiationOut
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | occurrence_handshake_wire initial

theorem initiation_tail_wire (msg e ck hash : List UInt8) (peer : Option PeerId) (pid : PeerId) : SameView txCryptWire (HandshakeLoans.initiationTail msg e ck hash peer pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold HandshakeLoans.initiationTail WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact (initiation_out_wire _ _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem initiation_lookup_wire (msg e ck hash : List UInt8) (peer : Option PeerId) : SameView txCryptWire (HandshakeLoans.initiationAfterLookup msg e ck hash peer) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold HandshakeLoans.initiationAfterLookup
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact (initiation_out_wire _ _).wp (· = initial))
    | (rx_retention_head HandshakeLoans.initiationTail; exact (initiation_tail_wire _ _ _ _ _ _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem consume_initiation_wire (msg : List UInt8) : SameView txCryptWire (consumeInitiation msg) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  rw [HandshakeLoans.consumeInitiation_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact (initiation_out_wire _ _).wp (· = initial))
    | (rx_retention_head HandshakeLoans.initiationAfterLookup; exact (initiation_lookup_wire _ _ _ _ _).wp (· = initial))
    | (rx_retention_head pubkeyLookup; exact (pubkey_lookup_wire _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem response_tail_wire (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) : SameView txCryptWire (HandshakeLoans.responseTail msg identity pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold HandshakeLoans.responseTail
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | occurrence_handshake_wire initial

theorem consume_response_wire (msg : List UInt8) : SameView txCryptWire (consumeResponse msg) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  rw [HandshakeLoans.consumeResponse_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.responseTail; exact (response_tail_wire _ _ _).wp (· = initial))
    | (rx_retention_head indexLookup; exact (index_lookup_wire _ _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem cookie_consume_wire (msg : List UInt8) : SameView txCryptWire (cookieMessageConsume msg) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact (index_lookup_wire _ _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem pubkey_lookup_contents (key : Key) : SameView txQueueContents (pubkeyLookup key) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold pubkeyLookup
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | occurrence_handshake_contents initial

theorem initiation_out_contents (peer ret : Option PeerId) : SameView txQueueContents (HandshakeLoans.initiationOut peer ret) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold HandshakeLoans.initiationOut
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | occurrence_handshake_contents initial

theorem initiation_tail_contents (msg e ck hash : List UInt8) (peer : Option PeerId) (pid : PeerId) : SameView txQueueContents (HandshakeLoans.initiationTail msg e ck hash peer pid) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold HandshakeLoans.initiationTail WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact (initiation_out_contents _ _).wp (· = initial))
    | occurrence_handshake_contents initial

theorem initiation_lookup_contents (msg e ck hash : List UInt8) (peer : Option PeerId) : SameView txQueueContents (HandshakeLoans.initiationAfterLookup msg e ck hash peer) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold HandshakeLoans.initiationAfterLookup
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact (initiation_out_contents _ _).wp (· = initial))
    | (rx_retention_head HandshakeLoans.initiationTail; exact (initiation_tail_contents _ _ _ _ _ _).wp (· = initial))
    | occurrence_handshake_contents initial

theorem consume_initiation_contents (msg : List UInt8) : SameView txQueueContents (consumeInitiation msg) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  rw [HandshakeLoans.consumeInitiation_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.initiationOut; exact (initiation_out_contents _ _).wp (· = initial))
    | (rx_retention_head HandshakeLoans.initiationAfterLookup; exact (initiation_lookup_contents _ _ _ _ _).wp (· = initial))
    | (rx_retention_head pubkeyLookup; exact (pubkey_lookup_contents _).wp (· = initial))
    | occurrence_handshake_contents initial

theorem response_tail_contents (msg : List UInt8) (identity : StaticIdentity) (pid : PeerId) : SameView txQueueContents (HandshakeLoans.responseTail msg identity pid) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold HandshakeLoans.responseTail
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | occurrence_handshake_contents initial

theorem consume_response_contents (msg : List UInt8) : SameView txQueueContents (consumeResponse msg) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  rw [HandshakeLoans.consumeResponse_factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head HandshakeLoans.responseTail; exact (response_tail_contents _ _ _).wp (· = initial))
    | (rx_retention_head indexLookup; exact (index_lookup_contents _ _).wp (· = initial))
    | occurrence_handshake_contents initial

theorem cookie_consume_contents (msg : List UInt8) : SameView txQueueContents (cookieMessageConsume msg) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact (index_lookup_contents _ _).wp (· = initial))
    | occurrence_handshake_contents initial

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
