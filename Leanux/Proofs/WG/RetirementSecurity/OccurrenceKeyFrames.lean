import Leanux.Proofs.WG.RetirementSecurity.OccurrenceWorkers

/-! Actual key/session maintenance leaves TX physical occurrences and cipher
aliases unchanged. Key allocation advances its own frontier; these frames
project only TX packet residency, peer queues and the encryption ring. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceKeys
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits

theorem index_wire (action : IndexM α) : SameView txCryptWire (liftIndex action) := by
  intro initial
  apply hoare_liftIndex action
  intro w d table before device
  simpa only [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,device,Option.map_some,Option.bind_some] using before

macro "occurrence_key_wire " initial:term : tactic => `(tactic| first
  | (allocation_release_lift_from IndexM; exact (index_wire _).wp (· = $initial))
  | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | (allocation_release_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
  | (allocation_release_head hidden; unfold hidden)
  | (allocation_release_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (allocation_release_head modify; apply hoare_modify; intro w before; exact before)
  | (allocation_release_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => txCryptWire w = $initial))
  | (allocation_release_head hiddenClock64; unfold hiddenClock64)
  | (allocation_release_head keypairPut
     exact ((TxRing.keypairPut_frame _ _).product (TxDisposition.keyPut_packets _ _)).wp (· = $initial))
  | (allocation_release_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
  | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_head liftIndex; exact (index_wire _).wp (· = $initial))
  | (allocation_release_head getDev
     exact (getDev_sameWGStore.of_factor (fun store => txCryptWire {dev := store.dev})
       txCryptWire (fun _ => rfl)).wp (· = $initial))
  | (allocation_release_head updatePeer; unfold updatePeer)
  | (allocation_release_head generatePublic; exact (generatePublic_sameWGWorld _).wp (fun w => txCryptWire w = $initial))
  | (allocation_release_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp (fun w => txCryptWire w = $initial))
  | (allocation_release_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp (fun w => txCryptWire w = $initial))
  | (allocation_release_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (fun w => txCryptWire w = $initial))
  | (allocation_release_head messageDecrypt; exact (messageDecrypt_sameWGWorld _ _ _).wp (fun w => txCryptWire w = $initial))
  | (allocation_release_head kdf; exact (Framing.kdf_sameWGWorld _ _ _ _).wp (fun w => txCryptWire w = $initial))
  | (allocation_release_head kdfOut; exact (Framing.kdfOut_sameWGWorld _ _).wp (fun w => txCryptWire w = $initial))
  | crypt_wire_step $initial)

theorem index_queues (action : IndexM α) : SameView handoffTxView (liftIndex action) := by
  intro initial
  apply hoare_liftIndex action
  intro w d table before device
  funext pid
  simpa only [handoffTxView,device,Option.bind_some] using congrFun before pid

macro "occurrence_key_queues " initial:term : tactic => `(tactic| first
  | (allocation_release_lift_from IndexM; exact (index_queues _).wp (· = $initial))
  | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | (allocation_release_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
  | (allocation_release_head hidden; unfold hidden)
  | (allocation_release_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (allocation_release_head modify; apply hoare_modify; intro w before; exact before)
  | (allocation_release_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => handoffTxView w = $initial))
  | (allocation_release_head hiddenClock64; unfold hiddenClock64)
  | (allocation_release_head keypairPut
     exact ((keypairPut_protect _ _).factor (fun s => s.2.2.1)).wp (· = $initial))
  | (allocation_release_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
  | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_head liftIndex; exact (index_queues _).wp (· = $initial))
  | (allocation_release_head getDev
     exact (getDev_sameWGStore.of_factor (fun store => handoffTxView {dev := store.dev})
       handoffTxView (fun _ => rfl)).wp (· = $initial))
  | (allocation_release_head updatePeer; unfold updatePeer)
  | (allocation_release_head generatePublic; exact (generatePublic_sameWGWorld _).wp (fun w => handoffTxView w = $initial))
  | (allocation_release_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp (fun w => handoffTxView w = $initial))
  | (allocation_release_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp (fun w => handoffTxView w = $initial))
  | (allocation_release_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (fun w => handoffTxView w = $initial))
  | (allocation_release_head messageDecrypt; exact (messageDecrypt_sameWGWorld _ _ _).wp (fun w => handoffTxView w = $initial))
  | (allocation_release_head kdf; exact (Framing.kdf_sameWGWorld _ _ _ _).wp (fun w => handoffTxView w = $initial))
  | (allocation_release_head kdfOut; exact (Framing.kdfOut_sameWGWorld _ _).wp (fun w => handoffTxView w = $initial))
  | crypt_queue_step $initial)

theorem handshake_zero_wire (pid : PeerId) : SameView txCryptWire (handshakeZero pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold handshakeZero
  repeat' first
    | occurrence_key_wire initial

theorem handshake_zero_queues (pid : PeerId) : SameView handoffTxView (handshakeZero pid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold handshakeZero
  repeat' first
    | occurrence_key_queues initial

theorem handshake_clear_wire (pid : PeerId) : SameView txCryptWire (handshakeClear pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold handshakeClear
  repeat' first
    | (allocation_release_head handshakeZero; exact (handshake_zero_wire _).wp (· = initial))
    | occurrence_key_wire initial

theorem handshake_clear_queues (pid : PeerId) : SameView handoffTxView (handshakeClear pid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold handshakeClear
  repeat' first
    | (allocation_release_head handshakeZero; exact (handshake_zero_queues _).wp (· = initial))
    | occurrence_key_queues initial

theorem clear_wire (pid : PeerId) : SameView txCryptWire (keypairsClear pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' first
    | occurrence_key_wire initial

theorem clear_queues (pid : PeerId) : SameView handoffTxView (keypairsClear pid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' first
    | occurrence_key_queues initial

theorem expire_wire (pid : PeerId) : SameView txCryptWire (expireCurrentPeerKeypairs pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold expireCurrentPeerKeypairs resetLastSentHandshake requireNotPending
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head handshakeClear; exact (handshake_clear_wire _).wp (· = initial))
    | occurrence_key_wire initial

theorem expire_queues (pid : PeerId) : SameView handoffTxView (expireCurrentPeerKeypairs pid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold expireCurrentPeerKeypairs resetLastSentHandshake requireNotPending
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head handshakeClear; exact (handshake_clear_queues _).wp (· = initial))
    | occurrence_key_queues initial

theorem create_wire (owner : Option PeerId) : SameView txCryptWire (keypairCreate owner) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold keypairCreate
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | occurrence_key_wire initial

theorem create_queues (owner : Option PeerId) : SameView handoffTxView (keypairCreate owner) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold keypairCreate
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | occurrence_key_queues initial

theorem rotate_wire (pid : PeerId) (kid : KeypairId) : SameView txCryptWire (addNewKeypair pid kid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | occurrence_key_wire initial

theorem rotate_queues (pid : PeerId) (kid : KeypairId) : SameView handoffTxView (addNewKeypair pid kid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | occurrence_key_queues initial

theorem derive_wire (kid : KeypairId) (initiator : Bool) (chain : List UInt8) : SameView txCryptWire (deriveKeys kid initiator chain) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' first
    | occurrence_key_wire initial

theorem derive_queues (kid : KeypairId) (initiator : Bool) (chain : List UInt8) : SameView handoffTxView (deriveKeys kid initiator chain) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' first
    | occurrence_key_queues initial

theorem session_wire (pid : PeerId) : SameView txCryptWire (beginSession pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold beginSession WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head keypairCreate; exact (create_wire _).wp (· = initial))
    | (allocation_release_head addNewKeypair; exact (rotate_wire _ _).wp (· = initial))
    | (allocation_release_head deriveKeys; exact (derive_wire _ _ _).wp (· = initial))
    | (allocation_release_head handshakeZero; exact (handshake_zero_wire _).wp (· = initial))
    | occurrence_key_wire initial

theorem session_queues (pid : PeerId) : SameView handoffTxView (beginSession pid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold beginSession WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head keypairCreate; exact (create_queues _).wp (· = initial))
    | (allocation_release_head addNewKeypair; exact (rotate_queues _ _).wp (· = initial))
    | (allocation_release_head deriveKeys; exact (derive_queues _ _ _).wp (· = initial))
    | (allocation_release_head handshakeZero; exact (handshake_zero_queues _).wp (· = initial))
    | occurrence_key_queues initial

theorem create_initiation_wire (pid : PeerId) : SameView txCryptWire (createInitiation pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | occurrence_key_wire initial

theorem create_initiation_queues (pid : PeerId) : SameView handoffTxView (createInitiation pid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | occurrence_key_queues initial

theorem create_response_wire (pid : PeerId) : SameView txCryptWire (createResponse pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | occurrence_key_wire initial

theorem create_response_queues (pid : PeerId) : SameView handoffTxView (createResponse pid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | occurrence_key_queues initial

theorem add_mac_wire (pid : PeerId) (msg : List UInt8) : SameView txCryptWire (addMacToPacket pid msg) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | occurrence_key_wire initial

theorem add_mac_queues (pid : PeerId) (msg : List UInt8) : SameView handoffTxView (addMacToPacket pid msg) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | occurrence_key_queues initial

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceKeys
