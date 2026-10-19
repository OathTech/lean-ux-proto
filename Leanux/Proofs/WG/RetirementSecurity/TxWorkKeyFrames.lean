import Leanux.Proofs.WG.RetirementSecurity.TxActorDecrypt

/-! Native key and Noise helpers leave pending TX work unchanged. These
frames supplement the existing exact packet/ring/queue-content projections;
they do not infer immutable peer ownership or initialized service. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem index_work (action : IndexM α) : SameView queued (liftIndex action) := by
  intro initial
  apply hoare_liftIndex action
  intro w d table before device
  simpa only [queued,device,Option.map_some,Option.getD_some] using before

macro "key_work_step " initial:term : tactic => `(tactic| first
  | (allocation_release_lift_from IndexM; exact (index_work _).wp (· = $initial))
  | (rx_retention_head liftIndex; exact (index_work _).wp (· = $initial))
  | (rx_retention_head keypairPut; exact (key_put _ _).wp (· = $initial))
  | (rx_retention_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w=>queued w=$initial))
  | (rx_retention_head hidden; unfold hidden)
  | (rx_retention_head hiddenClock64; unfold hiddenClock64)
  | (rx_retention_head updatePeer; unfold updatePeer)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | (rx_retention_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
  | receive_crypto (fun w=>queued w=$initial)
  | tx_work_step $initial)

theorem handshake_zero_work (pid : PeerId) : SameView queued (handshakeZero pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold handshakeZero
  repeat' first
    | key_work_step initial

theorem handshake_clear_work (pid : PeerId) : SameView queued (handshakeClear pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold handshakeClear
  repeat' first
    | (allocation_release_head handshakeZero; exact (handshake_zero_work _).wp (· = initial))
    | key_work_step initial

theorem clear_work (pid : PeerId) : SameView queued (keypairsClear pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' first
    | key_work_step initial

theorem expire_work (pid : PeerId) : SameView queued (expireCurrentPeerKeypairs pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold expireCurrentPeerKeypairs resetLastSentHandshake requireNotPending
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head handshakeClear; exact (handshake_clear_work _).wp (· = initial))
    | key_work_step initial

theorem create_work (owner : Option PeerId) : SameView queued (keypairCreate owner) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold keypairCreate
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | key_work_step initial

theorem rotate_work (pid : PeerId) (kid : KeypairId) : SameView queued (addNewKeypair pid kid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | key_work_step initial

theorem derive_work (kid : KeypairId) (initiator : Bool) (chain : List UInt8) : SameView queued (deriveKeys kid initiator chain) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' first
    | key_work_step initial

theorem session_work (pid : PeerId) : SameView queued (beginSession pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold beginSession WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head keypairCreate; exact (create_work _).wp (· = initial))
    | (allocation_release_head addNewKeypair; exact (rotate_work _ _).wp (· = initial))
    | (allocation_release_head deriveKeys; exact (derive_work _ _ _).wp (· = initial))
    | (allocation_release_head handshakeZero; exact (handshake_zero_work _).wp (· = initial))
    | key_work_step initial

theorem create_initiation_work (pid : PeerId) : SameView queued (createInitiation pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | key_work_step initial

theorem create_response_work (pid : PeerId) : SameView queued (createResponse pid) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | key_work_step initial

theorem add_mac_work (pid : PeerId) (msg : List UInt8) : SameView queued (addMacToPacket pid msg) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | key_work_step initial

end Leanux.Proofs.WG.RetirementSecurity.TxWork
