import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedHandshakeFrames

/-! Exact full-entry projection frames for native key creation, rotation,
confirmation and clearing. None of these operations disposes TX obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.KeyFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem index (action : IndexM α) : SameView StagedEntry.view (liftIndex action) := by
  intro initial
  apply hoare_liftIndex
  intro w d table before device
  rw [← before]
  unfold StagedEntry.view
  apply Prod.ext
  · simp [Packets.epoch,device]
  apply Prod.ext
  · funext pid; simp [Staged.stagedAt,device]
  apply Prod.ext
  · funext skb; simp [PacketMaterial.view,TxDisposition.txPackets,device]
  apply Prod.ext
  · simp [Packets.snapshot,Packets.deviceStore,device]
  apply Prod.ext
  · funext skb; simp [TxDisposition.txPackets,device]
  · funext pid; simp [txQueueContents,handoffTxView,device]

theorem world (f : WGWorld → WGWorld) (same : ∀ w, StagedEntry.view (f w) = StagedEntry.view w) :
    SameView StagedEntry.view (modify f : WG.M Unit) := by
  intro initial
  exact hoare_modify _ (fun w before => (same w).trans before)

macro "entry_key_step " initial:term : tactic => `(tactic| first
  | (receive_update_head Bind.bind
     apply Queued.update_bind $initial
     · intro p; exact ⟨rfl,rfl,rfl⟩
     intro ignored)
  | (receive_update_head setPeer; apply Queued.update; intro p; exact ⟨rfl,rfl,rfl⟩)
  | (rx_retention_head getPeer; exact Queued.read _ $initial)
  | (rx_retention_head getKeypair; exact ReceiveFrames.key_read _ $initial)
  | (rx_retention_head setKeypair; unfold setKeypair)
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
  | (rx_retention_head modifyDev; apply ReceiveFrames.device <;> intro d <;> rfl)
  | (rx_retention_head modify; apply world; intro w; rfl)
  | (rx_retention_head getDev; exact TimerFrames.store getDev_sameWGStore $initial)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (allocation_release_lift_from IndexM; exact index _ $initial)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head hiddenClock64; unfold hiddenClock64)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | receive_crypto (fun w => StagedEntry.view w = $initial)
  | rx_retention_step
  | rxstack_preserves_join)

theorem put (kid : Option KeypairId) (now : Bool) : SameView StagedEntry.view (keypairPut kid now) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold keypairPut refcountDecAndTest
  simp (config := {zeta := false}) only [branch,branchCmp,unsupported,invariant]
  repeat' entry_key_step initial

macro "entry_key_maintenance " initial:term : tactic => `(tactic| first
  | (rx_retention_head keypairPut; exact (put _ _).wp (· = $initial))
  | entry_key_step $initial)

theorem zero (pid : PeerId) : SameView StagedEntry.view (handshakeZero pid) :=
  Queued.update pid (fun p => {p with ephemeralPrivate := List.replicate 32 0, remoteEphemeral := List.replicate 32 0, hash := List.replicate 32 0, chainingKey := List.replicate 32 0, remoteIndex := 0, handshakeState := 0})
    (fun _ => ⟨rfl,rfl,rfl⟩)

theorem clear (pid : PeerId) : SameView StagedEntry.view (handshakeClear pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold handshakeClear
  repeat' first
    | (rx_retention_head handshakeZero; exact (zero _).wp (· = initial))
    | entry_key_maintenance initial

theorem create (peer : Option PeerId) : SameView StagedEntry.view (keypairCreate peer) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold keypairCreate
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' entry_key_maintenance initial

theorem rotate (pid : PeerId) (kid : KeypairId) : SameView StagedEntry.view (addNewKeypair pid kid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold addNewKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' entry_key_maintenance initial

theorem confirm (pid : PeerId) (kid : KeypairId) : SameView StagedEntry.view (receivedWithKeypair pid kid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold receivedWithKeypair
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  simp (config := {zeta := false}) only [branch]
  repeat' entry_key_maintenance initial

theorem clear_keys (pid : PeerId) : SameView StagedEntry.view (keypairsClear pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' entry_key_maintenance initial

theorem derive (kid : KeypairId) (initiator : Bool) (chain : Key) :
    SameView StagedEntry.view (deriveKeys kid initiator chain) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold deriveKeys
  simp (config := {zeta := false}) only [hiddenClock64]
  repeat' entry_key_maintenance initial

theorem session (pid : PeerId) : SameView StagedEntry.view (beginSession pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold beginSession WG.andM
  simp (config := {zeta := false}) only [branch,invariant,unsupported]
  repeat' first
    | (rx_retention_head keypairCreate; exact (create _).wp (· = initial))
    | (rx_retention_head addNewKeypair; exact (rotate _ _).wp (· = initial))
    | (rx_retention_head deriveKeys; exact (derive _ _ _).wp (· = initial))
    | (rx_retention_head handshakeZero; exact (zero _).wp (· = initial))
    | entry_key_maintenance initial

theorem expire (pid : PeerId) : SameView StagedEntry.view (expireCurrentPeerKeypairs pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold expireCurrentPeerKeypairs resetLastSentHandshake requireNotPending
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head handshakeClear; exact (clear _).wp (· = initial))
    | entry_key_maintenance initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.KeyFrames
