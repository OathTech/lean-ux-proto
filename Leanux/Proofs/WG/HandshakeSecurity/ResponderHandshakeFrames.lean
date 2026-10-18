import Leanux.Proofs.WG.HandshakeSecurity.ResponderIndexFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins Origins.Retaining ConfiguredReceive

theorem peerUpdate_native (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply native_fields (pool_of_material ((getPeer_material pid).bind (fun p => Origins.setPeer_view pid (f p))))
  intro initial
  change Preserves (fun w => CurrentSlots.fields w = initial) _
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotFrames.«0».Leanux.Proofs.WG.CurrentSlots.fields_read) initial pid
  intro p resident
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotFrames.«0».Leanux.Proofs.WG.CurrentSlots.fields_set) initial pid (f p)
  simpa only [same] using resident

theorem peerUpdate_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (same : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p) (confirmed : List Nat)
    (next : ∀ x, Preserves (History.Native confirmed) (tail x)) :
    Preserves (History.Native confirmed) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (peerUpdate_native pid f same confirmed) next

theorem readPeer_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b entry run
  exact (getPeer_normal pid w v p a b run).1 ▸ entry

theorem index_native (a : IndexM α) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (liftIndex a) := by
  apply hoare_liftIndex
  intro w d table entry device
  refine ⟨Authorized.frame entry.1 ?_, CurrentSlots.fields_transport entry.2 ?_⟩
  · unfold current
    rw [device]
    rfl
  · unfold CurrentSlots.fields RxCredits.keyWords
    simp only [device, Option.map_some, Option.bind_some]

theorem pubkey_native (key : Key) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (pubkeyLookup key) := by
  apply native_fields (pool_of_material (pubkeyLookup_material key))
  intro initial
  change Preserves (fun w => CurrentSlots.fields w = initial) _
  unfold pubkeyLookup peerGetMaybeZero
  simp (config := {zeta := false}) only [branch, branchCmp, refcountIncNotZero, requireNotPending, invariant, unsupported]
  repeat' slot_fields_step initial

macro "responder_handshake_step " confirmed:term : tactic => `(tactic| first
  | (receive_update_head setPeer; apply peerUpdate_native; intro p; rfl)
  | (receive_update_head Bind.bind
     apply peerUpdate_bind
     · intro p; rfl
     intro x)
  | (rx_retention_head getPeer; exact readPeer_native _ $confirmed)
  | (rx_retention_head peerPut; exact peerPut_native _ $confirmed)
  | (rx_retention_head indexLookup; exact indexLookup_native _ _ $confirmed)
  | (rx_retention_head pubkeyLookup; exact pubkey_native _ $confirmed)
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head getDev; exact native_store getDev_sameWGStore $confirmed)
  | (allocation_release_lift_from IndexM; exact index_native _ $confirmed)
  | (allocation_release_lift_from Net.M; exact native_store (liftRouting_sameWGStore _) $confirmed)
  | (rx_retention_head ite
     apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
  | responder_native_leaf $confirmed)

theorem initiation_native (msg : List UInt8) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (consumeInitiation msg) := by
  unfold consumeInitiation WG.orM
  simp (config := {zeta := false}) only [branch, branchCmp, hiddenClock64, invariant]
  repeat' first
    | (rx_retention_head ite; apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | receive_crypto (History.Native confirmed)
    | responder_handshake_step confirmed

theorem response_native (msg : List UInt8) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (consumeResponse msg) := by
  unfold consumeResponse
  simp (config := {zeta := false}) only [branch, invariant]
  repeat' first
    | (rx_retention_head ite; apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | receive_crypto (History.Native confirmed)
    | responder_handshake_step confirmed

theorem createResponse_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (createResponse pid) := by
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch, hidden, invariant]
  repeat' first
    | (rx_retention_head ite; apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | receive_crypto (History.Native confirmed)
    | responder_handshake_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder
