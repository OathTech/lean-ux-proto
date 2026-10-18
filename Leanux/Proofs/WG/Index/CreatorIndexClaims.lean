import Leanux.Proofs.WG.Index.CreatorIndexSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do
open Queues.RxCredits

/-- All normal initiation-creator returns retain hashed-key slot coverage
and the supplied retirement obligations. No owner coherence, reference budget,
record readiness, successful creation or non-NULL caller word is assumed. -/
theorem createInitiation_hashSlots_retirement (retired : Reservations) (pid : PeerId) :
    Campaign2.Ensures (createInitiation pid)
      (fun s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s) := by
  let D : Device → Prop := fun d => HashSlotCoverage d ∧ DeadHashedReserved retired d
  let P : WGWorld → Prop := fun g => ∀ d, g.dev = some d → D d
  have write (f : Peer → Peer)
      (slots : ∀ p, clearKeys (f p) = clearKeys p)
      (stamp : ∀ p, (f p).internalId = p.internalId)
      (dead : ∀ p, (f p).isDead = p.isDead) :
      Ensures (modifyPeer pid f) P (fun _ => P) :=
    modifyPeer_device_predicate pid D f (fun d p resident pre =>
      ⟨hashSlotCoverage_peerWrite d pid p (f p) resident (slots p) pre.1,
       peerWrite_deadHashedReserved retired d pid p (f p) resident (stamp p) (dead p) pre.2⟩)
  have publication : Ensures (creatorPublish pid) P (fun _ => P) :=
    creatorPublish_device_predicate pid D (fun d index pre =>
      ⟨hashSlotCoverage_handshakeInsert d pid index pre.1,
       deadHashedReserved_handshakeInsert retired d pid index pre.2⟩)
  have native := createInitiation_preserves_source pid P
    (fun _ _ => write _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    (fun _ => write _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    (write _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) publication
  intro g ambient result out after pre run
  have post := native g ambient result out after
    (fun d device => ⟨pre.1 d device,pre.2 d device⟩) run
  exact ⟨fun d device => (post d device).1,fun d device => (post d device).2⟩

/-- The actual response creator has the same coverage/retirement contract,
including ordinary None refusals and the original stopped paths. -/
theorem createResponse_hashSlots_retirement (retired : Reservations) (pid : PeerId) :
    Campaign2.Ensures (createResponse pid)
      (fun s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s) := by
  let D : Device → Prop := fun d => HashSlotCoverage d ∧ DeadHashedReserved retired d
  let P : WGWorld → Prop := fun g => ∀ d, g.dev = some d → D d
  have write (f : Peer → Peer)
      (slots : ∀ p, clearKeys (f p) = clearKeys p)
      (stamp : ∀ p, (f p).internalId = p.internalId)
      (dead : ∀ p, (f p).isDead = p.isDead) :
      Ensures (modifyPeer pid f) P (fun _ => P) :=
    modifyPeer_device_predicate pid D f (fun d p resident pre =>
      ⟨hashSlotCoverage_peerWrite d pid p (f p) resident (slots p) pre.1,
       peerWrite_deadHashedReserved retired d pid p (f p) resident (stamp p) (dead p) pre.2⟩)
  have publication : Ensures (creatorPublish pid) P (fun _ => P) :=
    creatorPublish_device_predicate pid D (fun d index pre =>
      ⟨hashSlotCoverage_handshakeInsert d pid index pre.1,
       deadHashedReserved_handshakeInsert retired d pid index pre.2⟩)
  have native := createResponse_preserves_source pid P
    (fun _ _ => write _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    (fun _ => write _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    (write _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) publication
  intro g ambient result out after pre run
  have post := native g ambient result out after
    (fun d device => ⟨pre.1 d device,pre.2 d device⟩) run
  exact ⟨fun d device => (post d device).1,fun d device => (post d device).2⟩

end Leanux.Proofs.WG.Index
