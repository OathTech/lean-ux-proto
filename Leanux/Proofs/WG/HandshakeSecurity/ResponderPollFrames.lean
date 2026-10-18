import Leanux.Proofs.WG.HandshakeSecurity.ResponderHistory
import Leanux.Proofs.WG.Queues.CurrentSlotPoll

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Origins Origins.Retaining Lifetimes Queues.RxCredits

theorem counter_core (kid : KeypairId) (nonce : Nat) : SameView pool (counterValidate kid nonce) := by
  intro initial
  unfold counterValidate
  apply hoare_bind _ _ (pool_get (fun p => p = initial) kid)
  intro k
  let Q := fun w => pool w = initial ∧ pool w kid = some (keyCore k)
  have setter (counter : ReplayCounter) : Preserves Q
      (setKeypair kid {k with receivingCounter := counter}) := by
    apply hoare_consequence
      (pool_set (fun p => p = initial ∧ p kid = some (keyCore k))
        kid {k with receivingCounter := counter})
    · exact fun _ h => ⟨h, h.2⟩
    · exact fun _ _ h => h
  apply hoare_consequence (P := Q) (Q := fun _ => Q) ?_ (fun _ h => h) (fun _ _ h => h.1)
  simp (config := {zeta := false}) only [WG.orM, Std.Legacy.Range.forIn_eq_forIn_range']
  material_lower
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head setKeypair; exact setter _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (index_material_head ForIn.forIn; apply list_view_spec id Q)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem native_fields {a : WG.M α} (keys : SameView pool a)
    (fields : SameView CurrentSlots.fields a) (confirmed : List Nat) :
    Preserves (History.Native confirmed) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v b entry run
  have keyFrame := (hoare_iff_run_ambient _ _ _).mp (keys (pool w)) w ambient result v b rfl run
  have fieldFrame := (hoare_iff_run_ambient _ _ _).mp (fields (CurrentSlots.fields w)) w ambient result v b rfl run
  refine ⟨?_, CurrentSlots.fields_transport entry.2 fieldFrame⟩
  intro pid core resident responder
  apply entry.1 pid core _ responder
  exact current_retained_fields fieldFrame (by rw [keyFrame]; exact Retains.refl _) pid core resident

theorem counter_native (kid : KeypairId) (nonce : Nat) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (counterValidate kid nonce) :=
  native_fields (counter_core kid nonce)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotPoll.«0».Leanux.Proofs.WG.CurrentSlots.counter_fields) kid nonce) confirmed

theorem keypairPut_native (kid : Option KeypairId) (now : Bool) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (keypairPut kid now) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  refine ⟨entry.1.retain ?_ ?_, ?_⟩
  · exact (KeyEffects.iff_run_ambient _ _).mp (keypairPut_keyEffect (allowed := NoPromotion) kid now) w a result v b run
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp (keypairPut_core kid now) w a result v b run
  · exact (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.keypairPut_preserves kid now) w a result v b entry.2 run

theorem peerPut_native (pid : Option PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (peerPut pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  refine ⟨?_, (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.peerPut_preserves pid) w a result v b entry.2 run⟩
  exact (hoare_iff_run_ambient _ _ _).mp
    (authorization_of_frames (pool_of_material (peerPut_material pid))
      (peerPut_keyEffect (allowed := NoPromotion) pid) confirmed) w a result v b entry.1 run

theorem staged_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (sendStagedPackets pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (sendStagedPackets_authorized pid confirmed) w a result v b entry.1 run,
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.sendStagedPackets_preserves pid) w a result v b entry.2 run⟩

end Leanux.Proofs.WG.HandshakeSecurity.Responder
