import Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption
import Leanux.Proofs.WG.Queues.TxSelectedEncrypt

/-! A normal native encryption tail publishes a terminal head state. An AEAD
followed by Stop has no next scheduler state; normal continuation closes the
head against another pending-encryption selection. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def Terminal (id : SkbId) (w : WGWorld) : Prop :=
  ∃ state, state ≠ PacketState.uncrypted ∧ TxDisposition.HeadState id state w

private theorem constant (a : Leanux.M α) (P : Prop) : Preserves (fun _ => P) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi _
  exact hi

private theorem loop (xs : List α) (init : β) (body : α → β → Leanux.M (ForInStep β))
    (P : β → Prop)
    (step : ∀ x b, Hoare (body x b) (fun _ => P b) (fun result _ => P result.value)) :
    Hoare (forIn xs init body) (fun _ => P init) (fun result _ => P result) := by
  induction xs generalizing init with
  | nil =>
    rw [List.forIn_nil]
    exact hoare_consequence (hoare_pure _ _) (fun _ hi => hi) (fun _ _ hi => hi.1 ▸ hi.2)
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply hoare_bind _ _ (step x init)
    intro result
    cases result with
    | done b =>
      exact hoare_consequence (hoare_pure _ _) (fun _ hi => hi) (fun _ _ hi => hi.1 ▸ hi.2)
    | yield b => exact ih b

private theorem publish (items : List SkbId) (first : SkbId) (head : items.head? = some first)
    (state : PacketState) :
    Hoare (liftWG (enqueuePerPeerTx items state)) (fun _ => state ≠ .uncrypted)
      (fun _ w => Terminal first w.wg) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v mark run
  rw [liftWG_run] at run
  cases native : ((enqueuePerPeerTx items state).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at run
  | ok out =>
    obtain ⟨⟨value,g⟩,a⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨_,rfl⟩ := run
    cases items with
    | nil => cases head
    | cons id rest =>
      cases head
      exact ⟨state,mark,(hoare_iff_run_ambient _ _ _).mp
        (TxDisposition.publication_head first rest state) w.wg w.ambient value g a trivial native⟩

theorem native_tail (items : List SkbId) (first : SkbId) (head : items.head? = some first) :
    Hoare (RxWorkers.encryptStepTailSource (some items)) (fun _ => True)
      (fun _ w => Terminal first w.wg) := by
  unfold RxWorkers.encryptStepTailSource
  apply hoare_bind _ _ (constant _ True)
  intro _
  simp only [head]
  apply hoare_bind _ _ (constant _ True)
  intro saved
  apply hoare_bind (Q := fun state _ => state ≠ PacketState.uncrypted)
  · apply hoare_consequence (loop _ _ _ (fun state => state ≠ PacketState.uncrypted) ?_)
      (fun _ _ => by decide) (fun _ _ hi => hi)
    intro id state
    apply hoare_bind _ _ (constant _ _)
    intro _
    apply hoare_bind _ _ (constant _ _)
    intro packet
    apply hoare_bind _ _ (constant _ _)
    intro encrypted
    apply hoare_bind _ _ (constant _ _)
    intro success
    split
    · apply hoare_bind _ _ (constant _ _)
      intro _
      exact hoare_consequence (hoare_pure _ _) (fun _ hi => hi)
        (fun _ _ hi => hi.1 ▸ hi.2)
    · apply (hoare_iff_run _ _ _).mpr
      intro w result v _ run
      cases run
      decide
  · intro state
    split
    · apply hoare_bind _ _ (constant _ _)
      intro _
      exact hoare_bind _ _ (publish items first head state) (fun _ => preserves_pure _)
    · exact hoare_bind _ _ (publish items first head state) (fun _ => preserves_pure _)

end Leanux.Proofs.WG.TransmitSecurity.EncryptionCompletion
