import Leanux.Proofs.WG.HandshakeSecurity.AllocationSource

namespace Leanux.Proofs.WG.HandshakeSecurity.Installation
open Leanux Leanux.WG Leanux.Proofs.Logged

def Evidence (base h : List AllocationReceipt) : Prop :=
  h = base ∨ ∃ r, h = base ++ [r] ∧ r.Valid

def Allocated (base : List AllocationReceipt) (created : Option KeypairId)
    (h : List AllocationReceipt) : Prop :=
  ∃ r, h = base ++ [r] ∧ r.Valid ∧ r.execution.value = created

def FrontResult (base : List AllocationReceipt) (result : Option SessionOrigin.Context)
    (h : List AllocationReceipt) : Prop :=
  Evidence base h ∧ ∀ context, result = some context → Allocated base (some context.slot) h

theorem Allocated.evidence {base h : List AllocationReceipt} {created : Option KeypairId}
    (ha : Allocated base created h) : Evidence base h :=
  Or.inr ⟨ha.choose, ha.choose_spec.1, ha.choose_spec.2.1⟩

private theorem silent {α : Type} (base : List AllocationReceipt)
    (P : List AllocationReceipt → Prop) (safe : ∀ h, P h → Evidence base h) (action : WG.M α) :
    StatePrefixPreserves (fun h _ _ => P h) (Evidence base) (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun h _ _ hi => safe h hi) (fun _ _ _ _ _ _ hi _ => hi)

private theorem none_result (base : List AllocationReceipt)
    (P : List AllocationReceipt → Prop) (safe : ∀ h, P h → Evidence base h) :
    StatePrefixEnsures (fun h _ _ => P h) (Evidence base)
      (pure none : WGPrefix AllocationReceipt (Option SessionOrigin.Context))
      (fun result h _ _ => FrontResult base result h) :=
  StatePrefixEnsures.pure _ (fun h _ _ hi => safe h hi)
    (fun h _ _ hi => ⟨safe h hi, by intro context impossible; cases impossible⟩)

private theorem stopped {α : Type} (base : List AllocationReceipt)
    (P : List AllocationReceipt → Prop) (safe : ∀ h, P h → Evidence base h)
    (Q : α → List AllocationReceipt → WGWorld → Ambient → Prop) (message : String) :
    StatePrefixEnsures (fun h _ _ => P h) (Evidence base)
      (liftWGPrefix (invariant message)) Q := by
  apply StatePrefixEnsures.lift _ (fun h _ _ hi => safe h hi)
  intro h w a x v b hi run
  cases run

theorem create_allocated (base : List AllocationReceipt) (word : Option PeerId) :
    StatePrefixEnsures (fun h _ _ => h = base) (Evidence base) (createObserved word)
      (fun created h _ _ => Allocated base created h) := by
  intro w a h hi
  subst h
  have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (keypairCreate word))
    (fun r => (⟨word, r⟩ : AllocationReceipt)) w a base
  rw [runWGPrefix_lift] at equation
  change runStatePrefix (createObserved word) w a base = _ at equation
  unfold runStatePrefix at equation
  rw [equation]
  cases run : ((keypairCreate word).run w).run a with
  | error stop => exact ⟨[], by simp, Or.inl rfl, trivial⟩
  | ok out =>
    rcases out with ⟨⟨created, v⟩, b⟩
    exact ⟨_, rfl, Or.inr ⟨⟨word, ⟨created, w, v, a, b⟩⟩, rfl, run⟩,
      ⟨⟨word, ⟨created, w, v, a, b⟩⟩, rfl, run, rfl⟩⟩

theorem front_evidence (base : List AllocationReceipt) (pid : PeerId) :
    StatePrefixEnsures (fun h _ _ => h = base) (Evidence base) (frontObserved pid)
      (fun result h _ _ => FrontResult base result h) := by
  have unchanged {α : Type} (action : WG.M α) :=
    silent base (fun h => h = base) (fun _ hi => Or.inl hi) action
  unfold frontObserved SessionOrigin.frontWith
  apply StatePrefixEnsures.bind (unchanged (getPeer pid))
  intro p
  apply StatePrefixEnsures.bind (unchanged _)
  intro rejected
  split
  · exact none_result base _ (fun _ hi => Or.inl hi)
  · apply StatePrefixEnsures.bind (unchanged (IndexOwner.peerWord (.handshake pid)))
    intro word
    apply StatePrefixEnsures.bind (create_allocated base word)
    intro created
    apply StatePrefixEnsures.bind (silent base (Allocated base created) (fun _ hi => hi.evidence) _)
    intro missing
    split
    · exact none_result base _ (fun _ hi => hi.evidence)
    · cases created with
      | none => exact stopped base _ (fun _ hi => hi.evidence) _ _
      | some kp =>
        apply StatePrefixEnsures.bind (silent base (Allocated base (some kp)) (fun _ hi => hi.evidence) _)
        intro peer
        apply StatePrefixEnsures.bind (silent base (Allocated base (some kp)) (fun _ hi => hi.evidence) _)
        intro _
        apply StatePrefixEnsures.bind (silent base (Allocated base (some kp)) (fun _ hi => hi.evidence) _)
        intro direction
        apply StatePrefixEnsures.bind (silent base (Allocated base (some kp)) (fun _ hi => hi.evidence) _)
        intro _
        apply StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.evidence)
        intro h w a hi
        refine ⟨hi.evidence, ?_⟩
        intro context equal
        cases equal
        exact hi

theorem evidence (base : List AllocationReceipt) (pid : PeerId) :
    StatePrefixEnsures (fun h _ _ => h = base) (Evidence base) (observed pid)
      (fun result h _ _ => Evidence base h ∧ (result = true →
        ∃ kp, Allocated base (some kp) h)) := by
  unfold observed
  apply StatePrefixEnsures.bind (front_evidence base pid)
  intro result
  cases result with
  | none =>
    exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1)
      (fun _ _ _ hi => ⟨hi.1, by intro impossible; cases impossible⟩)
  | some context =>
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
    intro h w a x v b hi _
    exact ⟨hi.1, fun _ => ⟨context.slot, hi.2 context rfl⟩⟩

end Leanux.Proofs.WG.HandshakeSecurity.Installation
