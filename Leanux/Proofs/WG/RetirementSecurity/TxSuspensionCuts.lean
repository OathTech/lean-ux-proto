import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionWork

/-! Below-cut record consumers preserve suspended actors. The captured
Ambient writes are justified by their actual preceding get, rather than a
frame for arbitrary ambient writes or unexecuted source branches. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem ambient_get_bind (initial : List Activation) (next : Ambient→AmbientM α)
    (after : ∀saved,saved.suspended=initial→
      Preserves (fun w=>w.suspended=initial) (next saved)) :
    Preserves (fun w=>w.suspended=initial) ((MonadStateOf.get : AmbientM Ambient) >>= next) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨saved,u,read,tail⟩:=run
  cases read
  exact (hoare_iff_run _ _ _).mp (after w before) w result v before tail

theorem ambient_set (initial : List Activation) (value : Ambient) (same : value.suspended=initial) :
    Preserves (fun w=>w.suspended=initial) (MonadStateOf.set value : AmbientM Unit) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run
  exact same

theorem ambient_modify (initial : List Activation) (f : Ambient→Ambient)
    (same : ∀w,(f w).suspended=w.suspended) :
    Preserves (fun w=>w.suspended=initial) (_root_.modify f : AmbientM Unit) := by
  apply hoare_modify
  intro w before
  exact (same w).trans before

theorem cut_sites_ambient (sites : List HiddenSite) :
    SameView Ambient.suspended (AmbientM.skipCutSites sites) := by
  intro initial
  let P := fun w : Ambient=>w.suspended=initial
  have read {α : Type} (next : Ambient→AmbientM α)
      (after : ∀saved,saved.suspended=initial→Preserves P (next saved)) :
      Preserves P ((MonadStateOf.get : AmbientM Ambient) >>= next) := ambient_get_bind initial next after
  have budget : Preserves P AmbientM.recordBudget := TxActorFrames.budget initial
  have skip : Preserves P AmbientM.skipAmbient := TxActorFrames.skip initial
  have note (site : Nat) : Preserves P (AmbientM.noteNetRxStart site) := TxActorFrames.note site initial
  have unsupported {α : Type} (message : String) : Preserves P (AmbientM.unsupported message : AmbientM α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run
  have exhausted {α : Type} (message : String) : Preserves P (AmbientM.budgetExhausted message : AmbientM α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    unfold AmbientM.budgetExhausted at run
    rw [MaterialOrigin.bind_ok] at run
    obtain ⟨saved,u,getter,tail⟩:=run
    cases getter
    split at tail <;> cases tail
  have write (value : Ambient) (same : value.suspended=initial) :
      Preserves P (MonadStateOf.set value : AmbientM Unit) := ambient_set initial value same
  change Preserves P _
  simp only [AmbientM.skipCutSites]
  have loop (xs : List Nat) (b : Option (List Nat) × List Nat)
      (f : Nat → (Option (List Nat) × List Nat) → AmbientM (ForInStep (Option (List Nat) × List Nat)))
      (hf : ∀ x b, Preserves P (f x b)) : Preserves P (forIn xs b f) :=
    list_view_spec id P xs b f hf
  repeat' first
    | (rx_retention_head Bind.bind; apply read)
    | env_operation_fact budget
    | env_operation_fact skip
    | env_operation_fact note
    | env_operation_fact unsupported
    | env_operation_fact exhausted
    | env_operation_fact write
    | (rx_retention_head ForIn.forIn; first | apply loop | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
    | routing_tx_step
  all_goals assumption

theorem cut_ambient (sites : List HiddenSite) : SameView Ambient.suspended (AmbientM.skipCut sites) := by
  intro initial
  exact discard_view_spec Ambient.suspended (·=initial) _ (cut_sites_ambient sites initial)

theorem cuts (sites : List HiddenSite) : Keeps (skipCut sites : StateT S AmbientM Unit) :=
  ambient (cut_ambient sites)

theorem cut_sites (sites : List HiddenSite) : Keeps (skipCutSites sites : StateT S AmbientM (List Nat)) :=
  ambient (cut_sites_ambient sites)

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
