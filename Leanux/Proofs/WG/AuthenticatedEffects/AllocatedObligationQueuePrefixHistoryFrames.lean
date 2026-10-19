import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationQueueCompositionFrames

/-! The pre-installation prefix emits only original lifetime accesses; the
CPU/ring continuation emits nothing. In particular neither can conceal an
ownership-transfer or terminal event around the existing queued cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

theorem before_history (ρ : TxDisposition.Event → Option F)
    (quiet : ∀ access, ρ (.access access) = none) (pid : PeerId) (items : List SkbId) :
    HistoryFrame ρ (before pid items) := by
  have access {α : Type} (action : MixedM α) : HistoryFrame ρ (TxDisposition.nativeAccess action) :=
    focusPrefix_other _ _ _ quiet _
  unfold before
  repeat' first
    | exact access _
    | exact HistoryFrame.lift _ _
    | exact HistoryFrame.pure _ _
    | apply HistoryFrame.bind
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

theorem after_history (ρ : TxDisposition.Event → Option F) (items : List SkbId) :
    HistoryFrame ρ (after items) := by
  unfold after
  repeat' first
    | exact HistoryFrame.lift _ _
    | exact HistoryFrame.pure _ _
    | apply HistoryFrame.bind
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

theorem focused_after_history (items : List SkbId) (w : World) (history : List CausalJournal.Event) :
    (runPrefix (focused (after items)) w history).2 = history := by
  have unchanged := after_history some items w (history.filterMap CausalJournal.txEvent?)
  simp only [List.filterMap_some] at unchanged
  change history ++ ((runPrefix (after items) w (history.filterMap CausalJournal.txEvent?)).2.drop
    (history.filterMap CausalJournal.txEvent?).length).map CausalJournal.txEvent = history
  rw [unchanged]
  simp

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
