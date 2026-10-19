import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseGuards

/-! Key acquisition is expanded at its actual read, reference guard and
reference write. It does not change the selected tickets, packet ownership
or complete terminal ledger, including before a later borrow failure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staging Staging.Points
set_option maxHeartbeats 600000
attribute [local implicit_reducible] Native.action keypairGet HandshakeSecurity.StagedConservation.Take.borrow

theorem invariant_covers (before : E h w a) : Covers E (.native (.invariant α)) w a h := by
  refine ⟨before,?_⟩
  intro value u b middle run
  cases run

theorem key_covers (key : Option KeypairId)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position) (keyShape key) w a h := by
  cases key with
  | none=>
    unfold keyShape
    dsimp only [Covers,id]
    erw [covers_mpr (lift_bind _ _)]
    change Covers _ (.bind _ _) w a h
    have first:=selected_ambient (.branch .keypairGetNull true) _ rfl before
    apply covers_bind first
    intro missing u b middle absent
    cases missing <;> dsimp only
    · exact invariant_covers (first.normal absent)
    · exact first.normal absent
  | some kid=>
    unfold keyShape
    dsimp only [Covers,id]
    erw [covers_mpr (lift_bind _ _)]
    change Covers _ (.bind _ _) w a h
    have first:=selected_ambient (.branch .keypairGetNull false) _ rfl before
    apply covers_bind first
    intro missing u b middle absent
    cases missing <;> dsimp only
    · erw [covers_mpr (lift_bind _ _)]
      have read:=selected_key kid (first.normal absent)
      apply covers_bind read
      intro key v c last found
      erw [covers_mpr (by simp only [lift_bind]; rfl)]
      have inc:=selected_world (.incNotZero key.refcount) (native_inc_not_zero key.refcount) (read.normal found)
      apply covers_bind inc
      intro nonzero q d events incremented
      have guard:=selected_ambient (.branch .keypairGetZero (!nonzero)) _ rfl (inc.normal incremented)
      apply covers_bind guard
      intro zero r e final tested
      cases zero <;> dsimp only
      · erw [covers_mpr (lift_bind _ _)]
        have write:=selected_write_key kid {key with refcount:=key.refcount+1} (guard.normal tested)
        apply covers_bind write
        intro value s f done written
        exact write.normal written
      · exact guard.normal tested
    · exact first.normal absent

theorem borrow_covers
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (CompleteSelected.Ready ledger debts locals generation pid peer position)
      (borrowShape (some peer)) w a h := by
  unfold borrowShape
  dsimp only [Covers,id]
  erw [covers_mpr (lift_bind _ _)]
  have key:=key_covers peer.keypairCurrent before
  apply covers_bind key
  intro value u b middle borrowed
  exact key.normal borrowed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
