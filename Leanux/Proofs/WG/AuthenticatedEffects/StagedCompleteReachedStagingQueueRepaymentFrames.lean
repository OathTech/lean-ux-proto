import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointAccounts

/-! A queued-initiation repayment is funded by its own preceding borrow.
Its fixed release points therefore preserve the original ledger, including
the native decrement before its receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open CompleteCarrier HandshakeSecurity.StagedDisposal PeerRetirement

theorem funded_release_none (funded : Queued.Funded pid w)
    (native : ((releaseCut (some pid)).run w).run a = .ok ((value,v),b)) :
    value = none := by
  obtain ⟨target,clock,actual⟩ := AllocatedObligation.Publication.release_cut_nonfinal pid funded a
  rw [native] at actual
  exact (Prod.mk.inj (Prod.mk.inj (Except.ok.inj actual)).1).1

theorem release_none_view
    (native : ((releaseCut peer).run w).run a = .ok ((none,v),b)) :
    StagedEntry.view v = StagedEntry.view w := by
  have path := release_cases peer w a
  rw [native] at path
  cases path with
  | null => rfl
  | nonfinal device resident _ => exact Points.decrement_view device resident

/-- Each actual release cut retains the same packet account. The native
borrow excludes final peer erasure, so no successor ledger is substituted. -/
theorem funded_release_point
    (before : Accounted h ledger debts locals w)
    (funded : Queued.Funded pid w)
    (point : Points.Point (some pid) w a h v b middle) :
    Accounted middle ledger debts locals v := by
  cases point with
  | entry => exact before
  | native stage value performed => exact Points.Stage.accounted before performed
  | erased value performed =>
    have none := funded_release_none funded performed
    subst value
    exact before.same_view (release_none_view performed)
  | recorded value performed =>
    have none := funded_release_none funded performed
    subst value
    exact (before.same_view (release_none_view performed)).append_quiet _
      (by intro event member; cases List.mem_singleton.mp member; rfl)
      (by intro event member; cases List.mem_singleton.mp member; intro position; rfl)
  | finish target peer site native performed =>
    have impossible := funded_release_none funded native
    cases impossible

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
