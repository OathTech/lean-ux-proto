import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointFrames

/-! Every fixed release point retains its entry ledger or its actual
successor. The native erasure interval owes precisely the original receipt;
its emission is total and does not mutate WGWorld. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
open Leanux Leanux.WG Leanux.Proofs.Logged
open CausalJournal HandshakeSecurity.StagedDisposal CompleteCarrier TransmitSecurity
open Staged.Obligations AllocatedObligation

abbrev AccountAt (ledger : Ledger) (debts : List CleanupDebt) (locals : List RetirementSecurity.TxLocalBatch)
    (h : History) (w : WGWorld) : Prop :=
  ∃ next, Staged.Obligations.Step ledger next ∧ AllocatedFrame ledger next ∧
    Accounted h next debts locals w

def receipt (peer : Option PeerId) (value : Cached) (origin target : WGWorld)
    (clock next : Ambient) : WGPrefix CausalJournal.Event Unit :=
  emitStatePrefix (releaseEvent peer value origin target clock next)

theorem receipt_total (peer : Option PeerId) (value : Cached) (origin target : WGWorld)
    (clock next : Ambient) (h : History) :
    runWGPrefix (receipt peer value origin target clock next) target next h=
      (.ok (((),target),next),h++[releaseEvent peer value origin target clock next]) := rfl

/-- Pending carries the literal native release, its original account and
its actual successor at the one still-unemitted receipt. It does not assert
that the old queued cohort remains resident in the erased world. -/
inductive Evidence (ledger : Ledger) (debts : List CleanupDebt) (locals : List RetirementSecurity.TxLocalBatch) :
    History → WGWorld → Prop where
  | accounted (account : AccountAt ledger debts locals h w) : Evidence ledger debts locals h w
  | pending (peer : Option PeerId) (value : Cached) (origin target : WGWorld) (clock next : Ambient)
      (before : Accounted h ledger debts locals origin)
      (native : ((releaseCut peer).run origin).run clock=.ok ((value,target),next))
      (after : AccountAt ledger debts locals
        (h++[releaseEvent peer value origin target clock next]) target) :
      Evidence ledger debts locals h target

theorem AccountAt.initial (before : Accounted h ledger debts locals w) :
    AccountAt ledger debts locals h w :=
  ⟨ledger,Staged.Obligations.Step.refl ledger,AllocatedFrame.refl ledger,before⟩

theorem native_account (before : Accounted h ledger debts locals w)
    (native : ((releaseCut peer).run w).run a=.ok ((value,v),b)) :
    AccountAt ledger debts locals (h++[releaseEvent peer value w v a b]) v := by
  obtain ⟨next,step,frame,_,entry,complete⟩ :=
    StagedTerminalComplete.Source.original_native_entry peer before.entry before.complete a b native
  exact ⟨next,step,frame,entry,complete⟩

/-- The account is derived at the same actual native world and history at
every declared point, on successful paths and before any later Stop. -/
theorem Point.evidence (before : Accounted h ledger debts locals w)
    (point : Point peer w a h u b middle) : Evidence ledger debts locals middle u := by
  cases point with
  | entry => exact .accounted (AccountAt.initial before)
  | native stage value performed =>
    exact .accounted (AccountAt.initial (Stage.accounted before performed))
  | erased value performed =>
    exact .pending peer value w _ a _ before performed (native_account before performed)
  | recorded value performed => exact .accounted (native_account before performed)
  | finish pid p site native performed =>
    obtain ⟨next,step,frame,accounted⟩ := native_account before native
    exact .accounted ⟨next,step,frame,finish_accounted accounted performed⟩

/-- At each pending release point the one due receipt completes on the
same world, and its successor retains every pre-existing terminal. -/
theorem pending_emission (before : Accounted h ledger debts locals w)
    (native : ((releaseCut peer).run w).run a=.ok ((value,v),b)) :
    runWGPrefix (receipt peer value w v a b) v b h=
      (.ok (((),v),b),h++[releaseEvent peer value w v a b]) ∧
    AccountAt ledger debts locals (h++[releaseEvent peer value w v a b]) v :=
  ⟨receipt_total _ _ _ _ _ _ _,native_account before native⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
