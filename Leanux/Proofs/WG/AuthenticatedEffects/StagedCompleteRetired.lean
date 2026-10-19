import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryRetired
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCompleteCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredFrames

/-! Same-ledger destruction after an actual quiescent source cut. A successful
reset keeps already established outcomes. It never supplies a terminal outcome
for an outstanding ticket; staged quiescence remains an explicit caller fact. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRetired
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier
variable {history : List Event} {ledger : Ledger} {w v : WGWorld} {a b : Ambient}

/-- Successful native destruction guards discharge TX-cell emptiness from
service. The independent staged-empty premise is not inferred from the guards. -/
theorem checked_no_pending (before : Accounted history ledger [] [] w)
    (service : TxWork.Serving [] [] [] w)
    (staged : ∀ epoch pid stamp, stagedPackets epoch pid stamp w = [])
    (run : (TxWork.Destruct.check.run w).run a = .ok (((),v),b)) :
    v = w ∧ Retired.NoPending ledger := by
  obtain ⟨same,cells⟩ := TxWork.Destruct.check_empty service run
  refine ⟨same,Retired.no_pending before.entry staged ?_⟩
  simpa only [same] using cells

/-- Replacing an allocation whose obligations are already terminal preserves
both forward evidence and the converse receipt account on exactly one ledger. -/
theorem absent_replacement (before : Accounted history ledger [] [] w)
    (settled : Retired.NoPending ledger) (absent : v.dev = none) :
    Accounted history ledger [] [] v :=
  ⟨Retired.empty_replacement before.entry settled
      (RetiredFrames.absent_staged absent) (RetiredFrames.absent_cells absent)
      (RetiredFrames.absent_bounds absent) (RetiredFrames.absent_coverage absent)
      (RetiredFrames.absent_inventory absent),before.complete⟩

/-- The same accounted entry is present immediately before reset after the
literal metadata/limiter suffix. Its old ticket domain has no pending member. -/
theorem before_reset (before : Accounted history ledger [] [] w)
    (service : TxWork.Serving [] [] [] w)
    (staged : ∀ epoch pid stamp, stagedPackets epoch pid stamp w = [])
    (run : ((do TxWork.Destruct.check; TxWork.Destruct.settle : WG.M Unit).run w).run a =
      .ok (((),v),b)) : Accounted history ledger [] [] v ∧ Retired.NoPending ledger := by
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨value,u,c,checked,settled⟩ := run
  cases value
  obtain ⟨same,noPending⟩ := checked_no_pending before service staged checked
  subst u
  exact ⟨before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp
    RetiredFrames.settle w c () v b settled),noPending⟩

/-- The literal final destructor suffix, beginning at its work-queue guards. -/
def tail : WG.M Unit := do
  TxWork.Destruct.check
  TxWork.Destruct.settle
  RetiredFrames.reset

theorem tail_returned (before : Accounted history ledger [] [] w)
    (service : TxWork.Serving [] [] [] w)
    (staged : ∀ epoch pid stamp, stagedPackets epoch pid stamp w = [])
    (run : (tail.run w).run a = .ok (((),v),b)) :
    Accounted history ledger [] [] v ∧ Retired.NoPending ledger := by
  simp only [tail,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨value,u,c,checked,_,s,e,settled,reset⟩ := run
  cases value
  obtain ⟨same,noPending⟩ := checked_no_pending before service staged checked
  subst u
  have atReset := before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp
    RetiredFrames.settle w c () s e settled)
  exact ⟨absent_replacement atReset noPending (RetiredFrames.reset_absent reset),noPending⟩

/-- Stop retains the actual incoming accounted cut and unchanged journal;
normal return retains the same ledger after the real native reset. The caller
still owes service and staged quiescence at this exact guard entry. -/
theorem tail_checked : StatePrefixEnsures
    (fun h w _ => Accounted h ledger [] [] w ∧ TxWork.Serving [] [] [] w ∧
      ∀ epoch pid stamp, stagedPackets epoch pid stamp w = [])
    (CompleteCarrier.Safe ledger [] []) (liftWGPrefix tail)
    (fun _ h w _ => Accounted h ledger [] [] w ∧ Retired.NoPending ledger) := by
  apply StatePrefixEnsures.lift _ (fun _ w _ before => ⟨w,before.1⟩)
  intro h w a value v b before run
  cases value
  exact tail_returned before.1 before.2.1 before.2.2 run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRetired
