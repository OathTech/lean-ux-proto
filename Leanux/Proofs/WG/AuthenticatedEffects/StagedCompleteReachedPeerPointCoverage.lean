import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointAccounts

/-! Unconditional source decomposition at all fixed peer-release stages.
Normal and stopped invocations use the same source family and entry ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
open Leanux Leanux.WG Leanux.Proofs.Logged
open CausalJournal HandshakeSecurity.StagedDisposal CompleteCarrier

theorem Stage.stopped {stage : Stage}
    (failed : ((stage.prefix peer).run w).run a=.error stop) :
    runWGPrefix (CausalJournal.peerRelease peer) w a h=(.error stop,h) := by
  apply release_stopped
  rw [stage.factor,StateT.run_bind,StateT.run_bind,failed]
  rfl

/-- Every actual source-stage outcome either stops the original observer
at that prefix or supplies its actual point, account and continuation. -/
theorem stage_cases (before : Accounted h ledger debts locals w) (stage : Stage) :
    match ((stage.prefix peer).run w).run a with
    | .error stop => runWGPrefix (CausalJournal.peerRelease peer) w a h=(.error stop,h)
    | .ok ((value,v),b) =>
        Evidence ledger debts locals h v ∧
        runWGPrefix (CausalJournal.peerRelease peer) w a h=
          runWGPrefix (remaining peer w a (stage.tail value)) v b h := by
  cases performed : ((stage.prefix peer).run w).run a with
  | error stop => exact Stage.stopped performed
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    exact ⟨Point.evidence before (.native stage value performed),native_continuation performed⟩

theorem Finish.prefix_stopped
    (failed : ((Finish.prefixAt site pid p).run w).run a=.error stop) :
    ((releaseFinish pid p).run w).run a=.error stop := by
  rw [Finish.point_factor site,StateT.run_bind,StateT.run_bind,failed]
  rfl

/-- All three post-receipt cuts keep the same actual receipt. A timer guard
failure keeps that history and supplies no fictitious returned world. -/
theorem finish_cases (before : Accounted h ledger debts locals w)
    (native : ((releaseCut peer).run w).run a=.ok ((some (pid,p),v),b))
    (site : Finish.Site) :
    let recorded := h++[releaseEvent peer (some (pid,p)) w v a b]
    match ((Finish.prefixAt site pid p).run v).run b with
    | .error stop => runWGPrefix (CausalJournal.peerRelease peer) w a h=(.error stop,recorded)
    | .ok (((),u),c) =>
        Evidence ledger debts locals recorded u ∧
        runWGPrefix (CausalJournal.peerRelease peer) w a h=
          runWGPrefix (liftWGPrefix (Finish.tailAt site pid)) u c recorded := by
  dsimp only
  cases performed : ((Finish.prefixAt site pid p).run v).run b with
  | error stop => rw [release_recorded native,Finish.prefix_stopped performed]
  | ok out =>
    obtain ⟨⟨value,u⟩,c⟩ := out
    cases value
    exact ⟨Point.evidence before (.finish pid p site native performed),
      Finish.release_continuation native performed⟩

/-- The actual complete observer is classified before selecting any point.
Its native erasure always supplies the exact successor account, even when
releaseFinish subsequently fails. The fixed stages cover every native
packet-projection mutation of this release source. -/
theorem source_cases (before : Accounted h ledger debts locals w) :
    ObservedRelease peer w a h (runWGPrefix (CausalJournal.peerRelease peer) w a h) ∧
    (∀ stage : Stage,
      match ((stage.prefix peer).run w).run a with
      | .error stop => runWGPrefix (CausalJournal.peerRelease peer) w a h=(.error stop,h)
      | .ok ((value,v),b) => Evidence ledger debts locals h v ∧
          runWGPrefix (CausalJournal.peerRelease peer) w a h=
            runWGPrefix (remaining peer w a (stage.tail value)) v b h) ∧
    (∀ value v b, ((releaseCut peer).run w).run a=.ok ((value,v),b) →
      Evidence ledger debts locals h v ∧
      AccountAt ledger debts locals (h++[releaseEvent peer value w v a b]) v) := by
  refine ⟨observed_release_cases peer w a h,stage_cases before,?_⟩
  intro value v b native
  exact ⟨Point.evidence before (.erased value native),native_account before native⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
