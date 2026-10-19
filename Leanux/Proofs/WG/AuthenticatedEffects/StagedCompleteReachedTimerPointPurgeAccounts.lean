import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointPurge

/-! Accounted survives the charge write. After queue erasure the original
cohort is explicitly awaiting its one total receipt, not still resident. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points.Purge
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
open RetirementSecurity PeerRetirement CompleteCarrier Staged.Obligations Queues.RxCredits

theorem charge_view (device : w.dev = some d) : StagedEntry.view (charged p d w) = StagedEntry.view w := by
  unfold StagedEntry.view Packets.epoch Staged.stagedAt PacketMaterial.view Packets.snapshot
    Packets.deviceStore TxDisposition.txPackets txQueueContents handoffTxView charged
  rw [device]
  rfl

theorem charged_accounted (before : Accounted h ledger debts locals w.wg) (device : w.wg.dev = some d) :
    Accounted h ledger debts locals (state pid p d w .charged).wg :=
  before.same_view (charge_view device)

inductive Awaiting : History → World → Prop where
  | cleared (before : Accounted h ledger debts locals w.wg)
      (device : w.wg.dev = some d) (resident : d.peers[pid]? = some p) :
      Awaiting h (state pid p d w .cleared)

/-- Original entry, ordered ticket cohort, native erase cut and total receipt
suffix remain together. Settlement uses the same ledger at that receipt. -/
theorem awaiting_cut (before : Accounted h ledger debts locals w.wg)
    (device : w.wg.dev = some d) (resident : d.peers[pid]? = some p) :
    runPrefix (sourcePrefix pid .cleared) w h = (.ok ((),state pid p d w .cleared),h) ∧
    Staged.Origins.Aligned (Staged.Origins.Born h d.ifindex pid p.internalId)
      (cohort ledger pid p d) p.staged ∧
    runPrefix (suffix pid p d w .cleared) (state pid p d w .cleared) h =
      (.ok ((),state pid p d w .recorded),history pid p d w h .recorded) ∧
    Accounted (history pid p d w h .recorded)
      (settle (cohort ledger pid p d) (.counted h.length .purge) ledger) debts locals (state pid p d w .recorded).wg ∧
    Staged.Obligations.Step ledger (settle (cohort ledger pid p d) (.counted h.length .purge) ledger) :=
  ⟨prefix_run device resident .cleared,cohort_aligned before device resident,suffix_run device .cleared,
    (purge_cohort_accounted before device resident (a:=w.ambient)).1,(purge_cohort_accounted before device resident (a:=w.ambient)).2.1⟩

inductive Point (pid : PeerId) : World → History → World → History → Prop where
  | entry : Point pid w h w h
  | phase (device : w.wg.dev = some d) (resident : d.peers[pid]? = some p) (phase : Phase) :
      Point pid w h (state pid p d w phase) (history pid p d w h phase)

theorem point_evidence (before : Carrier h w) (point : Point pid w h u middle) :
    Carrier middle u ∨ Awaiting middle u := by
  cases point with
  | entry => exact Or.inl before
  | phase device resident phase =>
    obtain ⟨ledger,before⟩ := before
    cases phase with
    | read => exact Or.inl ⟨ledger,before⟩
    | charged => exact Or.inl ⟨ledger,charged_accounted before device⟩
    | cleared => exact Or.inr (.cleared before device resident)
    | recorded => exact Or.inl ⟨_,(purge_cohort_accounted before device resident (a:=w.ambient)).1⟩

theorem remainder_exists (point : Point pid w h u middle) :
    ∃ rest : PrefixM Event Unit, runPrefix (liftWGObserver (stagedPurge pid)) w h = runPrefix rest u middle := by
  cases point with
  | entry => exact ⟨_,rfl⟩
  | phase device resident phase => exact ⟨_,continuation device resident phase⟩

noncomputable def remainder (point : Point pid w h u middle) : PrefixM Event Unit :=
  Classical.choose (remainder_exists point)

theorem point_continuation (point : Point pid w h u middle) :
    runPrefix (liftWGObserver (stagedPurge pid)) w h = runPrefix (remainder point) u middle :=
  Classical.choose_spec (remainder_exists point)

theorem run_cases (pid : PeerId) (w : World) (h : History) :
    (∃ reason, ((getPeer pid).run w.wg).run w.ambient = .error reason ∧
      runPrefix (liftWGObserver (stagedPurge pid)) w h = (.error reason,h)) ∨
    (∃ d p, w.wg.dev = some d ∧ d.peers[pid]? = some p ∧
      ∀ phase, runPrefix (sourcePrefix pid phase) w h =
        (.ok ((),state pid p d w phase),history pid p d w h phase)) := by
  rcases observed_purge_cases pid w.wg w.ambient h with ⟨reason,failed,performed⟩ | ⟨d,p,device,resident,_⟩
  · exact Or.inl ⟨reason,failed,by rw [liftWGObserver_run,performed]; rfl⟩
  · exact Or.inr ⟨d,p,device,resident,prefix_run device resident⟩
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points.Purge
