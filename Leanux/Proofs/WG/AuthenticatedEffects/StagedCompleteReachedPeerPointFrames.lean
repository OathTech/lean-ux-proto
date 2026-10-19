import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointSource

/-! Packet-projection frames for each native stage before final erasure.
Reference and index writes retain the same ordered packet ownership. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
open Leanux Leanux.WG Leanux.Proofs.Logged
open CausalJournal HandshakeSecurity.StagedDisposal CompleteCarrier TransmitSecurity Lifetimes Queues
set_option maxHeartbeats 800000

theorem decrement_view (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    StagedEntry.view (decremented pid p d w)=StagedEntry.view w :=
  Queued.replace_peer device resident rfl rfl rfl

theorem unlink_view (device : w.dev=some d) :
    StagedEntry.view (unlinked pid d w)=StagedEntry.view w := by
  change StagedEntry.view {w with dev:=some d}=StagedEntry.view w
  rw [←device]

theorem index_view (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    StagedEntry.view (indexWorld pid p d w)=StagedEntry.view w :=
  (unlink_view (pid:=pid) (d:=decDevice pid p d) (w:=decremented pid p d w) rfl).trans
    (decrement_view device resident)

/-- All completed pre-erasure prefixes preserve the complete packet view.
A failed test/guard provides no synthetic returned world. -/
theorem Stage.view {stage : Stage} {value : stage.Result}
    (performed : ((stage.prefix peer).run w).run a=.ok ((value,v),b)) :
    StagedEntry.view v=StagedEntry.view w := by
  cases peer with
  | none =>
    cases stage <;>
      simp [Stage.prefix,checkedTo,unlinkTo,testTo,decrementTo,readRelease,
        branch,AmbientM.branch] at performed <;>
      rcases performed with ⟨⟨rfl,rfl⟩,rfl⟩ <;> rfl
  | some pid =>
    cases device : w.dev with
    | none =>
      cases stage <;>
        simp [Stage.prefix,checkedTo,unlinkTo,testTo,decrementTo,readRelease,
          branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at performed <;>
        cases performed
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        cases stage <;>
          simp [Stage.prefix,checkedTo,unlinkTo,testTo,decrementTo,readRelease,
            branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at performed <;>
          cases performed
      | some p =>
        cases stage with
        | read =>
          change ((readRelease (some pid)).run w).run a=_ at performed
          rw [read_some device resident] at performed
          cases performed
          rfl
        | decrement =>
          change ((decrementTo (some pid)).run w).run a=_ at performed
          rw [decrement_prefix device resident] at performed
          cases performed
          exact decrement_view device resident
        | test =>
          change ((testTo (some pid)).run w).run a=_ at performed
          rw [test_prefix device resident] at performed
          cases tested : (testAmbient p.refcount).run (entryClock a) with
          | error stop => simp only [tested,Except.map] at performed; cases performed
          | ok out =>
            obtain ⟨final,c⟩ := out
            simp only [tested,Except.map] at performed
            cases performed
            exact decrement_view device resident
        | unlink =>
          change ((unlinkTo (some pid)).run w).run a=_ at performed
          simp only [unlinkTo,StateT.run_bind,test_prefix device resident] at performed
          cases tested : (testAmbient p.refcount).run (entryClock a) with
          | error stop => simp only [tested,Except.map] at performed; cases performed
          | ok out =>
            obtain ⟨final,c⟩ := out
            cases final with
            | false =>
              simp only [tested,Except.map] at performed
              cases performed
              exact decrement_view device resident
            | true =>
              have performed' := unlink_prefix device resident tested
              unfold unlinkTo at performed'
              simp only [StateT.run_bind,test_prefix device resident,tested,Except.map] at performed'
              simp only [tested,Except.map] at performed
              rw [performed'] at performed
              cases performed
              exact index_view device resident

        | checked =>
          change ((checkedTo (some pid)).run w).run a=_ at performed
          unfold checkedTo at performed
          rw [MaterialOrigin.bind_ok_ambient] at performed
          obtain ⟨cached,u,c,leading,rest⟩ := performed
          have same := Stage.view (stage:=.unlink) leading
          cases cached with
          | none => cases rest; exact same
          | some pair =>
            obtain ⟨q,r⟩ := pair
            change ((do queueGuard r; pure (some (q,r)) : WG.M Cached).run u).run c=_ at rest
            simp only [StateT.run_bind,guard_run] at rest
            cases busy : queued r <;> simp only [busy,Bool.false_eq_true,ite_false,ite_true] at rest
            · cases rest; exact same
            · cases rest
termination_by match stage with | .checked => 1 | _ => 0
decreasing_by all_goals simp_all

theorem Stage.accounted {stage : Stage} {value : stage.Result}
    (before : Accounted h ledger debts locals w)
    (performed : ((stage.prefix peer).run w).run a=.ok ((value,v),b)) :
    Accounted h ledger debts locals v :=
  ⟨before.entry.same_view (Stage.view performed),before.complete⟩

/-- A normal finish prefix preserves the successor ledger already established
by the actual release receipt, across both identity-retirement writes. -/
theorem finish_accounted (before : Accounted h ledger debts locals w)
    (performed : ((Finish.prefixAt site pid p).run w).run a=.ok (((),v),b)) :
    Accounted h ledger debts locals v := by
  cases found : Finish.pending p with
  | some timer =>
    cases site <;>
      simp only [Finish.prefixAt,StateT.run_bind,Finish.guard_stopped found] at performed <;>
      cases performed
  | none =>
    rw [Finish.prefix_run found] at performed
    cases performed
    exact Finish.prefix_accounted before site

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
