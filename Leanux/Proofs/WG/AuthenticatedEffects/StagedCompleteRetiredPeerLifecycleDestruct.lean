import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecycleGuard

/-! The exact destructor retains its account at real completed cuts and
establishes a fresh absent-device account only after the actual reset. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders HolderDeviceCreate
set_option maxHeartbeats 600000

/-- Absence makes every native balance zero. The lower and upper bounds use
the same holder witness supplied by the native absent-device construction. -/
theorem absent_exact (w : WGWorld) (absent : w.dev=none)
    (c7 : activeCursor w.nlSock7=none) (c8 : activeCursor w.nlSock8=none) :
    ExactBoundary [] [] w ∧ OptionalPhysical w := by
  obtain ⟨⟨h,funded,stable⟩,physical⟩ := HolderDeviceDelete.absent_boundary w absent c7 c8
  refine ⟨⟨h,funded,?_,stable⟩,physical⟩
  intro owner
  simp [balance,resident,absent]

/-- Original reset suffix, separate from all earlier guards and payments. -/
def resetTail : WG.M Unit := do
  _root_.modify fun w:WGWorld=>{w with dev:=none}
  retireDeviceUnits

theorem reset_normal (before : EmptyBase [] [] w)
    (run : (resetTail.run w).run a=.ok (((),v),b)) :
    v.dev=none ∧ Clear [] [] v ∧ OptionalPhysical v := by
  change (retireDeviceUnits.run {w with dev:=none}).run a=.ok (((),v),b) at run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp retireDeviceUnits_sameWGStore
    {w with dev:=none} a () v b run
  have absent : v.dev=none := congrArg WGStoreView.dev same
  obtain ⟨_,_,_,c7,c8⟩ := before
  have out7 := (congrArg (fun s : WGStoreView=>activeCursor s.nlSock7) same).trans c7
  have out8 := (congrArg (fun s : WGStoreView=>activeCursor s.nlSock8) same).trans c8
  have post := absent_exact v absent out7 out8
  exact ⟨absent,⟨post.1,out7,out8⟩,post.2⟩

theorem destruct_normal (before : Clear [] [] w)
    (run : (wgDestruct.run w).run a=.ok (((),v),b)) :
    v.dev=none ∧ Clear [] [] v ∧ OptionalPhysical v := by
  obtain ⟨_,_,z,e,_,_,_,atReset,reset⟩ := destruct_cuts before run
  exact reset_normal atReset reset

theorem destruct : Hoare wgDestruct (Clear [] [])
    (fun _ w=>w.dev=none ∧ Clear [] [] w ∧ OptionalPhysical w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact destruct_normal before run

/-- Exact source suffix at the prepared guard entry. Its failures retain
that actual completed preparation cut rather than inventing an error state. -/
def checkedTail : WG.M Unit := do
  RetirementSecurity.TxWork.Destruct.check
  RetirementSecurity.TxWork.Destruct.settle
  resetTail

theorem destruct_factor : wgDestruct =
    (RetirementSecurity.TxWork.Destruct.prepare >>= fun _=>checkedTail) := by
  rw [RetirementSecurity.TxWork.Destruct.factor]
  simp only [RetirementSecurity.TxWork.Destruct.beforeReset,checkedTail,resetTail,bind_assoc]

/-- A stopped destructor either stops inside preparation or has a real
prepared guard entry with the same exact account and an actually stopped
suffix. No normal-return assertion is used to dismiss either failure. -/
theorem destruct_stopped (before : Clear cs loans w)
    (run : (wgDestruct.run w).run a=.error error) :
    (RetirementSecurity.TxWork.Destruct.prepare.run w).run a=.error error ∨
    ∃u c,(RetirementSecurity.TxWork.Destruct.prepare.run w).run a=.ok (((),u),c) ∧
      EmptyBase cs loans u ∧ (checkedTail.run u).run c=.error error := by
  rw [destruct_factor] at run
  cases prepared : (RetirementSecurity.TxWork.Destruct.prepare.run w).run a with
  | error err =>
    simp only [StateT.run_bind,prepared] at run
    cases run
    exact Or.inl rfl
  | ok value =>
    rcases value with ⟨⟨result,u⟩,c⟩
    cases result
    simp only [StateT.run_bind,prepared,CounterWindow.except_ok_bind] at run
    exact Or.inr ⟨u,c,rfl,(hoare_iff_run_ambient _ _ _).mp prepare w a () u c before prepared,run⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle
