import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecycleDelete

/-! Native deletion reaches the actual destructor guard with the exact
remaining account, and stopped deletion retains its last completed cut.
The physical RX witness discharges the ledger at the original idle guard. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders HolderDeviceCreate
set_option maxHeartbeats 600000

/-- The live-device branch links the product prefix, native preparation and
actual checked suffix on one execution. Empty base and inactive cursors
belong to the same holder witness as both reference-count bounds. -/
theorem delete_live_cut (before : ExactBoundary cs [] w.wg)
    (physical : OptionalPhysical w.wg) (live : w.wg.dev.isSome=true)
    (run : Env.wgDelete.run w=.ok (result,v)) :
    cs=[] ∧ result=0 ∧ HolderDeviceDelete.guards.run w=.ok ((),w) ∧
    ∃u g c,deletePrefix.run w=.ok ((),u) ∧ Clear [] [] u.wg ∧
      (RetirementSecurity.TxWork.Destruct.prepare.run u.wg).run u.ambient=.ok (((),g),c) ∧
      EmptyBase [] [] g ∧ (checkedTail.run g).run c=.ok (((),v.wg),v.ambient) := by
  rw [delete_factor,MaterialOrigin.bind_ok] at run
  obtain ⟨ignored,middle,guard,rest⟩ := run
  cases ignored
  obtain ⟨same,empty,ready⟩ := delete_guards before physical guard
  subst middle
  subst cs
  have noAbsent : w.wg.dev.isNone=false := by
    cases found:w.wg.dev <;> simp_all
  simp only [StateT.run_bind,
    show (getWG : Leanux.M WGWorld).run w=.ok (w.wg,w) from rfl,
    CounterWindow.except_ok_bind,noAbsent,Bool.false_eq_true,ite_false] at rest
  change ((deletePrefix >>= fun _=>liftWG wgDestruct >>= fun _=>pure 0).run w)=.ok (result,v) at rest
  rw [MaterialOrigin.bind_ok] at rest
  obtain ⟨ignored,u,frontRun,rest⟩ := rest
  cases ignored
  have atDrop := (hoare_iff_run _ _ _).mp delete_prefix w () u ready frontRun
  rw [MaterialOrigin.bind_ok] at rest
  obtain ⟨ignored,z,dropped,returned⟩ := rest
  cases ignored
  cases returned
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    wgDestruct u v () dropped
  rw [destruct_factor,MaterialOrigin.bind_ok_ambient] at native
  obtain ⟨ignored,g,c,prepared,tail⟩ := native
  cases ignored
  exact ⟨rfl,rfl,guard,u,g,c,frontRun,atDrop,prepared,
    (hoare_iff_run_ambient _ _ _).mp prepare u.wg u.ambient () g c atDrop prepared,tail⟩

/-- A failed deletion is charged to an actual failed source prefix, or to
native destruction after a completed prefix carrying the exact account.
No stopped native world is manufactured. -/
theorem delete_stopped (before : ExactBoundary cs [] w.wg)
    (physical : OptionalPhysical w.wg) (run : Env.wgDelete.run w=.error error) :
    HolderDeviceDelete.guards.run w=.error error ∨
    (cs=[] ∧ HolderDeviceDelete.guards.run w=.ok ((),w) ∧
      (deletePrefix.run w=.error error ∨
        ∃u,deletePrefix.run w=.ok ((),u) ∧ Clear [] [] u.wg ∧
          (liftWG wgDestruct).run u=.error error)) := by
  rw [delete_factor] at run
  cases guarded : HolderDeviceDelete.guards.run w with
  | error err =>
    simp only [StateT.run_bind,guarded] at run
    cases run
    exact Or.inl rfl
  | ok value =>
    rcases value with ⟨ignored,middle⟩
    cases ignored
    have facts := delete_guards before physical guarded
    obtain ⟨same,empty,ready⟩ := facts
    subst middle
    subst cs
    simp only [StateT.run_bind,guarded,
      show (getWG : Leanux.M WGWorld).run w=.ok (w.wg,w) from rfl,
      CounterWindow.except_ok_bind] at run
    split at run
    · cases run
    · apply Or.inr
      refine ⟨rfl,rfl,?_⟩
      cases frontRun : deletePrefix.run w with
      | error err =>
        simp only [StateT.run_bind,frontRun] at run
        cases run
        exact Or.inl rfl
      | ok value =>
        rcases value with ⟨ignored,u⟩
        cases ignored
        simp only [StateT.run_bind,frontRun,CounterWindow.except_ok_bind] at run
        have atDrop := (hoare_iff_run _ _ _).mp delete_prefix w () u ready frontRun
        cases dropped : (liftWG wgDestruct).run u with
        | error err =>
          simp only [dropped] at run
          cases run
          exact Or.inr ⟨u,rfl,atDrop,dropped⟩
        | ok value =>
          rcases value with ⟨ignored,v⟩
          cases ignored
          simp only [dropped,CounterWindow.except_ok_bind] at run
          cases run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Lifecycle
