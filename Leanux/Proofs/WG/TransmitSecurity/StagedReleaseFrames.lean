import Leanux.Proofs.WG.TransmitSecurity.StagedFrames

/-! Surviving staged queues retain their exact ordered contents through native
reference acquisition and release. Deletion is permitted here; its counted
purge is accounted for separately. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Peers

theorem peerPut_retains (i : Option PeerId) (w v : WGWorld)
    (a b : Ambient) (result : Unit)
    (run : ((peerPut i).run w).run a = .ok ((result, v), b)) :
    Retains w v := by
  cases i with
  | none =>
    simp [peerPut, branch, AmbientM.branch] at run
    rcases run with ⟨rfl, rfl⟩
    exact fun _ _ h => h
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerPut, requireNotPending, getPeer, getDev, hd, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerPut, requireNotPending, getPeer, getDev, hd, hp, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        have hl (action : IndexM Unit) : (liftM action : WG.M Unit) = liftIndex action := rfl
        by_cases positive : 0 < p.refcount
        · have nonzero : p.refcount ≠ 0 := by omega
          by_cases final : p.refcount = 1
          all_goals
            simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
              refcountDecAndTest, branch, branchCmp, indexRemove_eq, indexUnhash,
              hl, liftIndex_run, retirePeerUnits, modifyAmbient,
              CounterWindow.branch_run, CounterWindow.branchCmp_run,
              hd, hp, positive, nonzero, final,
              StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
              CounterWindow.except_ok_bind, CounterWindow.except_pure,
              invariant, AmbientM.invariant, unsupported, AmbientM.unsupported] at run
          all_goals repeat' first | split at run | contradiction
          all_goals rcases run with ⟨rfl, rfl⟩
          all_goals
            intro target view found
            by_cases same : pid = target
            · subst target
              first
              | solve | simp [stagedAt] at found
              | simpa [stagedAt, hd, hp] using found
            · simpa [stagedAt, hd, Std.TreeMap.getElem?_insert,
                Std.TreeMap.getElem?_erase, same, Ne.symm same] using found
        · have zero : p.refcount = 0 := by omega
          simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
            refcountDecAndTest, branch, branchCmp, CounterWindow.branch_run,
            CounterWindow.branchCmp_run, hd, hp, zero,
            StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
            CounterWindow.except_ok_bind, CounterWindow.except_pure,
            unsupported, AmbientM.unsupported] at run
          cases run

theorem peerGetMaybeZero_retains (peer : Option PeerId) (w v : WGWorld)
    (a b : Ambient) (result : Option PeerId)
    (run : ((peerGetMaybeZero peer).run w).run a = .ok ((result, v), b)) :
    Retains w v := by
  cases peer with
  | none =>
    simp [peerGetMaybeZero, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact .refl _
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, hd, branch,
        AmbientM.branch, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, hd, hp,
          branch, AmbientM.branch, invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases zero : p.refcount = 0 <;> by_cases overflow : 2147483647 ≤ p.refcount <;>
          simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, setPeer, modifyDev,
            refcountIncNotZero, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
            hd, hp, zero, overflow, unsupported, AmbientM.unsupported] at run
        all_goals try solve | cases run
        all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        all_goals first
          | exact .refl _
          | intro target view found
            by_cases same : pid = target
            · subst target
              simpa [stagedAt, hd, hp] using found
            · simpa [stagedAt, hd, Std.TreeMap.getElem?_insert, same] using found


end Leanux.Proofs.WG.TransmitSecurity.Staged
