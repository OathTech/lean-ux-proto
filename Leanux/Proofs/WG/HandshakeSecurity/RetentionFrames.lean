import Leanux.Proofs.WG.HandshakeSecurity.Projection
import Leanux.Proofs.WG.Peers.Primitives

/-! Reference cleanup may delete a peer. Every surviving handshake projection
is retained; no whole-world silence premise is used. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Peers

def RetainsHandshake (before after : WGWorld) : Prop :=
  ∀ pid view, peerView after pid = some view → peerView before pid = some view

theorem peerPut_retains_handshake (i : Option PeerId) (w v : WGWorld)
    (a b : Ambient) (result : Unit)
    (run : ((peerPut i).run w).run a = .ok ((result, v), b)) :
    RetainsHandshake w v := by
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
              | solve | simp [peerView] at found
              | simpa [peerView, hd, hp, handshakeView] using found
            · simpa [peerView, hd, Std.TreeMap.getElem?_insert,
                Std.TreeMap.getElem?_erase, same, Ne.symm same] using found
        · have zero : p.refcount = 0 := by omega
          simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
            refcountDecAndTest, branch, branchCmp, CounterWindow.branch_run,
            CounterWindow.branchCmp_run, hd, hp, zero,
            StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
            CounterWindow.except_ok_bind, CounterWindow.except_pure,
            unsupported, AmbientM.unsupported] at run
          cases run

end Leanux.Proofs.WG.HandshakeSecurity
