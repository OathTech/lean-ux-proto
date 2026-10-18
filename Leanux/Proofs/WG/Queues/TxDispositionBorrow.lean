import Leanux.Proofs.Framing.PeerBorrow

/-! The strict acquisition used by TX publication derives its own positive
pre-count. This is a normal-return theorem, not totality or affiliation. -/
set_option maxHeartbeats 1000000
namespace Leanux.Proofs.Framing.PeerBorrow
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

theorem strict_acquire_spec (pid : PeerId) (initial : WGStoreView) :
    ⦃fun w => ⌜wgStoreView w = initial⌝⦄ peerGet pid
    ⦃⇓? _ w => ⌜Borrowed initial (some pid) (wgStoreView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' initialView run
  cases hd : w.dev with
  | none =>
    simp [peerGet, requireNotPending, getPeer, getDev, hd,
      invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      simp [peerGet, requireNotPending, getPeer, getDev, hd, hp,
        invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      by_cases zero : p.refcount = 0 <;>
        by_cases overflow : 2147483647 ≤ p.refcount <;>
        simp [StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
          Leanux.Proofs.WG.CounterWindow.except_ok_bind,
          Leanux.Proofs.WG.CounterWindow.except_pure, peerGet, requireNotPending,
          getPeer, getDev, setPeer, modifyDev, hd, hp, refcountInc, branch, branchCmp,
          AmbientM.branch, AmbientM.branchCmp, unsupported, AmbientM.unsupported, zero,
          overflow] at run
      all_goals try (change Except.error _ = Except.ok _ at run; cases run)
      all_goals rcases run with ⟨rfl, rfl⟩
      all_goals
        refine ⟨d, p, ?_, hp, by omega, ?_⟩
        · exact (congrArg WGStoreView.dev initialView).symm.trans hd
        · subst initial
          simp [wgStoreView, hd]

theorem strict_repaid (pid : PeerId) :
    SameView view (do peerGet pid; peerPut (some pid)) := by
  intro s
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hs hr
  have h : Hoare (do peerGet pid; peerPut (some pid))
      (fun z => wgStoreView z = wgStoreView w)
      (fun _ z => view z = view w) := by
    apply hoare_bind _ _ (strict_acquire_spec pid (wgStoreView w))
    intro _
    exact repay_spec (some pid) (wgStoreView w)
  exact ((hoare_iff_run_ambient _ _ _).mp h w ambient u v ambient' rfl hr).trans hs

end Leanux.Proofs.Framing.PeerBorrow
