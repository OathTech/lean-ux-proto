import Leanux.Proofs.Framing.PeerBorrow

/-! The strict acquisition used by TX publication derives its own positive
pre-count. This is a normal-return theorem, not totality or affiliation. -/
set_option maxHeartbeats 1000000
namespace Leanux.Proofs.Framing.PeerBorrow
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

theorem strict_acquire_spec (pid : PeerId) (initial : WGStoreView) :
    ⦃fun w => ⌜wgStoreView w = initial⌝⦄ peerGet pid
    ⦃⇓? _ w => ⌜Borrowed initial (some pid) (wgStoreView w)⌝⦄ := by
  mvcgen [peerGet, requireNotPending, getPeer, getDev, setPeer,
    modifyDev, refcountInc, branchCmp, branchCmpExcluded, branch,
    invariant, unsupported, AmbientM.branchCmp, AmbientM.branchCmpExcluded,
    AmbientM.branch, AmbientM.invariant, AmbientM.unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals subst_vars
  all_goals simp_all [Borrowed, wgStoreView]
  all_goals first
    | (refine ⟨_, _, ?_, ?_, ?_, ?_⟩ <;> first | assumption | rfl | omega)
    | omega

theorem strict_repaid (pid : PeerId) :
    SameView view (do peerGet pid; peerPut (some pid)) := by
  apply SameView.of_wp
  intro s
  mvcgen [strict_acquire_spec, repay_spec]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view]

end Leanux.Proofs.Framing.PeerBorrow
