import Leanux.Proofs.Framing.PeerBorrow
import Leanux.Proofs.WG.Queues.TxDispositionProjection

/-! The strict acquisition used by TX publication derives its own positive
pre-count. This is a normal-return theorem, not totality or affiliation. -/
set_option maxHeartbeats 1000000
namespace Leanux.Proofs.Framing.PeerBorrow
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

theorem strict_acquire_spec (pid : PeerId) (initial : Kernel) :
    ⦃fun w => ⌜w.k = initial⌝⦄ peerGet pid
    ⦃⇓? _ w => ⌜Borrowed initial (some pid) w.k⌝⦄ := by
  mvcgen [peerGet, requireNotPending, getPeer, getDev, getK, setPeer,
    modifyDev, modifyK, refcountInc, branchCmp, branchCmpExcluded, branch,
    invariant, unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [Borrowed]
  all_goals omega

theorem strict_repaid (pid : PeerId) :
    SameView view (do peerGet pid; peerPut (some pid)) := by
  apply SameView.of_wp
  intro s
  mvcgen [strict_acquire_spec, repay_spec]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [view]

end Leanux.Proofs.Framing.PeerBorrow
