import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNestedPeerFrames

/-! Exact continuations of the access-bearing release. Every residual keeps
the original receipt's before-state and clock, including a later Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NestedPeer
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open CausalJournal AllocatedObligation PeerRetirement

def resume (peer : Option PeerId) (origin : World) (suffix : WGPrefix Event Cached) : PrefixM Event Unit :=
  fun w=>ExceptT.mk fun h=>match runWGPrefix suffix w.wg w.ambient h with
    | (.error stop,last)=>(.error stop,last)
    | (.ok ((value,g),a),last)=>runPrefix (PeerRelease.finish value) {w with wg:=g,ambient:=a}
        (last++[PeerRelease.receipt peer value origin.wg g origin.ambient a])

theorem resume_run (peer : Option PeerId) (origin w : World) (suffix : WGPrefix Event Cached) (h : List Event) :
    runPrefix (resume peer origin suffix) w h=
      match runWGPrefix suffix w.wg w.ambient h with
      | (.error stop,last)=>(.error stop,last)
      | (.ok ((value,g),a),last)=>runPrefix (PeerRelease.finish value) {w with wg:=g,ambient:=a}
          (last++[PeerRelease.receipt peer value origin.wg g origin.ambient a]) := rfl

theorem stage_residual
    (performed : runWGPrefix (prefixAt actual stage peer) w.wg w.ambient h=(.ok ((value,v),b),middle)) :
    runPrefix (Admission.actualOps.release peer) w h=
      runPrefix (resume peer w (tail actual stage value)) {w with wg:=v,ambient:=b} middle := by
  rw [PeerRelease.actual_run,PeerRelease.cut,factor]
  simp only [runWGPrefix,runStatePrefix_bind] at performed ⊢
  rw [performed,resume_run]
  rfl

theorem cut_residual
    (performed : runWGPrefix (PeerRelease.cut peer) w.wg w.ambient h=(.ok ((value,v),b),middle)) :
    runPrefix (Admission.actualOps.release peer) w h=
      runPrefix (resume peer w (pure value)) {w with wg:=v,ambient:=b} middle := by
  rw [PeerRelease.actual_run,performed,resume_run]
  rfl

theorem finish_residual
    (cut : runWGPrefix (PeerRelease.cut peer) w.wg w.ambient h=(.ok ((some (pid,p),v),b),middle))
    (performed : ((Finish.prefixAt site pid p).run v).run b=.ok (((),u),c)) :
    runPrefix (Admission.actualOps.release peer) w h=
      runPrefix (liftPrefix (liftWG (Finish.tailAt site pid))) {w with wg:=u,ambient:=c}
        (middle++[PeerRelease.receipt peer (some (pid,p)) w.wg v w.ambient b]) := by
  rw [PeerRelease.after_cut peer cut,PeerRelease.finish_native]
  dsimp only
  rw [runPrefix_lift,liftWG_run]
  dsimp only
  rw [Finish.point_factor site,StateT.run_bind,StateT.run_bind,performed]
  rw [runPrefix_lift,liftWG_run]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NestedPeer
