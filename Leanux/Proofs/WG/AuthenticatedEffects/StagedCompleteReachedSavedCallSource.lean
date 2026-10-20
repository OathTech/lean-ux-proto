import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReadAccessSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSavedPeerSource

namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SavedCall
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

/-- The original read supplies the resident peer used by every later write. -/
inductive Point (pid : PeerId) (next : Peer → WG.M α)
    (source : ∀p,SavedPeer.Shape pid p (next p)) : WGWorld → Ambient → WGWorld → Ambient → Prop where
  | reading (point : ReadAccess.Point (ReadAccess.peerShape pid) w a v b) : Point pid next source w a v b
  | body (read : ((getPeer pid).run w).run a=.ok ((p,u),c))
      (point : SavedPeer.Point (source p) u c v b) : Point pid next source w a v b

theorem Point.remaining {α : Type} {next : Peer → WG.M α}
    {source : ∀p,SavedPeer.Shape pid p (next p)} (point : Point pid next source w a v b) :
    ∃rest : WG.M α,((getPeer pid >>= next).run w).run a=(rest.run v).run b := by
  cases point with
  | reading point =>
      obtain ⟨rest,same⟩:=point.remaining
      exact ⟨rest >>= next,by simp only [StateT.run_bind,same]⟩
  | body read point =>
      obtain ⟨rest,same⟩:=point.remaining
      exact ⟨rest,by simp only [StateT.run_bind,read];exact same⟩

theorem Point.lifted_remaining {α E : Type} {next : Peer → WG.M α}
    {source : ∀p,SavedPeer.Shape pid p (next p)} {w : World}
    (point : Point pid next source w.wg w.ambient v b) (h : List E) :
    ∃rest : PrefixM E α,runPrefix (liftPrefix (liftWG (getPeer pid >>= next))) w h=
      runPrefix rest {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  rw [←liftWGObserver_lift]
  simp only [liftWGObserver_run,runWGPrefix_lift,same]

def deleteBody (pid : PeerId) (timer : PeerTimer) (p : Peer) : WG.M Unit :=
  setPeer pid ((p.setTimer timer none).setWheel timer none)

noncomputable def deleteShape (pid : PeerId) (timer : PeerTimer) (p : Peer) :
    SavedPeer.Shape pid p (deleteBody pid timer p) := by
  apply SavedPeer.Shape.write
  cases timer <;> exact ⟨rfl,rfl,rfl⟩

theorem delete_source (pid : PeerId) (timer : PeerTimer) :
    delTimer pid timer=(getPeer pid >>= deleteBody pid timer) := rfl

def acquireBody (pid : PeerId) (p : Peer) : WG.M Unit := do
  refcountInc p.refcount
  setPeer pid {p with refcount:=p.refcount+1}

noncomputable def acquireShape (pid : PeerId) (p : Peer) : SavedPeer.Shape pid p (acquireBody pid p) := by
  unfold acquireBody
  repeat' saved_peer_source_step

theorem acquire_source (pid : PeerId) : peerGet pid=(getPeer pid >>= acquireBody pid) := by
  simp only [peerGet,requireNotPending,pure_bind]
  rfl

abbrev DeletePoint (pid : PeerId) (timer : PeerTimer) := Point pid (deleteBody pid timer) (deleteShape pid timer)
abbrev AcquirePoint (pid : PeerId) := Point pid (acquireBody pid) (acquireShape pid)

noncomputable def deleteRemainder {w : World} (h : List Event)
    (point : DeletePoint pid timer w.wg w.ambient v b) : PrefixM Event Unit :=
  Classical.choose (point.lifted_remaining h)

noncomputable def acquireRemainder {w : World} (h : List Event)
    (point : AcquirePoint pid w.wg w.ambient v b) : PrefixM Event Unit :=
  Classical.choose (point.lifted_remaining h)

theorem deleteRemainder_run {w : World} (h : List Event) (point : DeletePoint pid timer w.wg w.ambient v b) :
    runPrefix (liftPrefix (liftWG (delTimer pid timer))) w h=
      runPrefix (deleteRemainder h point) {w with wg:=v,ambient:=b} h := by
  rw [delete_source]
  exact Classical.choose_spec (point.lifted_remaining h)

theorem acquireRemainder_run {w : World} (h : List Event) (point : AcquirePoint pid w.wg w.ambient v b) :
    runPrefix (liftPrefix (liftWG (peerGet pid))) w h=
      runPrefix (acquireRemainder h point) {w with wg:=v,ambient:=b} h := by
  rw [acquire_source]
  exact Classical.choose_spec (point.lifted_remaining h)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SavedCall
