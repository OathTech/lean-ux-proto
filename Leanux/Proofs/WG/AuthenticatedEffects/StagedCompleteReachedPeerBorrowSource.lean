import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAccessCanonical

/-! Strict peer acquisition keeps its actual read and refcount check before the single saved-peer write. Its points retain the native continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerBorrowAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def front (pid : PeerId) : WG.M Peer := do
  requireNotPending pid "a reference count the handshake worker also changes"
  let p ← getPeer pid
  refcountInc p.refcount
  pure p

theorem source (pid : PeerId) : peerGet pid=(front pid >>= fun p=>setPeer pid {p with refcount:=p.refcount+1}) := by
  simp only [peerGet,front,bind_assoc,pure_bind]

noncomputable def frontShape (pid : PeerId) : Access.Shape (front pid) := by
  simp only [front,requireNotPending,getPeer,getDev,invariant]
  repeat' access_source_step

inductive Point (pid : PeerId) : WGWorld → Ambient → WGWorld → Ambient → Prop where
  | front (point : Access.Point (frontShape pid) w a v b) : Point pid w a v b
  | returned (performed : ((peerGet pid).run w).run a=.ok ((value,v),b)) : Point pid w a v b

theorem Point.remaining (point : Point pid w a v b) :
    ∃remaining : WG.M Unit,((peerGet pid).run w).run a=(remaining.run v).run b := by
  cases point with
  | front point=>
      obtain ⟨rest,same⟩:=point.remaining
      exact ⟨rest >>= fun p=>setPeer pid {p with refcount:=p.refcount+1},by rw [source];simp only [StateT.run_bind,same]⟩
  | returned performed=>exact ⟨pure _,performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerBorrowAccess
