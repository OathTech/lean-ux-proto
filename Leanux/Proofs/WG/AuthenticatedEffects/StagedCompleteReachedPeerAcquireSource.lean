import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAccessCanonical

/-! The maybe-zero peer acquisition saves its actual read peer before the
single reference write. Front points and the write retain the native suffix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerAcquire
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def front (peer : Option PeerId) : WG.M (Option (PeerId × Peer)) := do
  if ← branch .peerGetMaybeZeroNull peer.isNone then return none
  let some pid := peer | invariant "unreachable"
  requireNotPending pid "a reference count the handshake worker also changes"
  let p ← getPeer pid
  let live ← refcountIncNotZero p.refcount
  if ← branch .peerGetMaybeZeroDead !live then return none
  return some (pid,p)

def finish : Option (PeerId × Peer) → WG.M (Option PeerId)
  | none=>pure none
  | some (pid,p)=>do
      setPeer pid {p with refcount:=p.refcount+1}
      pure (some pid)

theorem source (peer : Option PeerId) : peerGetMaybeZero peer=(front peer >>= finish) := by
  cases peer <;> simp only [peerGetMaybeZero,front,Option.isNone,bind_assoc]
  all_goals repeat' first
    | rfl
    | apply RxWorkers.bind_congr
    | maintenance_intro
    | split
    | dsimp (config := {failIfUnchanged := true}) only [finish]
    | simp (config := {failIfUnchanged := true}) only [pure_bind]
    | simp (config := {failIfUnchanged := true}) only [bind_assoc]

noncomputable def frontShape (peer : Option PeerId) : Access.Shape (front peer) := by
  simp only [front,requireNotPending,getPeer,getDev,branch,invariant]
  repeat' access_source_step

inductive Point (peer : Option PeerId) : WGWorld → Ambient → WGWorld → Ambient → Prop where
  | front (point : Access.Point (frontShape peer) w a v b) : Point peer w a v b
  | written (prepared : ((front peer).run w).run a=.ok ((some (pid,p),u),c))
      (written : ((setPeer pid {p with refcount:=p.refcount+1}).run u).run c=.ok (((),v),b)) : Point peer w a v b
  | returned (performed : ((peerGetMaybeZero peer).run w).run a=.ok ((value,v),b)) : Point peer w a v b

theorem written_return
    (prepared : ((front peer).run w).run a=.ok ((some (pid,p),u),c))
    (written : ((setPeer pid {p with refcount:=p.refcount+1}).run u).run c=.ok (((),v),b)) :
    ((peerGetMaybeZero peer).run w).run a=.ok ((some pid,v),b) := by
  rw [source,MaterialOrigin.bind_ok_ambient]
  refine ⟨_,_,_,prepared,?_⟩
  change (((setPeer pid {p with refcount:=p.refcount+1} >>= fun _=>pure (some pid)).run u).run c)=_
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨(),v,b,written,rfl⟩

theorem Point.remaining (point : Point peer w a v b) :
    ∃remaining : WG.M (Option PeerId),((peerGetMaybeZero peer).run w).run a=(remaining.run v).run b := by
  cases point with
  | front point=>
      obtain ⟨rest,same⟩:=point.remaining
      exact ⟨rest >>= finish,by rw [source];simp only [StateT.run_bind,same]⟩
  | written prepared written=>exact ⟨pure _,written_return prepared written⟩
  | returned performed=>exact ⟨pure _,performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerAcquire
