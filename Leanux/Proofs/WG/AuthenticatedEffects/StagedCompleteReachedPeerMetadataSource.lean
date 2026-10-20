import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSavedPeerSource

/-! Metadata update points retain the actual peer read, its following write and the continuation using that saved peer. The fixed syntax permits no arbitrary action factorization. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def readShape (pid : PeerId) : Access.Shape (getPeer pid) := by
  simp only [getPeer,getDev,invariant]
  repeat' access_source_step

inductive Shape : {α : Type} → WG.M α → Type 1 where
  | access (source : Access.Shape action) : Shape action
  | saved (pid : PeerId) (next : Peer → WG.M α)
      (tail : ∀p,SavedPeer.Shape pid p (next p)) : Shape (getPeer pid >>= next)
  | update (pid : PeerId) (f : Peer → Peer) (next : Peer → WG.M α)
      (same : ∀p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue)
      (tail : ∀p,Shape (next p)) :
      Shape (getPeer pid >>= fun p=>setPeer pid (f p) >>= fun _=>next p)
  | bind {body : WG.M α} {next : α → WG.M β} (head : Shape body) (tail : ∀value,Shape (next value)) : Shape (body >>= next)

inductive Point : {α : Type} → {action : WG.M α} → Shape action →
    WGWorld → Ambient → WGWorld → Ambient → Prop where
  | entry (source : Shape action) : Point source w a w a
  | returned (source : Shape action) (performed : ((action.run w).run a)=.ok ((value,v),b)) : Point source w a v b
  | access (point : Access.Point source w a v b) : Point (.access source) w a v b
  | savedReading (tail : ∀p,SavedPeer.Shape pid p (next p))
      (point : Access.Point (readShape pid) w a v b) : Point (.saved pid next tail) w a v b
  | savedBody (tail : ∀p,SavedPeer.Shape pid p (next p))
      (read : ((getPeer pid).run w).run a=.ok ((p,u),c))
      (point : SavedPeer.Point (tail p) u c v b) : Point (.saved pid next tail) w a v b
  | reading (same : ∀p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue)
      (tail : ∀p,Shape (next p)) (point : Access.Point (readShape pid) w a v b) :
      Point (.update pid f next same tail) w a v b
  | written (same : ∀p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue)
      (tail : ∀p,Shape (next p))
      (read : ((getPeer pid).run w).run a=.ok ((p,u),c))
      (write : ((setPeer pid (f p)).run u).run c=.ok (((),v),b)) :
      Point (.update pid f next same tail) w a v b
  | continued (same : ∀p,(f p).internalId=p.internalId ∧ (f p).staged=p.staged ∧ (f p).txQueue=p.txQueue)
      (tail : ∀p,Shape (next p))
      (read : ((getPeer pid).run w).run a=.ok ((p,u),c))
      (write : ((setPeer pid (f p)).run u).run c=.ok (((),x),ax))
      (point : Point (tail p) x ax v b) : Point (.update pid f next same tail) w a v b
  | left {body : WG.M α} {next : α → WG.M β} {head : Shape body}
      (tail : ∀value,Shape (next value)) (point : Point head w a v b) : Point (.bind head tail) w a v b
  | right {body : WG.M α} {next : α → WG.M β} (head : Shape body) (tail : ∀value,Shape (next value))
      (leading : ((body.run w).run a)=.ok ((value,u),c)) (point : Point (tail value) u c v b) :
      Point (.bind head tail) w a v b

theorem update_run {f : Peer → Peer} (read : ((getPeer pid).run w).run a=.ok ((p,u),c))
    (write : ((setPeer pid (f p)).run u).run c=.ok (((),v),b)) :
    (((getPeer pid >>= fun p=>setPeer pid (f p)).run w).run a)=.ok (((),v),b) := by
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨p,u,c,read,write⟩

theorem Point.remaining {α : Type} {action : WG.M α} {source : Shape action}
    (point : Point source w a v b) : ∃remaining : WG.M α,((action.run w).run a)=((remaining.run v).run b) := by
  induction point with
  | entry source=>exact ⟨_,rfl⟩
  | returned source performed=>exact ⟨pure _,performed⟩
  | access point=>exact point.remaining
  | @savedReading α pid next w a v b tail point=>
      obtain ⟨rest,same⟩:=point.remaining
      exact ⟨rest >>= next,by simp only [StateT.run_bind,same]⟩
  | savedBody tail read point=>
      obtain ⟨rest,same⟩:=point.remaining
      exact ⟨rest,by simp only [StateT.run_bind,read];exact same⟩
  | @reading α f next pid w a v b same tail point=>
      obtain ⟨rest,run⟩:=point.remaining
      refine ⟨rest >>= fun p=>setPeer pid (f p) >>= fun _=>next p,?_⟩
      simp only [StateT.run_bind,run]
  | @written α f next pid w a p u c v b same tail read write=>
      refine ⟨next p,?_⟩
      simp only [StateT.run_bind,read]
      change ((setPeer pid (f p) >>= fun _=>next p).run u).run c=_
      simp only [StateT.run_bind,write]
      rfl
  | @continued α f next pid w a p u c x ax v b same tail read write point ih=>
      obtain ⟨rest,run⟩:=ih
      refine ⟨rest,?_⟩
      simp only [StateT.run_bind,read]
      change ((setPeer pid (f p) >>= fun _=>next p).run u).run c=_
      simp only [StateT.run_bind,write]
      exact run
  | @left α β w a v b body next head tail point ih=>
      obtain ⟨rest,same⟩:=ih
      exact ⟨rest >>= next,by simp only [StateT.run_bind,same]⟩
  | right head tail leading point ih=>
      obtain ⟨rest,same⟩:=ih
      exact ⟨rest,by simp only [StateT.run_bind,leading];exact same⟩

theorem Point.observed_remaining {α E : Type} {action : WG.M α} {source : Shape action}
    {w : World} (point : Point source w.wg w.ambient v b) (h : List E) :
    ∃remaining : PrefixM E α,runPrefix (liftWGObserver (liftWGPrefix action)) w h=
      runPrefix remaining {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  simp only [liftWGObserver_run,runWGPrefix_lift,same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
