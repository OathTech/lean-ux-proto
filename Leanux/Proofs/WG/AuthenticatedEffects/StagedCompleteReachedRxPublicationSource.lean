import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRxAccessCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerBorrowSource

/-! Receive publication source cuts expose peer resolution, strict acquisition, the queue-membership guard and RX state write before the saved-peer publication write. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxPublicationAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def resolve (skb : SkbId) : WG.M PeerId := do
  IndexOwner.peerDeref (.keypair (← getRxSkb skb).keypair)

def prepare (skb : SkbId) (state : PacketState) (pid : PeerId) : WG.M Peer := do
  let p ← getPeer pid
  if !(p.rxQueue.all.contains skb) then invariant "a decrypted packet that is not on its peer's rx_queue"
  setRxSkb skb fun q=>{q with state}
  pure p

def finish (pid : PeerId) (p : Peer) : WG.M PeerId := do
  setPeer pid {p with napiScheduled:=true}
  pure pid

def tail (skb : SkbId) (state : PacketState) (pid : PeerId) : WG.M PeerId := do
  peerGet pid
  prepare skb state pid >>= finish pid

theorem source (skb : SkbId) (state : PacketState) :
    RxWorkers.publishSource skb state=(resolve skb >>= tail skb state) := by
  simp only [RxWorkers.publishSource,resolve,bind_assoc]
  repeat' first
    | rfl
    | apply RxWorkers.bind_congr
    | maintenance_intro
    | split
    | dsimp (config := {failIfUnchanged := true}) only [tail,prepare,finish]
    | simp (config := {failIfUnchanged := true}) only [pure_bind]
    | simp (config := {failIfUnchanged := true}) only [bind_assoc]

noncomputable def resolveShape (skb : SkbId) : RxAccess.Shape (resolve skb) := by
  simp only [resolve,IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,invariant,unsupported]
  repeat' rx_access_source_step

noncomputable def prepareShape (skb : SkbId) (state : PacketState) (pid : PeerId) :
    RxAccess.Shape (prepare skb state pid) := by
  simp only [prepare,getPeer,getDev,invariant]
  repeat' rx_access_source_step

inductive Point (skb : SkbId) (state : PacketState) : WGWorld → Ambient → WGWorld → Ambient → Prop where
  | resolving (point : RxAccess.Point (resolveShape skb) w a v b) : Point skb state w a v b
  | borrowing (resolved : ((resolve skb).run w).run a=.ok ((pid,u),c))
      (point : PeerBorrowAccess.Point pid u c v b) : Point skb state w a v b
  | preparing (resolved : ((resolve skb).run w).run a=.ok ((pid,u),c))
      (borrowed : ((peerGet pid).run u).run c=.ok (((),x),ax))
      (point : RxAccess.Point (prepareShape skb state pid) x ax v b) : Point skb state w a v b
  | written (resolved : ((resolve skb).run w).run a=.ok ((pid,u),c))
      (borrowed : ((peerGet pid).run u).run c=.ok (((),x),ax))
      (prepared : ((prepare skb state pid).run x).run ax=.ok ((p,y),ay))
      (written : ((setPeer pid {p with napiScheduled:=true}).run y).run ay=.ok (((),v),b)) : Point skb state w a v b
  | returned (performed : ((RxWorkers.publishSource skb state).run w).run a=.ok ((value,v),b)) : Point skb state w a v b

theorem written_return
    (resolved : ((resolve skb).run w).run a=.ok ((pid,u),c))
    (borrowed : ((peerGet pid).run u).run c=.ok (((),x),ax))
    (prepared : ((prepare skb state pid).run x).run ax=.ok ((p,y),ay))
    (written : ((setPeer pid {p with napiScheduled:=true}).run y).run ay=.ok (((),v),b)) :
    ((RxWorkers.publishSource skb state).run w).run a=.ok ((pid,v),b) := by
  rw [source,MaterialOrigin.bind_ok_ambient]
  refine ⟨pid,u,c,resolved,?_⟩
  unfold tail
  rw [MaterialOrigin.bind_ok_ambient]
  refine ⟨(),x,ax,borrowed,?_⟩
  rw [MaterialOrigin.bind_ok_ambient]
  refine ⟨p,y,ay,prepared,?_⟩
  unfold finish
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨(),v,b,written,rfl⟩


theorem Point.remaining (point : Point skb state w a v b) :
    ∃remaining : WG.M PeerId,((RxWorkers.publishSource skb state).run w).run a=(remaining.run v).run b := by
  cases point with
  | resolving point=>
      obtain ⟨rest,same⟩:=point.remaining
      exact ⟨rest >>= tail skb state,by rw [source];simp only [StateT.run_bind,same]⟩
  | borrowing resolved point=>
      rename_i pid u c
      obtain ⟨rest,same⟩:=point.remaining
      refine ⟨rest >>= fun _=>prepare skb state pid >>= finish pid,?_⟩
      rw [source]
      simp only [StateT.run_bind,resolved]
      change ((tail skb state pid).run u).run c=_
      simp only [tail,StateT.run_bind,same]
  | preparing resolved borrowed point=>
      rename_i pid u c x ax
      obtain ⟨rest,same⟩:=point.remaining
      refine ⟨rest >>= finish pid,?_⟩
      rw [source]
      simp only [StateT.run_bind,resolved]
      change ((tail skb state pid).run u).run c=_
      simp only [tail,StateT.run_bind,borrowed]
      change (((prepare skb state pid >>= finish pid).run x).run ax)=_
      simp only [StateT.run_bind,same]
  | written resolved borrowed prepared written=>exact ⟨pure _,written_return resolved borrowed prepared written⟩
  | returned performed=>exact ⟨pure _,performed⟩

theorem Point.observed_remaining {E : Type} {w : World}
    (point : Point skb state w.wg w.ambient v b) (h : List E) :
    ∃remaining : PrefixM E PeerId,runPrefix (liftWGObserver (liftWGPrefix (RxWorkers.publishSource skb state))) w h=
      runPrefix remaining {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  simp only [liftWGObserver_run,runWGPrefix_lift,same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxPublicationAccess
