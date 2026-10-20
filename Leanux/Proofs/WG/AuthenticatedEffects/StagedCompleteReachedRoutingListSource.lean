import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerMetadataCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryRoutingFrames

namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutingList
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllowedIps

def entries (node : NodeId) (items : List (PeerId × Peer)) : WG.M Unit := do
  for (pid,p) in items do
    if p.allowedipsList.contains node then
      setPeer pid {p with allowedipsList:=listRemove p.allowedipsList node}

theorem source (node : NodeId) : listDel node=(getDev >>= fun d=>entries node d.peers.toList) := rfl

theorem entries_nil (node : NodeId) : entries node []=pure () := rfl

theorem entries_cons (node : NodeId) (pid : PeerId) (p : Peer) (rest : List (PeerId × Peer)) :
    entries node ((pid,p)::rest)=((if p.allowedipsList.contains node then
      setPeer pid {p with allowedipsList:=listRemove p.allowedipsList node} else pure ()) >>= fun _=>entries node rest) := by
  simp only [entries,List.forIn_cons,bind_assoc]
  cases p.allowedipsList.contains node <;> simp only [Bool.false_eq_true,↓reduceIte,pure_bind,bind_assoc]

theorem entries_append (node : NodeId) (left right : List (PeerId × Peer)) :
    entries node (left++right)=(entries node left >>= fun _=>entries node right) := by
  induction left with
  | nil=>simp only [List.nil_append,entries_nil,pure_bind]
  | cons item rest ih=>
      rcases item with ⟨pid,p⟩
      simp only [List.cons_append,entries_cons,ih,bind_assoc]

noncomputable def readShape : Access.Shape getDev := by
  simp only [getDev,invariant]
  repeat' access_source_step

inductive Point (node : NodeId) : WGWorld → Ambient → WGWorld → Ambient → Prop where
  | read (point : Access.Point readShape w a v b) : Point node w a v b
  | cursor (read : (getDev.run w).run a=.ok ((d,u),c))
      (splitItems : d.peers.toList=done++rest)
      (walked : ((entries node done).run u).run c=.ok (((),v),b)) : Point node w a v b
  | returned (performed : ((listDel node).run w).run a=.ok (((),v),b)) : Point node w a v b

theorem Point.remaining (point : Point node w a v b) :
    ∃rest : WG.M Unit,((listDel node).run w).run a=(rest.run v).run b := by
  cases point with
  | read point=>
      obtain ⟨rest,same⟩:=point.remaining
      exact ⟨rest >>= fun d=>entries node d.peers.toList,by rw [source];simp only [StateT.run_bind,same]⟩
  | cursor read splitItems walked=>
      rename_i d u c done rest
      refine ⟨entries node rest,?_⟩
      rw [source]
      simp only [StateT.run_bind,read]
      change ((entries node d.peers.toList).run u).run c = _
      rw [splitItems,entries_append]
      simp only [StateT.run_bind,walked]
      rfl
  | returned performed=>exact ⟨pure (),performed⟩

theorem Point.observed_remaining {E : Type} {w : World} (point : Point node w.wg w.ambient v b) (h : List E) :
    ∃remaining : PrefixM E Unit,runPrefix (liftWGObserver (liftWGPrefix (listDel node))) w h=
      runPrefix remaining {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  simp only [liftWGObserver_run,runWGPrefix_lift,same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutingList
