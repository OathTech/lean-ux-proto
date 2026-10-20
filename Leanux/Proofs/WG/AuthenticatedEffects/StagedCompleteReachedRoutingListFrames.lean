import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRoutingListSource

namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutingList
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllowedIps

theorem entries_run (node : NodeId) (items : List (PeerId × Peer)) (w : WGWorld) (d : Device)
    (device : w.dev=some d) (a : Ambient) :
    ((entries node items).run w).run a=.ok (((),{w with dev:=some {d with peers:=delFold node items d.peers}}),a) := by
  induction items generalizing w d with
  | nil=>simp only [entries_nil,delFold,List.foldl_nil]; rw [←device]; rfl
  | cons item rest ih=>
      rcases item with ⟨pid,p⟩
      rw [entries_cons]
      cases member : p.allowedipsList.contains node <;>
        simp only [Bool.false_eq_true,↓reduceIte,pure_bind]
      · simpa only [delFold,List.foldl_cons,delStep,member,Bool.false_eq_true,↓reduceIte] using ih w d device
      · simpa [StateT.run_bind,setPeer,modifyDev,StateT.run_modify,device,delFold,List.foldl_cons,delStep,member,unlist, show node ∈ p.allowedipsList from List.contains_iff_mem.mp member] using
          ih {w with dev:=some {d with peers:=d.peers.insert pid {p with allowedipsList:=listRemove p.allowedipsList node}}}
            {d with peers:=d.peers.insert pid {p with allowedipsList:=listRemove p.allowedipsList node}} rfl

theorem partial_clear (node : NodeId) (items : List (PeerId × Peer)) (w : WGWorld) (d : Device)
    (device : w.dev=some d) (saved : ∀item∈items,d.peers[item.1]?=some item.2) :
    clearListView {w with dev:=some {d with peers:=delFold node items d.peers}}=clearListView w := by
  apply Prod.ext
  · simp [clearListView,wgStoreView,device]
  · funext pid
    simp only [clearListView,device,Option.bind_some]
    rw [(pinned_const _private.Leanux.Proofs.WG.AllowedIps.ListsMirror.«0».Leanux.Proofs.WG.AllowedIps.delFold_get)
      node items d.peers d.peers saved pid]
    split <;> cases d.peers[pid]? <;> rfl

theorem Point.frame (point : Point node w a v b) : StagedEntry.view v=StagedEntry.view w := by
  cases point with
  | read point=>exact point.frame
  | cursor read splitItems walked=>
      rename_i d u c done rest
      cases device : w.dev with
      | none=>simp [getDev,device,invariant,AmbientM.invariant] at read;cases read
      | some current=>
          simp [getDev,device] at read
          obtain ⟨⟨rfl,rfl⟩,rfl⟩:=read
          rw [entries_run node done w current device a] at walked
          cases walked
          have saved : ∀item∈done,current.peers[item.1]?=some item.2 := by
            intro item member
            apply Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp
            rw [splitItems]
            exact List.mem_append_left _ member
          rw [RoutingFrames.list_factor,RoutingFrames.list_factor,partial_clear node done w current device saved]
  | returned performed=>exact (ProjectedAction.iff_run_ambient _ _ _).mp (RoutingFrames.list_delete node) _ _ _ _ _ performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutingList
