import Leanux.Proofs.WG.Config.RoutingReadbackModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

theorem routingReadNode_readable
    (d : Device) (t4 t6 : AllowedIps.Tree) (pid : PeerId) (p : Peer)
    (routing : AllowedIps.RoutingInvariant d t4 t6)
    (peer : d.peers[pid]? = some p) :
    ∀ id ∈ p.allowedipsList,
      d.nodes[id]? = some (routingReadNode d id) := by
  intro id member
  obtain ⟨entry, inside, sameId, _⟩ :=
    ((routing.lists pid p peer).2 id).mp member
  have resident : ∃ n, d.nodes[id]? = some n := by
    rcases List.mem_append.mp inside with in4 | in6
    · exact routing.forest.2.2.1.resident
        (sameId ▸ AllowedIps.Tree.entry_mem_nodeIds in4)
    · exact routing.forest.2.2.2.resident
        (sameId ▸ AllowedIps.Tree.entry_mem_nodeIds in6)
  obtain ⟨node, stored⟩ := resident
  simp only [routingReadNode, stored, Option.getD_some]

theorem allowedipRoutingEffect_target (d out : Device) (t4 t6 : AllowedIps.Tree)
    (pid : PeerId) (p : Peer) (attrs : AllowedIpAttrs) (ret : Int)
    (routing : AllowedIps.RoutingInvariant d t4 t6)
    (resident : d.peers[pid]? = some p)
    (effect : AllowedipRoutingEffect d out t4 t6 pid attrs ret) :
    ∃ next u4 u6, out.peers[pid]? = some next ∧
      AllowedIps.RoutingInvariant out u4 u6 := by
  rcases effect with ⟨_, rfl⟩ | ⟨v4, _, _, _, outcome⟩
  · exact ⟨p, t4, t6, resident, routing⟩
  · rcases outcome.result with ⟨_, inserted, finalInv⟩ | ⟨_, refused⟩
    · have present : ∃ next, out.peers[pid]? = some next := by
        rw [inserted.peers]
        change ∃ next, (d.peers[pid]?).map _ = some next
        rw [resident]
        exact ⟨_, rfl⟩
      obtain ⟨next, present⟩ := present
      exact ⟨next, _, _, present, finalInv⟩
    · exact ⟨p, t4, t6, (refused.peers pid).trans resident, refused.invariant⟩

/-- Successful insertion removes the bound ID from every old peer list and
appends it once to the destination list, retaining the actual trie-selected ID. -/
theorem allowedipRoutingEffect_moved (d out : Device) (t4 t6 : AllowedIps.Tree)
    (pid : PeerId) (attrs : AllowedIpAttrs)
    (routing : AllowedIps.RoutingInvariant d t4 t6)
    (effect : AllowedipRoutingEffect d out t4 t6 pid attrs 0) :
    AllowedipMoved d out t4 t6 pid attrs := by
  rcases effect with ⟨bad,_⟩ | ⟨v4,family,_,_,outcome⟩
  · simp only [EINVAL] at bad
    contradiction
  · rcases outcome.result with ⟨_,inserted,_⟩ | ⟨bad,_⟩
    · refine ⟨v4,family,?_⟩
      exact inserted.normalized_peers (routing.bumpSeq.selected_rep _)
        (routing.bumpSeq.selected_rep _) routing.bumpSeq.below (routing.bumpSeq.selected_lists _)
    · simp only [ENOMEM] at bad
      contradiction

end Leanux.Proofs.WG.Config
