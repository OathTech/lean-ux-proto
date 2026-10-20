import AllowedipsReconstructUpdate
import AllowedipsSourceModel

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG
open Binary.Pair.Allowedips.Model

/-- The executable reconstruction update agrees with the local endpoint
definition copied from the source proof, including the ordered peer lists and all unchanged records. -/
theorem target_exactInstalled (d : Device) (id pid : Nat) (old : AipNode) (peer : Peer)
    (hasNode : d.nodes.get? id=some old) (hasPeer : d.peers.get? pid=some peer) :
    target (exactInstalled d id old pid peer)=reassign id pid (target d) := by
  have hp : d.peers[pid]?=some peer := hasPeer
  have peers : (exactInstalled d id old pid peer).peers.Equiv
      (d.peers.map fun current p => {p with allowedipsList :=
        if current=pid then p.allowedipsList.filter (· != id)++[id] else p.allowedipsList.filter (· != id)}) := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro current
    by_cases same : current=pid
    · subst current
      simp [exactInstalled,Std.TreeMap.getElem?_map,hp,unlist,WG.listRemove]
    · simp only [exactInstalled,Std.TreeMap.getElem?_insert]
      rw [unlisted_get,Std.TreeMap.getElem?_map]
      cases d.peers[current]? <;> simp [unlist,WG.listRemove,same,Ne.symm same]
  have peersEq := peers.toList_eq
  rw [Std.TreeMap.toList_map] at peersEq
  unfold target reassign
  congr 1
  · change (d.nodes.insert id {old with peer := some pid}).toList=d.nodes.toList.map (reassignNode id pid)
    rw [Trie.tree_insert_present d.nodes id old _ hasNode]
    apply List.map_congr_left
    rintro ⟨current,node⟩ member
    by_cases same : current=id
    · subst current
      have equal := Option.some.inj ((Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member).symm.trans hasNode)
      subst old
      simp [reassignNode]
    · simp [reassignNode,same]
  · rw [peersEq]
    simp only [List.map_map]
    apply List.map_congr_left
    rintro ⟨current,p⟩ _
    by_cases same : current=pid <;> simp [reassignPeer,same]

theorem Exact.effect_corresponds {names o s memory regs d id base node pid peer owner}
    (related : Corresponds names o s.dmem d) (heap : heap names (target d) s.dmem=.ok ())
    (named : (id,base) ∈ names.trie.nodes) (present : d.nodes.get? id=some node)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (hasPeer : d.peers.get? pid=some owner)
    (nodeAt : s.regs.rbx.toNat=base) (peerAt : s.regs.r14.toNat=peer)
    (checked : Exact.effect s=.ok (memory,regs)) :
    Corresponds names o memory (exactInstalled d id node pid owner) := by
  change reconstruct names o memory=.ok (target _)
  rw [target_exactInstalled d id pid node owner present hasPeer]
  exact Exact.effect_reconstructs related heap named present peerNamed hasPeer nodeAt peerAt checked

#print axioms target_exactInstalled
#print axioms Exact.effect_corresponds
end Binary.Pair.Allowedips
