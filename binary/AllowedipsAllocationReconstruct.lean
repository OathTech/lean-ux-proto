import AllowedipsReconstructUpdate
import AllowedipsAllocationNames

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- Assemble decoder facts after one physical allocation. Old records remain
in their original order and the fresh identity is appended by the same Names
operation used in the runner. This is a data-reconstruction lemma, not an
assumed execution or an allocator contract. -/
theorem reconstruct_allocated {names o before after state address newNode table}
    (nodeUpdate : NodeId×AipNode → NodeId×AipNode)
    (peerUpdate : PeerId×Nat×List NodeId → PeerId×Nat×List NodeId)
    (entry : reconstruct names o before=.ok state)
    (valid : validate (names.allocated address) o=.ok ())
    (root4 : ∃ raw,word after "table.root4" (names.table+AllowedipsMutationLayout.root4) 8=.ok raw ∧
      Trie.pointer (names.allocated address).trie.nodes "table.root4" raw=.ok table.root4)
    (root6 : ∃ raw,word after "table.root6" (names.table+AllowedipsMutationLayout.root6) 8=.ok raw ∧
      Trie.pointer (names.allocated address).trie.nodes "table.root6" raw=.ok table.root6)
    (seq : word after "table.seq" (names.table+AllowedipsMutationLayout.seq) 8=.ok table.seq.toNat)
    (nodes : ∀ pair ∈ names.trie.nodes, ∀ value,
      decodeNode names o before pair.1 pair.2=.ok value →
      decodeNode (names.allocated address) o after pair.1 pair.2=.ok (nodeUpdate value))
    (fresh : decodeNode (names.allocated address) o after names.nextNode address=.ok (names.nextNode,newNode))
    (peers : ∀ pair ∈ names.trie.peers, ∀ value,
      decodePeer names o before pair.1 pair.2=.ok value →
      decodePeer (names.allocated address) o after pair.1 pair.2=.ok (peerUpdate value)) :
    reconstruct (names.allocated address) o after=
      .ok ⟨table,state.nodes.map nodeUpdate++[(names.nextNode,newNode)],
        state.peers.map peerUpdate,names.nextNode+1⟩ := by
  unfold reconstruct at entry
  obtain ⟨_,_,entry⟩ := bind_ok entry
  obtain ⟨_,_,entry⟩ := bind_ok entry
  obtain ⟨_,_,entry⟩ := bind_ok entry
  obtain ⟨_,_,entry⟩ := bind_ok entry
  obtain ⟨_,_,entry⟩ := bind_ok entry
  obtain ⟨_,_,entry⟩ := bind_ok entry
  obtain ⟨oldNodes,nodeReads,entry⟩ := bind_ok entry
  obtain ⟨oldPeers,peerReads,entry⟩ := bind_ok entry
  cases Except.ok.inj entry
  have ns := mapM_update nodeUpdate nodeReads nodes
  have ps := mapM_update peerUpdate peerReads peers
  obtain ⟨r4,r4Read,r4Decode⟩ := root4
  obtain ⟨r6,r6Read,r6Decode⟩ := root6
  have tableEq : (names.allocated address).table=names.table := rfl
  simp only [reconstruct,valid,ok_bind,tableEq,r4Read,r4Decode,r6Read,r6Decode,seq,Nat.toUInt64,UInt64.ofNat_toNat]
  change (do
    let nodes ← (names.trie.nodes++[(names.nextNode,address)]).mapM
      (fun (id,base) => decodeNode (names.allocated address) o after id base)
    let peers ← names.trie.peers.mapM (fun (id,base) => decodePeer (names.allocated address) o after id base)
    pure ({table,nodes,peers,nextNode:=names.nextNode+1} : State))=_
  rw [List.mapM_append,ns,ps]
  simp only [List.mapM_cons,List.mapM_nil,fresh,ok_bind]
  rfl

#print axioms reconstruct_allocated
end Binary.Pair.Allowedips
