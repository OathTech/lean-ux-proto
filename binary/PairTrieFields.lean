import PairNamesProof

namespace Binary.Pair.Trie
open Leanux Leanux.WG

theorem decoded_key {names : Names} {o : AllowedipsProbe.Offsets}
    {m : DataMem} {a query : Nat} {node : Node}
    (fields : DecodedFields names o m a node) (queryBound : query < 2^node.width) :
    AllowedipsRelation.KeyFields m (.ofNat 64 (a+o.bits)) node.width node.key query := by
  refine ⟨?_,queryBound,?_⟩
  · by_cases family : node.width = 32
    · have read := fields.key
      rw [ite_eq_left family] at read
      have bound := word_bound read
      simpa only [family] using bound
    · have read := fields.key
      rw [ite_eq_right family] at read
      obtain ⟨hi,lo,hiRead,loRead,key⟩ := read
      have hiBound := word_bound hiRead
      have loBound := word_bound loRead
      have width : node.width = 128 := fields.family.resolve_left family
      rw [width,key]
      omega
  · by_cases family : node.width = 32
    · have read := fields.key
      rw [ite_eq_left family] at read ⊢
      exact word_loadInt _ _ _ _ _ read
    · have read := fields.key
      rw [ite_eq_right family] at read ⊢
      obtain ⟨hi,lo,hiRead,loRead,key⟩ := read
      have loBound := word_bound loRead
      have high : node.key / 2^64 = hi := by rw [key]; omega
      have low : node.key % 2^64 = lo := by rw [key]; omega
      refine ⟨?_,fun _ => ?_⟩
      · rw [high]; exact word_loadInt _ _ _ _ _ hiRead
      · rw [low]
        simpa only [show (8 : BitVec 64) = .ofNat 64 8 from rfl,BitVec.ofNat_add] using word_loadInt _ _ _ _ _ loRead

/-- The physical fields consumed by one node body follow from the tested
decoder and the interpretation constructed from its Names. -/
theorem decoded_node_fields {names : Names} {o : AllowedipsProbe.Offsets}
    {m : DataMem} {s : State} {id a bits query : Nat} {node : AipNode}
    (reconstructed : Reconstructed names o m s)
    (member : (id,a) ∈ names.nodes)
    (decoded : decodeNode names o m a = .ok (targetNode node))
    (width : node.bitlen = bits) (queryBound : query < 2^bits) :
    AllowedipsRelation.NodeFields m (interpretation names.nodes) (interpretation names.peers)
      bits query id node := by
  have fields := decodeNode_fields decoded
  have ranges := reconstructed.nodeRange id a member
  have address := interpretation_of_mem reconstructed.nodeIds member
  obtain ⟨_,peerOffset,childOffset,cidrOffset,byteOffset,bitOffset,_,keyOffset,_⟩ := reconstructed.layout
  refine ⟨interpretation_nonnull reconstructed.nodeIds member ranges.1 (by omega),?_,?_,?_,?_⟩
  · exact word_bound fields.cidr
  · have key := decoded_key fields (by simpa only [targetNode,width] using queryBound)
    simpa only [targetNode,width,address,keyOffset,BitVec.ofNat_add] using key
  · change m.loadInt _ 1 = some (node.cidr : Int)
    simpa only [targetNode,address,cidrOffset,BitVec.ofNat_add] using
      word_loadInt _ _ _ _ _ fields.cidr
  · intro _
    obtain ⟨raw,read,decodedPeer⟩ := fields.peer
    have peer := pointer_value reconstructed.peerIds (by simpa using word_bound read) decodedPeer
    refine ⟨?_,peer.2,fun _ => ?_⟩
    · change m.loadInt _ 8 = some ((AllowedipsRelation.pointer (interpretation names.peers) (targetNode node).peer).toNat : Int)
      rw [peer.1]
      simpa only [address,peerOffset,BitVec.ofNat_add] using word_loadInt _ _ _ _ _ read
    obtain ⟨left,right,lp,rp,children,leftRead,leftPointer,rightRead,rightPointer⟩ := fields.children
    change node.bit = #[left,right] at children
    refine ⟨width,by rw [children]; rfl,?_,?_,?_⟩
    · change m.loadInt _ 1 = some ((node.cidr/8 ^^^ ((bits/8-1)%8)) : Int)
      simpa only [targetNode,width,address,byteOffset,BitVec.ofNat_add] using
        word_loadInt _ _ _ _ _ fields.byteSelector
    · change m.loadInt _ 1 = some (((7-node.cidr%8 : Nat)) : Int)
      simpa only [targetNode,address,bitOffset,BitVec.ofNat_add] using
        word_loadInt _ _ _ _ _ fields.bitSelector
    · intro next selected
      have index : AllowedipsRelation.childIndex node query = 0 ∨
          AllowedipsRelation.childIndex node query = 1 := by
        have bound := Nat.mod_lt (query / 2^(node.bitlen-1-node.cidr)) (by decide : 0 < 2)
        unfold AllowedipsRelation.childIndex
        omega
      rcases index with index | index
      · rw [children,index] at selected
        have equal : left = next := Option.some.inj selected
        subst next
        have pointer := pointer_value reconstructed.nodeIds (by simpa using word_bound leftRead) leftPointer
        refine ⟨?_,pointer.2⟩
        change m.loadInt _ 8 = some ((AllowedipsRelation.pointer (interpretation names.nodes) _).toNat : Int)
        rw [pointer.1]
        simpa only [address,childOffset,index,Nat.mul_zero,Nat.add_zero,BitVec.ofNat_add] using
          word_loadInt _ _ _ _ _ leftRead
      · rw [children,index] at selected
        have equal : right = next := Option.some.inj selected
        subst next
        have pointer := pointer_value reconstructed.nodeIds (by simpa using word_bound rightRead) rightPointer
        refine ⟨?_,pointer.2⟩
        change m.loadInt _ 8 = some ((AllowedipsRelation.pointer (interpretation names.nodes) _).toNat : Int)
        rw [pointer.1]
        simpa only [address,childOffset,index,Nat.mul_one,Nat.add_assoc,BitVec.ofNat_add,BitVec.add_assoc] using
          word_loadInt _ _ _ _ _ rightRead

#print axioms decoded_node_fields
end Binary.Pair.Trie
