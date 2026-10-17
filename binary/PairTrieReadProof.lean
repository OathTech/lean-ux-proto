import PairHeapProof
import PairTrieFrame

namespace Binary.Pair.Trie
open Leanux Leanux.WG AllowedipsRelation

theorem trieReads_decoded {n : Names} {o : AllowedipsProbe.Offsets} {m : DataMem} {d : Device}
    {root : Option NodeId} {bits query : Nat} (related : Corresponds n o m d)
    {address : BitVec 64}
    (read : TrieReads (interpretation n.nodes) (fun id => d.nodes.get? id) root bits query address) :
    ReadBytes n o address := by
  obtain ⟨id,node,_,present,read⟩ := read
  have reconstructed := reconstruct_fields related
  obtain ⟨base,member,_⟩ := reconstructed.node present
  have atAddress := interpretation_of_mem reconstructed.nodeIds member
  obtain ⟨_,peerOffset,childOffset,cidrOffset,byteOffset,bitOffset,_,keyOffset,_⟩ := reconstructed.layout
  have field (offset size : Nat) (span : (offset,size) ∈ nodeSpans o)
      (inside : InRange (.ofNat 64 base + .ofNat 64 offset) size address) : ReadBytes n o address :=
    .inl ⟨id,base,member,offset,size,span,by simpa only [BitVec.ofNat_add] using inside⟩
  simp only [NodeReads,atAddress] at read
  rcases read with key | cidr | ⟨_,peer | ⟨_,byte | bit | child⟩⟩
  · unfold KeyReads at key
    split at key
    · apply field o.bits 4 (by simp [nodeSpans])
      simpa only [keyOffset] using key
    · rcases key with hi | ⟨_,lo⟩
      · apply field o.bits 8 (by simp [nodeSpans])
        simpa only [keyOffset] using hi
      · apply field (o.bits+8) 8 (by simp [nodeSpans])
        simpa only [keyOffset,BitVec.ofNat_add,BitVec.add_assoc,
          show (8 : BitVec 64) = .ofNat 64 8 from rfl] using lo
  · apply field o.cidr 1 (by simp [nodeSpans])
    simpa only [cidrOffset] using cidr
  · apply field o.peer 8 (by simp [nodeSpans])
    simpa only [peerOffset] using peer
  · apply field o.bitAtA 1 (by simp [nodeSpans])
    simpa only [byteOffset] using byte
  · apply field o.bitAtB 1 (by simp [nodeSpans])
    simpa only [bitOffset] using bit
  · have index : childIndex node query = 0 ∨ childIndex node query = 1 := by
      have bound := Nat.mod_lt (query / 2^(node.bitlen-1-node.cidr)) (by decide : 0 < 2)
      unfold childIndex
      omega
    rcases index with index | index
    · apply field o.children 8 (by simp [nodeSpans])
      simpa only [childOffset,index,Nat.mul_zero,Nat.add_zero] using child
    · apply field (o.children+8) 8 (by simp [nodeSpans])
      simpa only [childOffset,index,Nat.mul_one] using child

#print axioms trieReads_decoded
end Binary.Pair.Trie
