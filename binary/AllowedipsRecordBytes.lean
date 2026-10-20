import AllowedipsRootRecord

namespace Binary.Pair.Allowedips
open Root

/-- A complete node record reads at most its first 56 bytes. Peer-list union
bytes are deliberately outside this decoder frame. -/
theorem record_bytes_congr {names : Names} {before after : DataMem} {id base : Nat}
    (words : ∀ offset size, offset+size≤56 → ∀ path,
      word after path (base+offset) size=word before path (base+offset) size) :
    decodeNode names nodeOffsets after id base=decodeNode names nodeOffsets before id base := by
  have core : Trie.decodeNode names.trie nodeOffsets after base=Trie.decodeNode names.trie nodeOffsets before base := by
    apply Trie.decodeNode_congr
    intro offset size member path
    apply words offset size _ path
    simp only [Trie.nodeSpans,nodeOffsets,AllowedipsLayout.peer,AllowedipsLayout.bit,
      AllowedipsLayout.cidr,AllowedipsLayout.bit_at_a,AllowedipsLayout.bit_at_b,
      AllowedipsLayout.bitlen,AllowedipsLayout.bits,List.mem_cons,List.not_mem_nil,
      or_false,Prod.mk.injEq] at member
    omega
  have parent := words 48 8 (by decide) "node.parent"
  simp only [decodeNode,core,AllowedipsMutationLayout.parent_bit_packed,parent]

end Binary.Pair.Allowedips
