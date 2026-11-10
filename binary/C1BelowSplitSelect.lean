import C1BelowSplitOrder
import AllowedipsSelectKey

/-! Result C1, work package 3, the split path: the link T5 left assumed
between the bit the machine selects (`selected byte shift`, from a node's two
selector bytes and a byte of another node's stored key) and the mirror's
`choose`. Derived from the two nodes' decodes in the memory of the reads. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.Pair.Allowedips.Root AllowedipsChild Binary.AllowedipsRelation

/-- The stored key of a decoded node, as the words `queryByte_read` takes. -/
theorem key_words {names : Trie.Names} {m : DataMem} {a : Nat} {node : Trie.Node}
    (decoded : Trie.decodeNode names nodeOffsets m a = .ok node) :
    QueryWords m (.ofNat 64 (a+32)) node.width node.key := by
  have fields := Trie.decodeNode_fields decoded
  have key := fields.key
  unfold QueryWords
  by_cases four : node.width = 32
  · simp only [four,↓reduceIte] at key ⊢
    exact word_loadInt _ _ _ _ _ key
  · simp only [four,↓reduceIte] at key ⊢
    obtain ⟨hi,lo,high,low,value⟩ := key
    have highRead := word_loadInt _ _ _ _ _ high
    have lowRead := word_loadInt _ _ _ _ _ low
    have small := (loadInt_range _ _ _ _ lowRead).2
    have small : lo < 2^64 := by
      change (lo : Int) < 18446744073709551616 at small
      omega
    have top : node.key/2^64 = hi := by rw [value]; omega
    have bottom : node.key%2^64 = lo := by rw [value]; omega
    rw [top,bottom]
    refine ⟨highRead,?_⟩
    have address : (BitVec.ofNat 64 (a+32) + 8 : BitVec 64) = .ofNat 64 (a+32+8) := by
      rw [BitVec.ofNat_add (a+32) 8]; rfl
    rw [address]
    exact lowRead

/-- The machine's selected bit is the mirror's: `sel` is the node whose
selector bytes (offsets 25, 26) are read, `keyNode` the node whose stored
key byte (offset 32 + index) is read. -/
theorem selected_link {names names' : Trie.Names} {m : DataMem} {selBase keyBase : Nat}
    {sel keyNode : Trie.Node} {index shift byte : Nat}
    (selDecoded : Trie.decodeNode names nodeOffsets m selBase = .ok sel)
    (keyDecoded : Trie.decodeNode names' nodeOffsets m keyBase = .ok keyNode)
    (sameWidth : keyNode.width = sel.width) (short : sel.cidr < sel.width)
    (indexRead : m.loadInt (.ofNat 64 selBase + 25) 1 = some (index : Int))
    (shiftRead : m.loadInt (.ofNat 64 selBase + 26) 1 = some (shift : Int))
    (byteRead : m.loadInt (.ofNat 64 keyBase + 32 + .ofNat 64 index) 1 = some (byte : Int)) :
    selected byte shift = keyNode.key/2^(sel.width-1-sel.cidr)%2 := by
  have fields := Trie.decodeNode_fields selDecoded
  have ixRead := word_loadInt _ _ _ _ _ fields.byteSelector
  have shRead := word_loadInt _ _ _ _ _ fields.bitSelector
  have a25 : (BitVec.ofNat 64 selBase + 25 : BitVec 64) = .ofNat 64 (selBase+25) := by
    rw [BitVec.ofNat_add]; rfl
  have a26 : (BitVec.ofNat 64 selBase + 26 : BitVec 64) = .ofNat 64 (selBase+26) := by
    rw [BitVec.ofNat_add]; rfl
  rw [a25] at indexRead
  rw [a26] at shiftRead
  have ix : index = byteSelector sel.width sel.cidr :=
    Int.ofNat.inj (Option.some.inj (indexRead.symm.trans ixRead))
  have sh : shift = 7-sel.cidr%8 :=
    Int.ofNat.inj (Option.some.inj (shiftRead.symm.trans shRead))
  have words := key_words keyDecoded
  rw [sameWidth] at words
  have loaded := queryByte_read m (.ofNat 64 (keyBase+32)) sel.width keyNode.key
    (byteSelector sel.width sel.cidr) fields.family
    (selector_position sel.width sel.cidr fields.family short).2 words
  have a32 : (BitVec.ofNat 64 keyBase + 32 : BitVec 64) = .ofNat 64 (keyBase+32) := by
    rw [BitVec.ofNat_add]; rfl
  rw [a32,ix] at byteRead
  have actual : byte = queryByte sel.width keyNode.key (byteSelector sel.width sel.cidr) :=
    Int.ofNat.inj (Option.some.inj (byteRead.symm.trans loaded))
  rw [actual,sh]
  exact queryByte_select sel.width keyNode.key sel.cidr fields.family short

/-- The same with the selectors in registers (the `choose` before
`Add.entry+0x338` computes them from the prefix length instead of reading
them): the byte at `byteSelector width cidr` of a decoded node's key, shifted
by `7 - cidr % 8`. -/
theorem selected_key_byte {names : Trie.Names} {m : DataMem} {keyBase width cidr byte : Nat}
    {keyNode : Trie.Node}
    (keyDecoded : Trie.decodeNode names nodeOffsets m keyBase = .ok keyNode)
    (sameWidth : keyNode.width = width) (short : cidr < width)
    (byteRead : m.loadInt (.ofNat 64 keyBase + 32 + .ofNat 64 (byteSelector width cidr)) 1 = some (byte : Int)) :
    selected byte (7-cidr%8) = keyNode.key/2^(width-1-cidr)%2 := by
  have family := (Trie.decodeNode_fields keyDecoded).family
  rw [sameWidth] at family
  have words := key_words keyDecoded
  rw [sameWidth] at words
  have loaded := queryByte_read m (.ofNat 64 (keyBase+32)) width keyNode.key
    (byteSelector width cidr) family (selector_position width cidr family short).2 words
  have a32 : (BitVec.ofNat 64 keyBase + 32 : BitVec 64) = .ofNat 64 (keyBase+32) := by
    rw [BitVec.ofNat_add]; rfl
  rw [a32] at byteRead
  have actual : byte = queryByte width keyNode.key (byteSelector width cidr) :=
    Int.ofNat.inj (Option.some.inj (byteRead.symm.trans loaded))
  rw [actual]
  exact queryByte_select width keyNode.key cidr family short

#print axioms selected_key_byte
#print axioms key_words
#print axioms selected_link
end Binary.Statements.C1.Proof
