import PairAllowedipsState

namespace Binary.Pair.Allowedips

/-- The interpretation update at a successful generic allocation return.
The caller must separately establish fresh physical storage. -/
def Names.allocated (names : Names) (address : Nat) : Names :=
  {names with
    nextNode:=names.nextNode+1,
    trie:={names.trie with nodes:=names.trie.nodes++[(names.nextNode,address)]}}

end Binary.Pair.Allowedips
