import PairAllowedipsState
import PairTrieFrame

namespace Binary.Pair.Allowedips
/-- Exact field reads, used as a frame footprint rather than additional R
clauses. The list traversal validates each link before reading through it. -/
def nodeFields (o : AllowedipsProbe.Offsets) : List Span :=
  Trie.nodeSpans o ++ [(AllowedipsMutationLayout.parent_bit_packed,8),
    (AllowedipsMutationLayout.peer_list,8),(AllowedipsMutationLayout.peer_list+8,8)]

def peerFields (o : AllowedipsProbe.Offsets) : List Span :=
  [(o.peerRefcount,4),(AllowedipsMutationLayout.allowedips_list,8),
    (AllowedipsMutationLayout.allowedips_list+8,8)]

def tableFields : List Span :=
  [(AllowedipsMutationLayout.root4,8),(AllowedipsMutationLayout.root6,8),(AllowedipsMutationLayout.seq,8)]

def readSpans (names : Names) (o : AllowedipsProbe.Offsets) : List Span :=
  tableFields.map (fun (offset,size) => (names.table+offset,size)) ++
  (names.trie.nodes.flatMap (fun (_,a) => (nodeFields o).map (fun (offset,size) => (a+offset,size))) ++
  names.trie.peers.flatMap (fun (_,a) => (peerFields o).map (fun (offset,size) => (a+offset,size))))


def listFields : List Span :=
  [(AllowedipsMutationLayout.allowedips_list,8),(AllowedipsMutationLayout.allowedips_list+8,8)]

def metadataSpans (names : Names) (o : AllowedipsProbe.Offsets) : List Span :=
  tableFields.map (fun (offset,size) => (names.table+offset,size)) ++
  (names.trie.nodes.flatMap (fun (_,a) => (nodeFields o).map (fun (offset,size) => (a+offset,size))) ++
  names.trie.peers.flatMap (fun (_,a) => listFields.map (fun (offset,size) => (a+offset,size))))

end Binary.Pair.Allowedips
