import AllowedipsConnectRecord
import AllowedipsRootMetadata

namespace Binary.Pair.Allowedips
open Root

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

private theorem error_bind (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f)=.error e := rfl

theorem peer_decoder_congr {names : Names} {before after : DataMem} {id base : Nat}
    (count : word after "peer.refcount" (base+Layouts.peer_refcount) 4=
      word before "peer.refcount" (base+Layouts.peer_refcount) 4)
    (lists : (do
        let first ← word after "peer.list.head" (base+1096) 8
        peerList names after (base+1096) (names.trie.nodes.length+1) first (base+1096) [])=
      (do
        let first ← word before "peer.list.head" (base+1096) 8
        peerList names before (base+1096) (names.trie.nodes.length+1) first (base+1096) [])) :
    decodePeer names nodeOffsets after id base=decodePeer names nodeOffsets before id base := by
  simp only [decodePeer,nodeOffsets,AllowedipsMutationLayout.allowedips_list,count]
  cases value : word before "peer.refcount" (base+Layouts.peer_refcount) 4 with
  | error e => simp only [error_bind]
  | ok c =>
    simp only [ok_bind]
    have mapped := congrArg (fun scan : Decode (List Nat) =>
      scan >>= fun entries => pure (id,c,entries)) lists
    simpa only [bind_assoc] using mapped

def ConnectWrites (base slot : Nat) (a : BitVec 64) : Prop :=
  InRange (.ofNat 64 (base+48)) 8 a ∨ InRange (.ofNat 64 slot) 8 a

theorem connect_frame (m : DataMem) (base slot packed : Nat) :
    EqualOutside (ConnectWrites base slot) m (connectMemory m base slot packed) := by
  intro a outside
  exact (write64_frame _ _ _ a (fun inside => outside (.inl inside))).trans
    (write64_frame _ _ _ a (fun inside => outside (.inr inside)))

theorem connect_lists_apart {names : Names} {id base parentId parentBase direction : Nat}
    (g : Geometry names nodeOffsets) (named : (id,base) ∈ names.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes) (bit : direction<2) :
    ∀ a, ListWrites names a → ¬ConnectWrites base (parentBase+8+direction*8) a := by
  intro a list written
  rcases written with fresh|slot
  · exact node_before_list_apart g rfl named (offset:=48) (size:=8) (by decide) a fresh list
  · exact node_before_list_apart g rfl parentNamed (offset:=8+direction*8) (size:=8)
      (by omega) a (by simpa only [Nat.add_assoc] using slot) list

theorem connect_count_apart {names : Names} {id base parentId parentBase direction pid peer : Nat}
    (g : Geometry names nodeOffsets) (named : (id,base) ∈ names.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (bit : direction<2) :
    ∀ a, InRange (.ofNat 64 (peer+Layouts.peer_refcount)) 4 a →
      ¬ConnectWrites base (parentBase+8+direction*8) a := by
  intro a read written
  rcases written with fresh|slot
  · exact g.slices_apart (peer_allocation peerNamed) (node_allocation named)
      Layouts.peer_refcount 4 48 8 (by dsimp only; decide) (by dsimp only; decide)
      (fun _ => .inr (by decide)) a read fresh
  · exact g.slices_apart (peer_allocation peerNamed) (node_allocation parentNamed)
      Layouts.peer_refcount 4 (8+direction*8) 8 (by dsimp only; decide)
      (by change 8+direction*8+8≤72; omega) (fun _ => .inr (by change 8+direction*8+8≤1056; omega))
      a read (by simpa only [Nat.add_assoc] using slot)

theorem connect_table_apart {names : Names} {id base parentId parentBase direction offset size : Nat}
    (valid : validate names nodeOffsets=.ok ()) (g : Geometry names nodeOffsets)
    (named : (id,base) ∈ names.trie.nodes) (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (bit : direction<2) (within : offset+size≤24) :
    ∀ a, InRange (.ofNat 64 (names.table+offset)) size a →
      ¬ConnectWrites base (parentBase+8+direction*8) a := by
  intro a read written
  rcases written with fresh|slot
  · exact table_allocation_bytes valid g (node_allocation named) within
      (field:=48) (width:=8) (by dsimp only; decide) a read fresh
  · exact table_allocation_bytes valid g (node_allocation parentNamed) within
      (field:=8+direction*8) (width:=8) (by change 8+direction*8+8≤72; omega)
      a read (by simpa only [Nat.add_assoc] using slot)

theorem connect_peer_frame {names : Names} {m : DataMem} {id base parentId parentBase direction pid peer packed : Nat}
    (g : Geometry names nodeOffsets) (named : (id,base) ∈ names.trie.nodes)
    (parentNamed : (parentId,parentBase) ∈ names.trie.nodes)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (bit : direction<2) :
    decodePeer names nodeOffsets (connectMemory m base (parentBase+8+direction*8) packed) pid peer=
      decodePeer names nodeOffsets m pid peer := by
  have frame := connect_frame m base (parentBase+8+direction*8) packed
  have count := Trie.word_frame frame "peer.refcount" _ _ (connect_count_apart g named parentNamed peerNamed bit)
  have lists := list_read_frame (fuel:=names.trie.nodes.length+1) frame
    (connect_lists_apart g named parentNamed bit) (.peer peerNamed)
  exact peer_decoder_congr count.symm lists.symm

#print axioms connect_peer_frame
end Binary.Pair.Allowedips
