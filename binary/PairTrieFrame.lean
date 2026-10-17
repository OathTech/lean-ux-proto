import PairTrie
import Memory

namespace Binary.Pair.Trie

/-- Bytes consulted by reconstruction, including both possible key layouts.
This is a footprint of the executable decoder, not another state relation. -/
def nodeSpans (o : AllowedipsProbe.Offsets) : List (Nat × Nat) :=
  [(o.peer,8), (o.children,8), (o.children+8,8), (o.cidr,1),
   (o.bitlen,1), (o.bitAtA,1), (o.bitAtB,1), (o.bits,4), (o.bits,8), (o.bits+8,8)]

def ReadBytes (n : Names) (o : AllowedipsProbe.Offsets) (a : BitVec 64) : Prop :=
  (∃ id base, (id,base) ∈ n.nodes ∧ ∃ offset size, (offset,size) ∈ nodeSpans o ∧
    InRange (.ofNat 64 (base+offset)) size a) ∨
  (∃ id base, (id,base) ∈ n.peers ∧ InRange (.ofNat 64 (base+o.peerRefcount)) 4 a)

theorem word_frame {before after : DataMem} {writes : BitVec 64 → Prop}
    (same : EqualOutside writes before after) (path : String) (base size : Nat)
    (apart : ∀ a, InRange (.ofNat 64 base) size a → ¬writes a) :
    word before path base size = word after path base size := by
  unfold word
  rw [same.loadBytes (.ofNat 64 base) size (fun i hi => apart _ ⟨i,hi,rfl⟩)]

theorem decodeNode_congr (n : Names) (o : AllowedipsProbe.Offsets) (before after : DataMem) (base : Nat)
    (same : ∀ offset size, (offset,size) ∈ nodeSpans o → ∀ path,
      word before path (base+offset) size = word after path (base+offset) size) :
    decodeNode n o before base = decodeNode n o after base := by
  have peer := same o.peer 8 (by simp [nodeSpans]) "node.peer"
  have left := same o.children 8 (by simp [nodeSpans])
  have right := same (o.children+8) 8 (by simp [nodeSpans])
  have cidr := same o.cidr 1 (by simp [nodeSpans]) "node.cidr"
  have width := same o.bitlen 1 (by simp [nodeSpans]) "node.width"
  have byte := same o.bitAtA 1 (by simp [nodeSpans]) "node.byte-selector"
  have bit := same o.bitAtB 1 (by simp [nodeSpans]) "node.bit-selector"
  have key32 := same o.bits 4 (by simp [nodeSpans]) "node.key32"
  have high := same o.bits 8 (by simp [nodeSpans]) "node.key128.high"
  have low := same (o.bits+8) 8 (by simp [nodeSpans]) "node.key128.low"
  simp only [decodeNode, Std.Legacy.Range.forIn_eq_forIn_range',
    show ([:2] : Std.Legacy.Range).size = 2 from rfl,
    List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil,
    Nat.reduceAdd, Nat.reduceMul, Nat.add_zero, Nat.add_assoc, bind_assoc, pure_bind]
  simp only [peer, left, right, cidr, width, byte, bit, key32, high, low]

theorem mapM_same [Monad m] [LawfulMonad m] (xs : List α) (f g : α → m β)
    (same : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, same x (by simp), ih (fun a h => same a (by simp [h]))]

theorem reconstruct_congr (n : Names) (o : AllowedipsProbe.Offsets) (before after : DataMem)
    (nodes : ∀ id base, (id,base) ∈ n.nodes → decodeNode n o before base = decodeNode n o after base)
    (peers : ∀ id base, (id,base) ∈ n.peers →
      word before s!"peer[{id}].refcount" (base+o.peerRefcount) 4 =
        word after s!"peer[{id}].refcount" (base+o.peerRefcount) 4) :
    reconstruct n o before = reconstruct n o after := by
  have ns : n.nodes.mapM (fun (id,a) => do return (id, ← decodeNode n o before a)) =
      n.nodes.mapM (fun (id,a) => do return (id, ← decodeNode n o after a)) := by
    apply mapM_same
    rintro ⟨id,a⟩ member
    simp only [nodes id a member]
  have ps : n.peers.mapM (fun (id,a) => do return (id, ← word before s!"peer[{id}].refcount" (a+o.peerRefcount) 4)) =
      n.peers.mapM (fun (id,a) => do return (id, ← word after s!"peer[{id}].refcount" (a+o.peerRefcount) 4)) := by
    apply mapM_same
    rintro ⟨id,a⟩ member
    simp only [peers id a member]
  unfold reconstruct
  rw [ns,ps]

/-- The exact tested reconstruction survives any execution frame disjoint
from its reads. No expected decoded values are supplied to the decoder. -/
theorem reconstruct_frame {before after : DataMem} {writes : BitVec 64 → Prop}
    (n : Names) (o : AllowedipsProbe.Offsets)
    (same : EqualOutside writes before after)
    (apart : ∀ a, ReadBytes n o a → ¬writes a) :
    reconstruct n o before = reconstruct n o after := by
  apply reconstruct_congr
  · intro id base member
    apply decodeNode_congr
    intro offset size span path
    exact word_frame same path _ _ (fun a h => apart a (.inl ⟨id,base,member,offset,size,span,h⟩))
  · intro id base member
    exact word_frame same _ _ _ (fun a h => apart a (.inr ⟨id,base,member,h⟩))

#print axioms reconstruct_frame
end Binary.Pair.Trie
