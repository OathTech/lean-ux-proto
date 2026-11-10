import C1TrunkReady
import PairAllowedipsFrame
import PairAllowedipsHeapFrame
import PairNextProof
/-! Result C1, package 2: the relation across the wrapper's sequence
increment. The landed frame lemmas (`reconstruct_frame`, `heap_frame`) ask
that no read span is written; here the table's sequence word is, and the
mirror's device is the one with the sequence advanced (`bump`). The two
congruence proofs follow `PairAllowedipsFrame.reconstruct_congr` and
`PairAllowedipsHeapFrame.internalListCheck_frame` (origin of the copied
steps), with the sequence word taken out of the unchanged set. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG

/-- The read spans other than the table's sequence word. -/
def keptSpans (names : Allowedips.Names) (o : AllowedipsProbe.Offsets) : List Pair.Span :=
  [(names.table+AllowedipsMutationLayout.root4,8),(names.table+AllowedipsMutationLayout.root6,8)] ++
  (names.trie.nodes.flatMap (fun (_,a) => (nodeFields o).map (fun (offset,size) => (a+offset,size))) ++
  names.trie.peers.flatMap (fun (_,a) => (peerFields o).map (fun (offset,size) => (a+offset,size))))

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem word_bound {m : DataMem} {path : String} {a bytes value : Nat}
    (read : word m path a bytes = .ok value) : a + bytes ≤ 2^64 := by
  by_cases bound : a + bytes ≤ 2^64
  · exact bound
  · simp [word, bound] at read

theorem word_of_load {m : DataMem} (path : String) {a bytes n : Nat} (bound : a + bytes ≤ 2^64)
    (load : m.loadInt (.ofNat 64 a) bytes = some (n : Int)) : word m path a bytes = .ok n := by
  unfold word
  simp only [bound, ↓reduceIte]
  cases h : m.loadBytes (.ofNat 64 a) bytes with
  | none => simp [Mem.loadInt, h] at load
  | some bs =>
    simp only [Mem.loadInt, h, Option.map_some, Option.some.injEq] at load
    simp only [load, Int.toNat_natCast]

theorem seq_next (seq : BitVec 64) (v : Nat) (x : UInt64) (value : seq.toNat = v)
    (held : v.toUInt64 = x) : (1+seq).toNat.toUInt64 = x + 1 := by
  rw [← held, ← value]
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  simp [Nat.toUInt64, BitVec.toNat_add, Nat.add_comm]

/-- Reconstruction after the sequence word advanced by one (modulo 2^64) and
nothing else that is read changed. -/
theorem reconstruct_bump {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {before after : DataMem}
    {d : Device} {writes : BitVec 64 → Prop} (seq : BitVec 64)
    (related : reconstruct names o before = .ok (target d))
    (same : EqualOutside writes before after)
    (apart : ∀ span ∈ keptSpans names o, ∀ a, span.contains a → ¬writes a)
    (seqBefore : before.loadInt (.ofNat 64 (names.table+AllowedipsMutationLayout.seq)) 8 =
      some (seq.toNat : Int))
    (seqAfter : after.loadInt (.ofNat 64 (names.table+AllowedipsMutationLayout.seq)) 8 =
      some ((1+seq).toNat : Int)) :
    reconstruct names o after = .ok (target (bump d)) := by
  have wordSame (base size : Nat) (member : (base,size) ∈ keptSpans names o) (path : String) :
      word after path base size = word before path base size :=
    (Trie.word_frame same path base size (apart _ member)).symm
  have nodeRead (id a offset size : Nat) (named : (id,a) ∈ names.trie.nodes)
      (field : (offset,size) ∈ nodeFields o) (path : String) :=
    wordSame (a+offset) size (List.mem_append_right _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨(id,a),named,List.mem_map.mpr ⟨(offset,size),field,rfl⟩⟩))) path
  have peerRead (id a offset size : Nat) (named : (id,a) ∈ names.trie.peers)
      (field : (offset,size) ∈ peerFields o) (path : String) :=
    wordSame (a+offset) size (List.mem_append_right _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨(id,a),named,List.mem_map.mpr ⟨(offset,size),field,rfl⟩⟩))) path
  have nodeLists : ∀ id a, (id,a) ∈ names.trie.nodes → ∀ path offset, offset=0 ∨ offset=8 →
      word after path (a+AllowedipsMutationLayout.peer_list+offset) 8=
        word before path (a+AllowedipsMutationLayout.peer_list+offset) 8 := by
    intro id a named path offset which
    rcases which with rfl | rfl
    · simpa only [Nat.add_zero] using nodeRead id a AllowedipsMutationLayout.peer_list 8 named
        (by simp [nodeFields]) path
    · simpa only [Nat.add_assoc] using nodeRead id a (AllowedipsMutationLayout.peer_list+8) 8 named
        (by simp [nodeFields]) path
  have heads : ∀ id a, (id,a) ∈ names.trie.peers → ∀ path offset, offset=0 ∨ offset=8 →
      word after path (a+AllowedipsMutationLayout.allowedips_list+offset) 8=
        word before path (a+AllowedipsMutationLayout.allowedips_list+offset) 8 := by
    intro id a named path offset which
    rcases which with rfl | rfl
    · simpa only [Nat.add_zero] using peerRead id a AllowedipsMutationLayout.allowedips_list 8 named
        (by simp [peerFields]) path
    · simpa only [Nat.add_assoc] using peerRead id a (AllowedipsMutationLayout.allowedips_list+8) 8 named
        (by simp [peerFields]) path
  have ns : names.trie.nodes.mapM (fun (id,a) => decodeNode names o after id a)=
      names.trie.nodes.mapM (fun (id,a) => decodeNode names o before id a) := by
    apply Trie.mapM_same
    rintro ⟨id,a⟩ member
    have core : Trie.decodeNode names.trie o after a = Trie.decodeNode names.trie o before a := by
      apply Trie.decodeNode_congr
      intro offset size field path
      exact nodeRead id a offset size member (List.mem_append_left _ field) path
    have parent := nodeRead id a AllowedipsMutationLayout.parent_bit_packed 8 member
      (by simp [nodeFields]) "node.parent"
    simp only [decodeNode,core,parent]
  have ps : names.trie.peers.mapM (fun (id,a) => decodePeer names o after id a)=
      names.trie.peers.mapM (fun (id,a) => decodePeer names o before id a) := by
    apply Trie.mapM_same
    rintro ⟨id,a⟩ member
    have first := heads id a member "peer.list.head" 0 (Or.inl rfl)
    simp only [Nat.add_zero] at first
    have count := peerRead id a o.peerRefcount 4 member (by simp [peerFields]) "peer.refcount"
    simp only [decodePeer,count,first,
      peerList_congr names after before _ (heads id a member) nodeLists]
  have t4 := wordSame (names.table+AllowedipsMutationLayout.root4) 8 (by simp [keptSpans]) "table.root4"
  have t6 := wordSame (names.table+AllowedipsMutationLayout.root6) 8 (by simp [keptSpans]) "table.root6"
  unfold Allowedips.reconstruct at related
  obtain ⟨_,hval,h⟩ := bind_ok related
  obtain ⟨w4,hw4,h⟩ := bind_ok h
  obtain ⟨r4,hp4,h⟩ := bind_ok h
  obtain ⟨w6,hw6,h⟩ := bind_ok h
  obtain ⟨r6,hp6,h⟩ := bind_ok h
  obtain ⟨v,hv,h⟩ := bind_ok h
  obtain ⟨nodes,hn,h⟩ := bind_ok h
  obtain ⟨peers,hp,h⟩ := bind_ok h
  have eq := Except.ok.inj h
  have value : seq.toNat = v := by
    have read := word_loadInt _ _ _ _ _ hv
    rw [seqBefore] at read
    exact Int.ofNat.inj (Option.some.inj read)
  have hv' := word_of_load "table.seq" (word_bound hv) seqAfter
  have next := seq_next seq v d.peerAllowedips.seq value (congrArg (·.table.seq) eq)
  have e4 : r4 = d.peerAllowedips.root4 := congrArg (·.table.root4) eq
  have e6 : r6 = d.peerAllowedips.root6 := congrArg (·.table.root6) eq
  have en : nodes = d.nodes.toList := congrArg (·.nodes) eq
  have ep : peers = d.peers.toList.map (fun (id,p) => (id,p.refcount,p.allowedipsList)) :=
    congrArg (·.peers) eq
  have ec : names.nextNode = d.nextNode := congrArg (·.nextNode) eq
  simp only [Allowedips.reconstruct, ns, ps, t4, t6, hv', hval, hw4, hp4, hw6, hp6, hn, hp, ok_bind]
  show Except.ok _ = Except.ok _
  rw [next, e4, e6, en, ep, ec]
  rfl

/-- The structural check does not read the sequence word. -/
theorem heap_bump {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {before after : DataMem}
    {d : Device} {writes : BitVec 64 → Prop}
    (same : EqualOutside writes before after)
    (apart : ∀ span ∈ keptSpans names o, ∀ a, span.contains a → ¬writes a) :
    heap names (target (bump d)) after = heap names (target d) before := by
  have checks : internalListCheck names before=internalListCheck names after := by
    funext id
    simp only [internalListCheck,Trie.address]
    cases found : names.trie.nodes.find? (·.1 == id) with
    | none => rfl
    | some pair =>
      rcases pair with ⟨pid,a⟩
      dsimp only [Bind.bind,Except.bind,Pure.pure,Except.pure]
      have named := List.mem_of_find?_eq_some found
      have read (offset : Nat) (field : (offset,8) ∈ nodeFields o) :
          readNat ⟨{dmem := before},0⟩ (a+offset) 8=
            readNat ⟨{dmem := after},0⟩ (a+offset) 8 := by
        have member : (a+offset,8) ∈ keptSpans names o :=
          List.mem_append_right _ (List.mem_append_left _
            (List.mem_flatMap.mpr ⟨(pid,a),named,List.mem_map.mpr ⟨(offset,8),field,rfl⟩⟩))
        have bytes := same.loadBytes (.ofNat 64 (a+offset)) 8 (by
          intro i hi
          exact apart _ member _ ⟨i,hi,rfl⟩)
        simp only [readNat,bytes]
      simp only [read AllowedipsMutationLayout.peer_list (by simp [nodeFields])]
      have next := read (AllowedipsMutationLayout.peer_list+8) (by simp [nodeFields])
      have next' : readNat ⟨{dmem := before},0⟩ (a+AllowedipsMutationLayout.peer_list+8) 8=
          readNat ⟨{dmem := after},0⟩ (a+AllowedipsMutationLayout.peer_list+8) 8 := by
        simpa only [Nat.add_assoc] using next
      rw [next']
  simp only [heap,checks]
  rfl

#print axioms reconstruct_bump
#print axioms heap_bump
end C1Trunk
