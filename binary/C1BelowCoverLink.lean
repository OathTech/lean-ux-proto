import C1BelowCoverData
import C1BelowCoverFacts
import C1BelowSplitSelect
import C1BelowUndoBytes
import AllowedipsNodeResourceFrame

/-! Result C1, work package 3, covering path: small facts linking the
machine's reads to the decoded nodes: the selected bit as a `getLsbD`, the
separation of two named nodes, and the mapped parent word of an old node. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase AllowedipsChild
open Binary.Pair.Allowedips.Root

/-- `bt` on the byte: the selected bit. -/
theorem bit_selected (byte k : Nat) (kBound : k<8) :
    ((BitVec.ofNat 8 byte).getLsbD k).toNat=selected (byte%256) k := by
  unfold selected
  rw [BitVec.getLsbD_ofNat]
  simp only [kBound,decide_true,Bool.true_and,Nat.testBit,Nat.shiftRight_eq_div_pow]
  have : byte/2^k%2=byte%256/2^k%2 := by
    rcases (by omega : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7) with
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  rw [←this]
  rcases Nat.mod_two_eq_zero_or_one (byte/2^k) with h|h <;> simp [h]

theorem pairwise_map_members {α β : Type} {R : β → β → Prop} (f : α → β) :
    ∀ (l : List α), (l.map f).Pairwise R → ∀ x ∈ l, ∀ y ∈ l, x≠y → R (f x) (f y) ∨ R (f y) (f x)
  | [], _, x, member, _, _, _ => by cases member
  | head :: tail, pairwise, x, hx, y, hy, differ => by
    rw [List.map_cons,List.pairwise_cons] at pairwise
    rcases List.mem_cons.mp hx with rfl|hx' <;> rcases List.mem_cons.mp hy with rfl|hy'
    · exact absurd rfl differ
    · exact .inl (pairwise.1 _ (List.mem_map.mpr ⟨y,hy',rfl⟩))
    · exact .inr (pairwise.1 _ (List.mem_map.mpr ⟨x,hx',rfl⟩))
    · exact pairwise_map_members f tail pairwise.2 x hx' y hy' differ

/-- Two different named nodes do not overlap. -/
theorem nodes_apart {names : Allowedips.Names} (g : Geometry names nodeOffsets)
    {id id' address address' : Nat} (named : (id,address) ∈ names.trie.nodes)
    (named' : (id',address') ∈ names.trie.nodes) (differ : (id,address)≠(id',address')) :
    ∀ x, InRange (.ofNat 64 address) 72 x → ¬InRange (.ofNat 64 address') 72 x := by
  have pairwise := (List.pairwise_append.mp g.apart).1
  have first := g.bounded _ (node_allocation named)
  have second := g.bounded _ (node_allocation named')
  change address+72≤2^64 at first
  change address'+72≤2^64 at second
  have either := pairwise_map_members (fun p : NodeId×Nat => (p.2,nodeOffsets.nodeSize)) _ pairwise
    _ named _ named' differ
  have apart : address+72≤address' ∨ address'+72≤address := by
    rcases either with h|h
    · change disjointRanges address 72 address' 72=true at h
      simpa [disjointRanges] using h
    · change disjointRanges address' 72 address 72=true at h
      have := by simpa [disjointRanges] using h
      omega
  exact Undo.range_apart first second apart

/-- A resolved node address is a named node. -/
theorem named_of_address {nodes : List (Nat×Nat)} {id address : Nat}
    (resolved : Trie.address nodes (some id)=.ok address) : (id,address) ∈ nodes := by
  simp only [Trie.address] at resolved
  cases found : nodes.find? (·.1==id) with
  | none => rw [found] at resolved; cases resolved
  | some pair =>
    rw [found] at resolved
    obtain ⟨current,value⟩ := pair
    cases Except.ok.inj resolved
    have same : current=id := by simpa using List.find?_some found
    exact same ▸ List.mem_of_find?_eq_some found

/-- An old node's packed parent word is readable while the fresh node is pending. -/
theorem old_parent_mapped {names : Allowedips.Names} {entry : MachineData} {d : Device}
    {key cidr pid base : Nat} {memory : DataMem} {id address : Nat}
    (pending : NodeInit.Pending names entry d key cidr pid base memory)
    (related : Corresponds names nodeOffsets entry.dmem d)
    (named : (id,address) ∈ names.trie.nodes) :
    (memory.loadInt (.ofNat 64 (address+48)) 8).isSome=true := by
  obtain ⟨⟨current,actual⟩,_,read⟩ := (reconstruct_fields related).nodes.left (id,address) named
  have after := pending.nodes _ named _ read
  unfold decodeNode at after
  obtain ⟨core,_,after⟩ := bind_ok after
  obtain ⟨raw,rawRead,_⟩ := bind_ok after
  exact Option.isSome_of_eq_some (word_loadInt _ _ _ _ _ rawRead)

/-- A decoded node's two child words are readable. -/
theorem children_mapped {names : Trie.Names} {m : DataMem} {a : Nat} {node : Trie.Node}
    (decoded : Trie.decodeNode names nodeOffsets m a=.ok node) :
    (m.loadInt (.ofNat 64 (a+8)) 8).isSome=true ∧ (m.loadInt (.ofNat 64 (a+16)) 8).isSome=true := by
  obtain ⟨left,right,lp,rp,_,leftRead,_,rightRead,_⟩ := (Trie.decodeNode_fields decoded).children
  exact ⟨Option.isSome_of_eq_some (word_loadInt _ _ _ _ _ leftRead),
    Option.isSome_of_eq_some (word_loadInt _ _ _ _ _ rightRead)⟩

#print axioms named_of_address
#print axioms old_parent_mapped
#print axioms children_mapped
#print axioms bit_selected
#print axioms nodes_apart
end Binary.Statements.C1.Proof
