import C1TrunkRootBody
import PairHeapProof
import AllowedipsPlacementChecked
/-! Result C1, package 2: source-side facts for the paths through the walk.
What `step`'s case says of its inputs, what `ordered` and `walk` say of the
root and the placed node, the landed `TrieHeap` without the executable
`callInput`, and the placed node's address from the loop's cursor. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem step_slot (d : Device) (family : Nat) :
    slotOf (bump d) (if family == 4 then Slot.root4 else Slot.root6) =
      (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) := by
  by_cases four : (family == 4) = true <;> simp [four, slotOf, bump]

/-- A step that reached the walk: the prefix fits and the root is there. -/
theorem step_walked {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool}
    (h1 : (step d family key cidr pid placed exact outcomes).case ≠ .tooLong)
    (h2 : (step d family key cidr pid placed exact outcomes).case ≠ .rootNoMem)
    (h3 : (step d family key cidr pid placed exact outcomes).case ≠ .root) :
    cidr ≤ (if family == 4 then 32 else 128) ∧
    ∃ rootId, (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some rootId := by
  by_cases long : cidr > (if family == 4 then 32 else 128)
  · exfalso
    apply h1
    simp only [step, long, ↓reduceIte]
  · refine ⟨by omega,?_⟩
    cases root : (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) with
    | some rootId => exact ⟨rootId,rfl⟩
    | none =>
      exfalso
      unfold step at h2 h3
      simp only [long, ↓reduceIte, step_slot, root] at h2 h3
      cases outcomes with
      | nil => exact h2 rfl
      | cons outcome rest =>
        cases outcome
        · exact h2 rfl
        · exact h3 rfl

/-- The same, from the case as a disjunction. -/
theorem step_walked_of {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool}
    (hc : (step d family key cidr pid placed exact outcomes).case = .exact ∨
      (step d family key cidr pid placed exact outcomes).case = .nodeNoMem ∨
      (step d family key cidr pid placed exact outcomes).case = .child ∨
      (step d family key cidr pid placed exact outcomes).case = .cover ∨
      (step d family key cidr pid placed exact outcomes).case = .split ∨
      (step d family key cidr pid placed exact outcomes).case = .splitNoMem) :
    cidr ≤ (if family == 4 then 32 else 128) ∧
    ∃ rootId, (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some rootId := by
  apply step_walked <;> rcases hc with h | h | h | h | h | h <;> rw [h] <;> decide

/-- `step`'s device for an exact match on the stored node `n` at `id`. -/
def exactDevice (d0 : Device) (pid : Nat) (id : NodeId) (n : AipNode) : Device :=
  addTail (delete {d0 with nodes := d0.nodes.insert id {n with peer := some pid}} id) pid id

theorem step_exact {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool}
    (hc : (step d family key cidr pid placed exact outcomes).case = .exact) :
    exact = true ∧
    step d family key cidr pid placed exact outcomes =
      (match placed.bind fun id => ((bump d).nodes.get? id).map fun n => (id,n) with
      | some (id,n) => ⟨.exact,0,exactDevice (bump d) pid id n,0⟩
      | none => ⟨.exact,0,bump d,0⟩) := by
  obtain ⟨bound,rootId,root⟩ := step_walked_of (.inl hc)
  have long : ¬cidr > (if family == 4 then 32 else 128) := by omega
  unfold step at hc ⊢
  simp only [long, ↓reduceIte, step_slot, root] at hc ⊢
  cases exact with
  | true => exact ⟨rfl,rfl⟩
  | false =>
    exfalso
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    repeat' split at hc
    all_goals first | cases hc | simp at hc

theorem step_nodeNoMem {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool}
    (hc : (step d family key cidr pid placed exact outcomes).case = .nodeNoMem) :
    exact = false ∧ outcomes.head? ≠ some true ∧
    step d family key cidr pid placed exact outcomes = ⟨.nodeNoMem,-ENOMEM,bump d,1⟩ := by
  obtain ⟨bound,rootId,root⟩ := step_walked_of (.inr (.inl hc))
  have long : ¬cidr > (if family == 4 then 32 else 128) := by omega
  unfold step at hc ⊢
  simp only [long, ↓reduceIte, step_slot, root] at hc ⊢
  cases exact with
  | true =>
    exfalso
    simp only [↓reduceIte] at hc
    repeat' split at hc
    all_goals first | cases hc | simp at hc
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    cases outcomes with
    | nil =>
      refine ⟨rfl,by simp,?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
    | cons outcome rest =>
      cases outcome
      · refine ⟨rfl,by simp,?_⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
      · exfalso
        simp only at hc
        repeat' split at hc
        all_goals first | cases hc | simp at hc

theorem step_child {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool}
    (hc : (step d family key cidr pid placed exact outcomes).case = .child) :
    exact = false ∧ outcomes.head? = some true ∧
    ∃ rootId, (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some rootId ∧
    ((below (bump d) (some rootId) key placed).bind fun id =>
      ((bump d).nodes.get? id).map fun n => (id,n)) = none ∧
    step d family key cidr pid placed exact outcomes =
      (match placed with
      | some p => ⟨.child,0,chooseConnect (addTail (alloc (bump d) (newNode key cidr
          (if family == 4 then 32 else 128) (some pid))) pid (bump d).nextNode) p (bump d).nextNode,1⟩
      | none => ⟨.child,0,addTail (alloc (bump d) (newNode key cidr
          (if family == 4 then 32 else 128) (some pid))) pid (bump d).nextNode,1⟩) := by
  obtain ⟨bound,rootId,root⟩ := step_walked_of (.inr (.inr (.inl hc)))
  have long : ¬cidr > (if family == 4 then 32 else 128) := by omega
  unfold step at hc ⊢
  simp only [long, ↓reduceIte, step_slot, root] at hc ⊢
  cases exact with
  | true =>
    exfalso
    simp only [↓reduceIte] at hc
    repeat' split at hc
    all_goals first | cases hc | simp at hc
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    cases outcomes with
    | nil => cases hc
    | cons outcome rest =>
      cases outcome
      · cases hc
      · simp only at hc
        cases hb : ((below (bump d) (some rootId) key placed).bind fun id =>
            ((bump d).nodes.get? id).map fun n => (id,n)) with
        | none =>
          refine ⟨rfl,by simp,rootId,rfl,hb,?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases placed <;> rfl
        | some pair =>
          exfalso
          simp only [hb] at hc
          repeat' split at hc
          all_goals first | cases hc | simp at hc

theorem step_below {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool}
    (hc : (step d family key cidr pid placed exact outcomes).case = .cover ∨
      (step d family key cidr pid placed exact outcomes).case = .split ∨
      (step d family key cidr pid placed exact outcomes).case = .splitNoMem) :
    exact = false ∧ outcomes.head? = some true := by
  obtain ⟨bound,rootId,root⟩ := step_walked_of
    (hc.elim (fun h => .inr (.inr (.inr (.inl h)))) (fun h => h.elim
      (fun h => .inr (.inr (.inr (.inr (.inl h))))) (fun h => .inr (.inr (.inr (.inr (.inr h)))))))
  have long : ¬cidr > (if family == 4 then 32 else 128) := by omega
  unfold step at hc
  simp only [long, ↓reduceIte, step_slot, root] at hc
  cases exact with
  | true =>
    exfalso
    simp only [↓reduceIte] at hc
    rcases hc with hc | hc | hc <;>
      (repeat' split at hc) <;> first | cases hc | simp at hc
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    cases outcomes with
    | nil => rcases hc with hc | hc | hc <;> cases hc
    | cons outcome rest =>
      cases outcome
      · rcases hc with hc | hc | hc <;> cases hc
      · exact ⟨rfl,rfl⟩

/-- What `ordered` says of each stored node. -/
theorem ordered_node {d : Device} (ord : ordered d = true) {id : NodeId} {n : AipNode}
    (present : d.nodes.get? id = some n) :
    (n.bitlen = 32 ∨ n.bitlen = 128) ∧ n.cidr ≤ n.bitlen ∧ n.bits < 2^n.bitlen ∧ n.bit.size = 2 := by
  unfold ordered at ord
  rw [Bool.and_eq_true] at ord
  have member : (id,n) ∈ d.nodes.toList := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present
  have h := List.all_eq_true.mp ord.1 (id,n) member
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1,h.1.1.1.2,h.1.1.2,h.1.2⟩

/-- The family's root is a stored node of the family's width. -/
theorem ordered_root {d : Device} (ord : ordered d = true) {family : Nat} {rootId : NodeId}
    (root : (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some rootId) :
    ∃ node, (bump d).nodes.get? rootId = some node ∧ node.bitlen = (if family == 4 then 32 else 128) := by
  unfold ordered at ord
  rw [Bool.and_eq_true] at ord
  have h := ord.2
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  show ∃ node, d.nodes.get? rootId = some node ∧ _
  by_cases four : (family == 4) = true
  · simp only [four, ↓reduceIte] at root ⊢
    have h4 := h.1
    rw [root] at h4
    simp only at h4
    cases hg : d.nodes.get? rootId with
    | none => rw [hg] at h4; cases h4
    | some node =>
      rw [hg] at h4
      exact ⟨node,rfl,by simpa using h4⟩
  · simp only [four, Bool.false_eq_true, ↓reduceIte] at root ⊢
    have h6 := h.2
    rw [root] at h6
    simp only at h6
    cases hg : d.nodes.get? rootId with
    | none => rw [hg] at h6; cases h6
    | some node =>
      rw [hg] at h6
      exact ⟨node,rfl,by simpa using h6⟩

/-- Origin: the landed `Trie.trieHeap_of_checks` (`PairHeapProof.lean`),
copied, with the three facts `callInput_ok` extracts from the executable
`callInput` taken as hypotheses in its place. -/
theorem trieHeap_of_facts {names : Trie.Names} {o : AllowedipsProbe.Offsets}
    {m : DataMem} {d : Device} {root : Option NodeId} {bits query : Nat}
    (related : Trie.Corresponds names o m d)
    (checked : Trie.heap (Trie.target d) [d.peerAllowedips.root4,d.peerAllowedips.root6] = .ok ())
    (family : bits = 32 ∨ bits = 128) (bounded : query < 2^bits)
    (rootWidth : ∀ id, root = some id → ∃ node, d.nodes.get? id = some node ∧ node.bitlen = bits) :
    AllowedipsRelation.TrieHeap m (Trie.interpretation names.nodes) (Trie.interpretation names.peers)
      (fun id => d.nodes.get? id) root bits query := by
  have fields := Trie.reconstruct_fields related
  have reachable : ∀ id, AllowedipsRelation.Reached (fun id => d.nodes.get? id) root bits query id →
      ∃ node, d.nodes.get? id = some node ∧ node.bitlen = bits := by
    intro id reached
    induction reached with
    | root id atRoot => exact rootWidth id atRoot
    | child id node next reached present matching short link ih =>
      obtain ⟨parent,parentAt,width⟩ := ih
      have same : parent = node := Option.some.inj (parentAt.symm.trans present)
      subst parent
      have member : (id,Trie.targetNode node) ∈ (Trie.target d).nodes :=
        List.mem_map.mpr ⟨(id,node),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present,rfl⟩
      have childMember : some next ∈ (Trie.targetNode node).children.toList :=
        by simpa only [Trie.targetNode,Array.mem_toList_iff] using Array.mem_of_getElem? link
      obtain ⟨child,found,widthEq⟩ := Trie.heap_edges checked id (Trie.targetNode node) member next childMember
      obtain ⟨source,present,nodeEq⟩ := Trie.target_node found
      exact ⟨source,present,(congrArg Trie.Node.width nodeEq).trans (widthEq.trans width)⟩
  refine ⟨family,bounded,?_⟩
  intro id reached
  obtain ⟨node,present,width⟩ := reachable id reached
  obtain ⟨a,member,decoded⟩ := fields.node present
  exact ⟨node,present,Trie.decoded_node_fields fields member decoded width bounded⟩

/-- What `walk` says of a placed node. -/
theorem walk_placed {d' : Device} {root : Option NodeId} {key cidr bits : Nat} {id : NodeId}
    {exact : Bool} (h : walk d' root key cidr bits (some id) exact = true) :
    ∃ p, d'.nodes.get? id = some p ∧ p.bitlen = bits ∧ p.cidr ≤ cidr ∧
      (exact = true ↔ p.cidr = cidr) ∧ key / 2^(bits-p.cidr) = p.bits / 2^(bits-p.cidr) := by
  unfold walk at h
  rw [Bool.and_eq_true] at h
  have h1 := h.1
  simp only at h1
  cases hg : d'.nodes.get? id with
  | none => rw [hg] at h1; cases h1
  | some p =>
    rw [hg] at h1
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    refine ⟨p,rfl,h1.1.1.1,h1.1.1.2,?_,h1.2⟩
    have e := h1.1.2
    cases exact
    · simpa using e.symm
    · simpa using e.symm

/-- Nothing placed: the walk did not end on an exact match. -/
theorem walk_none {d' : Device} {root : Option NodeId} {key cidr bits : Nat}
    {exact : Bool} (h : walk d' root key cidr bits none exact = true) : exact = false := by
  unfold walk at h
  rw [Bool.and_eq_true] at h
  simpa using h.1

/-- Every stored node has an address. -/
theorem node_named {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {m : DataMem} {d' : Device}
    (related : Allowedips.Corresponds names o m d') {id : NodeId} {n : AipNode}
    (present : d'.nodes.get? id = some n) : ∃ a, (id,a) ∈ names.trie.nodes := by
  obtain ⟨a,member,_⟩ := (Trie.reconstruct_fields related.trie).node present
  exact ⟨a,member⟩

/-- The loop's cursor register is the placed node's address. -/
theorem placed_address {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {m : DataMem} {d' : Device}
    (related : Allowedips.Corresponds names o m d') {placed : Option NodeId}
    (present : ∀ id, placed = some id → ∃ n, d'.nodes.get? id = some n)
    {rbx : UInt64} (held : rbx = Placement.ptr (Trie.interpretation names.trie.nodes) placed) :
    Trie.address names.trie.nodes placed = .ok rbx.toNat ∧
    ∀ id, placed = some id → (id,rbx.toNat) ∈ names.trie.nodes := by
  have fields := Trie.reconstruct_fields related.trie
  cases placed with
  | none =>
    subst held
    exact ⟨rfl,fun _ h => by cases h⟩
  | some id =>
    obtain ⟨n,hn⟩ := present id rfl
    obtain ⟨a,member⟩ := node_named related hn
    have found := Trie.find_identity fields.nodeIds member
    have range := fields.nodeRange id a member
    have value : rbx.toNat = a := by
      subst held
      show (AllowedipsRelation.pointer (Trie.interpretation names.trie.nodes) (some id)).toNat = a
      rw [Trie.address_value (names := names.trie.nodes) (id := some id) (raw := a)
        (by simp only [Trie.address, found]; rfl), BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rw [value]
    refine ⟨by simp only [Trie.address, found]; rfl,?_⟩
    intro id' h
    cases h
    exact member

#print axioms step_walked
#print axioms step_walked_of
#print axioms step_exact
#print axioms step_nodeNoMem
#print axioms step_child
#print axioms step_below
#print axioms ordered_node
#print axioms ordered_root
#print axioms trieHeap_of_facts
#print axioms walk_placed
#print axioms walk_none
#print axioms node_named
#print axioms placed_address
end C1Trunk
