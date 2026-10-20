import AllowedipsHeapChecks
import PairForInCongr

namespace Binary.Pair.Trie
open Leanux Leanux.WG

/-- Proof names for the existing executable heap check's two traversals. -/
def rootCheck (nodes : List (NodeId×Node)) (root : Option NodeId) : Except String Unit := do
  if let some id := root then
    unless nodes.any (·.1==id) do throw s!"trie.root: absent node {id}"

def edgeStep (s : State) (roots : List (Option NodeId)) (id : NodeId) (node : Node)
    (edge : Option NodeId×Nat) (parents : List NodeId) : Except String (ForInStep (List NodeId)) := do
  let (child,bit) := edge
  if let some next := child then
    let some (_,n) := s.nodes.find? (·.1==next) | throw s!"trie.child: absent node {next}"
    if parents.contains next then throw s!"trie.parents: repeated child {next}"
    if roots.contains (some next) then throw s!"trie.parents: root {next} is also a child"
    unless n.width==node.width && node.cidr<n.cidr do
      throw s!"trie.measure: {id}->{next} does not increase CIDR in the same family"
    unless n.key/2^(node.width-node.cidr)==node.key/2^(node.width-node.cidr) do
      throw s!"trie.prefix: child {next} does not share parent {id}'s prefix"
    unless n.key/2^(node.width-1-node.cidr)%2==bit do
      throw s!"trie.branch: child {next} is on the wrong side of {id}"
    return .yield (next::parents)
  else return .yield parents

def nodeStep (s : State) (roots : List (Option NodeId)) (entry : NodeId×Node)
    (parents : List NodeId) : Except String (ForInStep (List NodeId)) := do
  let result ← forIn entry.2.children.toList.zipIdx parents (edgeStep s roots entry.1 entry.2)
  return .yield result

theorem heap_walk (s : State) (roots : List (Option NodeId)) :
    heap s roots=(do
      checkEach roots (rootCheck s.nodes)
      let _ ← forIn s.nodes [] (nodeStep s roots)
      pure ()) := by
  simp only [heap,checkEach,rootCheck,bind_assoc]
  congr 1
  apply forIn_congr_mem
  intro root _ before
  cases root with
  | none => rfl
  | some id => dsimp only; split <;> rfl

theorem nodeStep_yields {s roots entry before after} (run : nodeStep s roots entry before=.ok after) :
    ∃ next, after=.yield next := by
  obtain ⟨next,_,run⟩ := bind_ok run
  exact ⟨next,(Except.ok.inj run).symm⟩

theorem heap_root {s roots} (checked : heap s roots=.ok ()) {id}
    (member : some id ∈ roots) : ∃ node, (id,node) ∈ s.nodes := by
  rw [heap_walk] at checked
  obtain ⟨value,checked,_⟩ := bind_ok checked
  cases value
  have checked := (checkEach_ok roots _).mp checked (some id) member
  unfold rootCheck at checked
  obtain ⟨present,_⟩ := check_ok _ _ _ _ checked
  obtain ⟨⟨current,n⟩,member,same⟩ := List.any_eq_true.mp present
  have same : current=id := by simpa using same
  exact ⟨n,same ▸ member⟩

theorem nodeStep_append_leaf {s : State} {roots newRoots : List (Option NodeId)}
    {fresh : NodeId} {leaf : Node} (checked : heap s roots=.ok ())
    (rootFrame : ∀ id node, (id,node) ∈ s.nodes →
      newRoots.contains (some id)=roots.contains (some id))
    {id node} (member : (id,node) ∈ s.nodes) (parents : List NodeId) :
    nodeStep {s with nodes:=s.nodes++[(fresh,leaf)]} newRoots (id,node) parents=
      nodeStep s roots (id,node) parents := by
  unfold nodeStep
  congr 1
  apply forIn_congr_mem
  intro edge atEdge before
  rcases edge with ⟨child,bit⟩
  cases child with
  | none => rfl
  | some next =>
    have atChild : some next ∈ node.children.toList := by
      exact List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp atEdge)
    obtain ⟨target,present,_⟩ := heap_edges checked id node member next atChild
    have found : ∃ pair, s.nodes.find? (·.1==next)=some pair := by
      exact Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨(next,target),present,by simp⟩)
    obtain ⟨pair,found⟩ := found
    simp only [edgeStep,List.find?_append,found,Option.some_or,rootFrame next target present]

theorem heap_append_leaf {s : State} {roots newRoots : List (Option NodeId)}
    {fresh : NodeId} {leaf : Node} (checked : heap s roots=.ok ())
    (noChildren : leaf.children=#[none,none])
    (rootFrame : ∀ id node, (id,node) ∈ s.nodes →
      newRoots.contains (some id)=roots.contains (some id))
    (rootsPresent : ∀ id, some id ∈ newRoots →
      ∃ node, (id,node) ∈ s.nodes++[(fresh,leaf)]) :
    heap {s with nodes:=s.nodes++[(fresh,leaf)]} newRoots=.ok () := by
  have rootChecks : checkEach newRoots (rootCheck (s.nodes++[(fresh,leaf)]))=.ok () := by
    apply (checkEach_ok _ _).mpr
    intro root member
    cases root with
    | none => rfl
    | some id =>
      obtain ⟨node,present⟩ := rootsPresent id member
      apply check_of
      · exact List.any_eq_true.mpr ⟨(id,node),present,by simp⟩
      · rfl
  have original := checked
  rw [heap_walk] at checked ⊢
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨parents,walk,_⟩ := bind_ok checked
  rw [rootChecks]
  dsimp only [Bind.bind,Except.bind]
  have oldWalk : forIn s.nodes [] (nodeStep {s with nodes:=s.nodes++[(fresh,leaf)]} newRoots)=.ok parents := by
    rw [forIn_congr_mem (fun entry member initial =>
      nodeStep_append_leaf original rootFrame member initial)]
    exact walk
  rw [forIn_append_yield (fun _ _ _ _ => nodeStep_yields) oldWalk]
  simp only [List.forIn_cons,List.forIn_nil,nodeStep,noChildren]
  rfl

#print axioms heap_append_leaf
end Binary.Pair.Trie
