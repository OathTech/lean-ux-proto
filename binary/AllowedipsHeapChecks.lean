import AllowedipsTrieShape

namespace Binary.Pair

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

private theorem error_bind (error : ε) (f : α → Except ε β) :
    ((Except.error error : Except ε α) >>= f)=.error error := rfl

def checkEach (xs : List α) (f : α → Except ε Unit) : Except ε Unit := do
  for x in xs do f x

theorem checkEach_cons (x : α) (xs : List α) (f : α → Except ε Unit) :
    checkEach (x::xs) f=(f x >>= fun _ => checkEach xs f) := by
  simp only [checkEach,List.forIn_cons,bind_assoc]
  congr 1

theorem checkEach_ok (xs : List α) (f : α → Except ε Unit) :
    checkEach xs f=.ok () ↔ ∀ x ∈ xs, f x=.ok () := by
  induction xs with
  | nil => simp [checkEach,Pure.pure,Except.pure,ok_bind]
  | cons x xs ih =>
    rw [checkEach_cons]
    cases first : f x with
    | error e => simp [first,error_bind]
    | ok value =>
      cases value
      simpa only [ok_bind,List.mem_cons,forall_eq_or_imp,first,eq_self,true_and] using ih

namespace Allowedips
open Leanux Leanux.WG

def structureCheck (s : State) (id : NodeId) (n : AipNode) : Except String Unit := do
  let roots := [(s.table.root4,Slot.root4,32),(s.table.root6,Slot.root6,128)]
  let mut incoming := []
  for (root,slot,width) in roots do
    if root == some id then
      unless n.bitlen == width do throw "heap.root-family"
      incoming := slot::incoming
  for (pid,p) in s.nodes do
    for (child,bit) in p.bit.toList.zipIdx do
      if child == some id then incoming := .child pid bit::incoming
  unless incoming == [n.parent] do throw s!"heap.parent[{id}]: {repr incoming}"

def ownershipCheck (names : Names) (s : State) (m : DataMem) (id : NodeId) (n : AipNode) : Except String Unit := do
  unless owners s id == n.peer.toList do throw s!"heap.peer-membership[{id}]"
  if n.peer.isNone then internalListCheck names m id

theorem heap_decompose (names : Names) (s : State) (m : DataMem) :
    heap names s m=(do
      Trie.heap ⟨s.nodes.map (fun (id,n) => (id,Trie.targetNode n)),
        s.peers.map (fun (id,count,_) => (id,count))⟩ [s.table.root4,s.table.root6]
      checkEach s.nodes fun (id,n) => do
        structureCheck s id n
        ownershipCheck names s m id n) := by
  simp only [heap,checkEach,structureCheck,ownershipCheck,owners,bind_assoc]
  congr 1
  funext value
  congr 1
  congr 1
  funext entry before
  congr 1
  funext incoming
  congr 1
  funext incoming
  split <;> split <;> split <;> rfl

theorem heap_checks (names : Names) (s : State) (m : DataMem) :
    heap names s m=.ok () ↔
      Trie.heap ⟨s.nodes.map (fun (id,n) => (id,Trie.targetNode n)),
        s.peers.map (fun (id,count,_) => (id,count))⟩ [s.table.root4,s.table.root6]=.ok () ∧
      ∀ id n, (id,n) ∈ s.nodes → structureCheck s id n=.ok () ∧ ownershipCheck names s m id n=.ok () := by
  rw [heap_decompose]
  cases core : Trie.heap ⟨s.nodes.map (fun (id,n) => (id,Trie.targetNode n)),
    s.peers.map (fun (id,count,_) => (id,count))⟩ [s.table.root4,s.table.root6] with
  | error error => simp [error_bind]
  | ok value =>
    cases value
    simp only [ok_bind,checkEach_ok,eq_self,true_and]
    constructor
    · intro run id n member
      obtain ⟨value,shape,ownership⟩ := bind_ok (run (id,n) member)
      cases value
      exact ⟨shape,ownership⟩
    · rintro checks ⟨id,n⟩ member
      obtain ⟨shape,ownership⟩ := checks id n member
      simp only [shape,ok_bind,ownership]

theorem structureCheck_mapPeer (s : State) (focus pid id : Nat) (node : AipNode) :
    structureCheck (reassign focus pid s) id {node with peer := some pid}=structureCheck s id node := by
  simp only [structureCheck,reassign,List.forIn_map,reassignNode]
  congr 1
  funext incoming
  congr 1
  congr 1
  funext entry before
  by_cases same : entry.1=focus <;> simp [same]

#print axioms heap_checks
#print axioms structureCheck_mapPeer
end Allowedips
end Binary.Pair
