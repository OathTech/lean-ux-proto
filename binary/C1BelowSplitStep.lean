import C1Interfaces
import C1BelowSplitRootSource

/-! Result C1, work package 3, the split path's source side: `C1Step.step`'s
device for case `.split` is trial T5's installed device (as devices, hence
also up to `Allowedips.target`), and T5's ordering hypotheses follow from
`ordered` and `walk`. Pure lemmas about the mirror's device; no machine. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.Pair.Allowedips.C1Split

theorem addTail_nextNode (d : Device) (pid : PeerId) (id : NodeId) :
    (addTail d pid id).nextNode = d.nextNode := by
  unfold addTail
  split <;> rfl

/-- What `st.case = .split` says about the arguments of `step`. -/
theorem step_split_inv {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool} {bits : Nat} {root : Slot}
    (width : bits = if family == 4 then 32 else 128)
    (slot : root = if family == 4 then Slot.root4 else Slot.root6)
    (case : (step d family key cidr pid placed exact outcomes).case = .split) :
    ∃ rootId downId down rest,
      cidr ≤ bits ∧ slotOf (bump d) root = some rootId ∧ exact = false ∧
      outcomes = true :: true :: rest ∧
      below (bump d) (some rootId) key placed = some downId ∧ (bump d).nodes.get? downId = some down ∧
      cidr ≠ min cidr (AllowedipsRelation.common bits down.bits key) ∧
      (step d family key cidr pid placed exact outcomes).device =
        placed.elim
          (connect (chooseConnect (chooseConnect
              (alloc (addTail (alloc (bump d) (newNode key cidr bits (some pid))) pid (bump d).nextNode)
                (newNode key (min cidr (AllowedipsRelation.common bits down.bits key)) bits none))
              ((bump d).nextNode+1) downId) ((bump d).nextNode+1) (bump d).nextNode) root ((bump d).nextNode+1))
          (fun p => chooseConnect (chooseConnect (chooseConnect
              (alloc (addTail (alloc (bump d) (newNode key cidr bits (some pid))) pid (bump d).nextNode)
                (newNode key (min cidr (AllowedipsRelation.common bits down.bits key)) bits none))
              ((bump d).nextNode+1) downId) ((bump d).nextNode+1) (bump d).nextNode) p ((bump d).nextNode+1)) ∧
      (step d family key cidr pid placed exact outcomes).answer = 0 ∧
      (step d family key cidr pid placed exact outcomes).consumed = 2 := by
  subst width slot
  by_cases long : cidr > (if family == 4 then 32 else 128)
  · simp only [step,long,↓reduceIte] at case
    cases case
  cases rootEq : slotOf (bump d) (if family == 4 then Slot.root4 else Slot.root6) with
  | none =>
    simp only [step,long,rootEq,↓reduceIte] at case
    split at case <;> cases case
  | some rootId =>
    cases exact with
    | true =>
      simp only [step,long,rootEq,↓reduceIte] at case
      split at case <;> cases case
    | false =>
      rcases outcomes with _|⟨_|_,rest⟩
      · simp only [step,long,rootEq,↓reduceIte,Bool.false_eq_true] at case
        cases case
      · simp only [step,long,rootEq,↓reduceIte,Bool.false_eq_true] at case
        cases case
      cases belowEq : (below (bump d) (some rootId) key placed).bind fun id =>
          ((bump d).nodes.get? id).map fun n => (id,n) with
      | none =>
        simp only [step,long,rootEq,belowEq,↓reduceIte,Bool.false_eq_true] at case
        split at case <;> cases case
      | some pair =>
        obtain ⟨downId,down⟩ := pair
        obtain ⟨id,found,node⟩ := Option.bind_eq_some_iff.mp belowEq
        obtain ⟨n,hasNode,same⟩ := Option.map_eq_some_iff.mp node
        cases same
        by_cases covers : cidr = min cidr (AllowedipsRelation.common (if family == 4 then 32 else 128) down.bits key)
        · have yes : (cidr == min cidr (AllowedipsRelation.common (if family == 4 then 32 else 128) down.bits key)) = true :=
            beq_iff_eq.mpr covers
          simp only [step,long,rootEq,belowEq,yes,↓reduceIte,Bool.false_eq_true] at case
          cases case
        have no : (cidr == min cidr (AllowedipsRelation.common (if family == 4 then 32 else 128) down.bits key)) = false :=
          beq_eq_false_iff_ne.mpr covers
        rcases rest with _|⟨_|_,rest⟩
        · simp only [step,long,rootEq,belowEq,no,↓reduceIte,Bool.false_eq_true] at case
          cases case
        · simp only [step,long,rootEq,belowEq,no,↓reduceIte,Bool.false_eq_true] at case
          cases case
        refine ⟨rootId,downId,down,rest,Nat.le_of_not_gt long,rfl,rfl,rfl,found,hasNode,covers,?_,?_,?_⟩
        · simp only [step,long,rootEq,belowEq,no,↓reduceIte,Bool.false_eq_true]
          cases placed <;> simp only [Option.elim,addTail_nextNode] <;> rfl
        · simp only [step,long,rootEq,belowEq,no,↓reduceIte,Bool.false_eq_true]
        · simp only [step,long,rootEq,belowEq,no,↓reduceIte,Bool.false_eq_true]

#print axioms step_split_inv
/-- Parent sub-case: `step`'s three connections after the two allocations
are T5's `intermediateInstalled`, as devices. `D` is the device with the
sequence incremented. The three directions are `C1Step.side` of the internal
node on the node below, of the internal node on the new leaf, and of the
parent on the internal node (whose key is the leaf's). -/
theorem split_device_parent (D : Device) (key cidr least bits pid downId p : Nat)
    (down pnode : AipNode) (owner : Peer)
    (hasPeer : D.peers[pid]? = some owner)
    (hasDown : D.nodes[downId]? = some down) (hasParent : D.nodes[p]? = some pnode)
    (downBelow : downId < D.nextNode) (parentBelow : p < D.nextNode) (different : downId ≠ p) :
    chooseConnect (chooseConnect (chooseConnect
        (alloc (addTail (alloc D (newNode key cidr bits (some pid))) pid D.nextNode)
          (newNode key least bits none))
        (D.nextNode+1) downId) (D.nextNode+1) D.nextNode) p (D.nextNode+1) =
      intermediateInstalled D downId (down.bits/2^(bits-1-least)%2) (key/2^(bits-1-least)%2) p
        (key/2^(pnode.bitlen-1-pnode.cidr)%2) key cidr least bits pid down pnode owner := by
  have f1 : D.nextNode≠downId := Ne.symm (Nat.ne_of_lt downBelow)
  have f2 : D.nextNode+1≠downId := Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt downBelow))
  have f3 : D.nextNode≠p := Ne.symm (Nat.ne_of_lt parentBelow)
  have f4 : D.nextNode+1≠p := Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt parentBelow))
  simp [chooseConnect,connect,setSlot,alloc,addTail,side,newNode,intermediateInstalled,
    hasPeer,hasDown,hasParent,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem_insert,
    different,f1,f2,f3,f4,Ne.symm f1,Ne.symm f2]

#print axioms split_device_parent

/-- Root sub-case: the two connections and the root publication are T5's
`intermediateRootInstalled`, as devices. -/
theorem split_device_root (D : Device) (v4 : Bool) (key cidr least bits pid downId : Nat)
    (down : AipNode) (owner : Peer)
    (hasPeer : D.peers[pid]? = some owner) (hasDown : D.nodes[downId]? = some down)
    (downBelow : downId < D.nextNode) :
    connect (chooseConnect (chooseConnect
        (alloc (addTail (alloc D (newNode key cidr bits (some pid))) pid D.nextNode)
          (newNode key least bits none))
        (D.nextNode+1) downId) (D.nextNode+1) D.nextNode)
        (if v4 then Slot.root4 else Slot.root6) (D.nextNode+1) =
      intermediateRootInstalled D v4 downId (down.bits/2^(bits-1-least)%2) (key/2^(bits-1-least)%2)
        key cidr least bits pid down owner := by
  have f1 : D.nextNode≠downId := Ne.symm (Nat.ne_of_lt downBelow)
  have f2 : D.nextNode+1≠downId := Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt downBelow))
  cases v4 <;>
  simp [chooseConnect,connect,setSlot,alloc,addTail,side,newNode,intermediateRootInstalled,
    hasPeer,hasDown,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem_insert,
    f1,f2,Ne.symm f1,Ne.symm f2]

#print axioms split_device_root

end Binary.Statements.C1.Proof
