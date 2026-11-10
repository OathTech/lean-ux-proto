import C1BelowSplitStep

/-! Result C1, work package 3, the split path: trial T5's ordering
hypotheses derived from `C1Invariant.walk` and `ordered`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.Pair.Allowedips.C1Split

/-- T5's ordering and side hypotheses for the parent sub-case, with
`common := least`, `width := bits`, `b1 := down.bits/2^(bits-1-least)%2`,
`b2 := key/2^(bits-1-least)%2`, `direction := key/2^(pnode.bitlen-1-pnode.cidr)%2`
(so T5's `side`, `downSide`, `leafSide` are `rfl`). -/
structure SplitParentFacts (D : Device) (key cidr bits least p downId : Nat)
    (down pnode : AipNode) : Prop where
  hasParent : D.nodes.get? p = some pnode
  different : downId ≠ p
  occupied : pnode.bit[key/2^(pnode.bitlen-1-pnode.cidr)%2]? = some (some downId)
  sameWidth : bits = pnode.bitlen
  measure : pnode.cidr < least
  prefixEq : key/2^(pnode.bitlen-pnode.cidr) = pnode.bits/2^(pnode.bitlen-pnode.cidr)
  downWidth : down.bitlen = bits
  downMeasure : least < down.cidr
  leafMeasure : least < cidr
  proper : least < bits
  downPrefix : down.bits/2^(bits-least) = key/2^(bits-least)
  sides : down.bits/2^(bits-1-least)%2 ≠ key/2^(bits-1-least)%2

theorem split_parent_facts {D : Device} {root : Option NodeId} {key cidr bits p downId : Nat}
    {down : AipNode}
    (walked : walk D root key cidr bits (some p) false = true)
    (found : below D root key (some p) = some downId)
    (hasDown : D.nodes.get? downId = some down)
    (notCover : cidr ≠ min cidr (AllowedipsRelation.common bits down.bits key)) :
    ∃ pnode, SplitParentFacts D key cidr bits (min cidr (AllowedipsRelation.common bits down.bits key))
      p downId down pnode := by
  unfold walk at walked
  cases hasParent : D.nodes.get? p with
  | none => simp only [hasParent,Bool.false_and,Bool.false_eq_true] at walked
  | some pnode =>
    simp only [hasParent,found,hasDown,Bool.false_or,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,
      Bool.or_eq_true,bne_iff_ne,Bool.false_eq,beq_eq_false_iff_ne] at walked
    obtain ⟨⟨⟨⟨width,_⟩,_⟩,prefixEq⟩,⟨⟨⟨downWidth,downMeasure⟩,downPrefix⟩,measure⟩,branch⟩ := walked
    have shorter : AllowedipsRelation.common bits down.bits key < cidr := by omega
    have least : min cidr (AllowedipsRelation.common bits down.bits key) =
        AllowedipsRelation.common bits down.bits key := by omega
    have differ := branch.resolve_left (by omega)
    have occupied : pnode.bit[key/2^(pnode.bitlen-1-pnode.cidr)%2]? = some (some downId) := by
      unfold below at found
      simp only [hasParent] at found
      exact Option.join_eq_some_iff.mp found
    refine ⟨pnode,hasParent,?_,occupied,width.symm,measure,by rw [width]; exact prefixEq,downWidth,
      downMeasure,by omega,by omega,downPrefix,by rw [least]; exact differ.2⟩
    intro same
    subst same
    have equal : down = pnode := Option.some.inj (hasDown.symm.trans hasParent)
    subst equal
    omega

#print axioms split_parent_facts

/-- T5's ordering hypotheses for the root sub-case (same instantiation). -/
structure SplitRootFacts (key cidr bits least : Nat) (down : AipNode) : Prop where
  downWidth : down.bitlen = bits
  downMeasure : least < down.cidr
  leafMeasure : least < cidr
  proper : least < bits
  downPrefix : down.bits/2^(bits-least) = key/2^(bits-least)
  sides : down.bits/2^(bits-1-least)%2 ≠ key/2^(bits-1-least)%2

theorem split_root_facts {D : Device} {key cidr bits downId : Nat} {down : AipNode}
    (walked : walk D (some downId) key cidr bits none false = true)
    (hasDown : D.nodes.get? downId = some down)
    (notCover : cidr ≠ min cidr (AllowedipsRelation.common bits down.bits key)) :
    SplitRootFacts key cidr bits (min cidr (AllowedipsRelation.common bits down.bits key)) down := by
  unfold walk at walked
  simp only [below,hasDown,Bool.false_or,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,
    Bool.or_eq_true,bne_iff_ne,Bool.not_false,Bool.true_and,Bool.and_true] at walked
  obtain ⟨⟨⟨downWidth,downMeasure⟩,downPrefix⟩,branch⟩ := walked
  have least : min cidr (AllowedipsRelation.common bits down.bits key) =
      AllowedipsRelation.common bits down.bits key := by omega
  have differ := branch.resolve_left (by omega)
  exact ⟨downWidth,downMeasure,by omega,by omega,downPrefix,by rw [least]; exact differ.2⟩

#print axioms split_root_facts

/-- The two root slots never name the same node: each root has its slot's
family (`ordered`). T5's `otherRoot`. -/
theorem split_other_root {d : Device} {v4 : Bool} {downId : Nat}
    (ord : ordered d = true)
    (rootHere : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some downId) :
    (if v4 then d.peerAllowedips.root6 else d.peerAllowedips.root4) ≠ some downId := by
  unfold ordered at ord
  simp only [Bool.and_eq_true,List.all_cons,List.all_nil,Bool.and_true] at ord
  obtain ⟨_,four,six⟩ := ord
  intro other
  cases v4
  · simp only [Bool.false_eq_true,↓reduceIte] at rootHere other
    simp only [rootHere,other] at four six
    cases node : d.nodes.get? downId with
    | none => simp only [node] at four; cases four
    | some n =>
      simp only [node,beq_iff_eq] at four six
      omega
  · simp only [↓reduceIte] at rootHere other
    simp only [rootHere,other] at four six
    cases node : d.nodes.get? downId with
    | none => simp only [node] at four; cases four
    | some n =>
      simp only [node,beq_iff_eq] at four six
      omega

#print axioms split_other_root

theorem rootOf_slot (d : Device) (family : Nat) :
    slotOf (bump d) (if family == 4 then Slot.root4 else Slot.root6) = rootOf d family := by
  unfold rootOf
  split <;> rfl

/-- THE SPLIT CASE, PARENT SUB-CASE, SOURCE SIDE. From what `StepFacts`
carries (`model`, `walked`) and two facts of the relation at the cut (the
owner is a peer; identities are below the allocation counter): the node
below, T5's ordering hypotheses, and `step`'s device as T5's installed
device over the device with the sequence incremented. -/
theorem split_step_parent {d : Device} {family key cidr pid p : Nat} {exact : Bool}
    {outcomes : List Bool} {owner : Peer}
    (case : (step d family key cidr pid (some p) exact outcomes).case = .split)
    (walked : walk (bump d) (rootOf d family) key cidr (widthOf family) (some p) exact = true)
    (hasPeer : d.peers.get? pid = some owner)
    (belowNext : ∀ pair ∈ d.nodes.toList, pair.1 < d.nextNode) :
    ∃ downId down pnode rest,
      below (bump d) (rootOf d family) key (some p) = some downId ∧
      (bump d).nodes.get? downId = some down ∧
      SplitParentFacts (bump d) key cidr (widthOf family)
        (min cidr (AllowedipsRelation.common (widthOf family) down.bits key)) p downId down pnode ∧
      (step d family key cidr pid (some p) exact outcomes).device =
        intermediateInstalled (bump d) downId
          (down.bits/2^(widthOf family-1-min cidr (AllowedipsRelation.common (widthOf family) down.bits key))%2)
          (key/2^(widthOf family-1-min cidr (AllowedipsRelation.common (widthOf family) down.bits key))%2)
          p (key/2^(pnode.bitlen-1-pnode.cidr)%2) key cidr
          (min cidr (AllowedipsRelation.common (widthOf family) down.bits key)) (widthOf family) pid
          down pnode owner ∧
      (step d family key cidr pid (some p) exact outcomes).answer = 0 ∧
      (step d family key cidr pid (some p) exact outcomes).consumed = 2 ∧
      exact = false ∧ outcomes = true :: true :: rest ∧ cidr ≤ widthOf family := by
  obtain ⟨rootId,downId,down,rest,short,_,inexact,records,found,hasDown,notCover,device,answer,consumed⟩ :=
    step_split_inv (bits := widthOf family) rfl rfl case
  subst inexact
  obtain ⟨pnode,facts⟩ := split_parent_facts walked (show below (bump d) (rootOf d family) key (some p) = _ from found)
    hasDown notCover
  have downBelow : downId < d.nextNode :=
    belowNext (downId,down) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown)
  have parentBelow : p < d.nextNode :=
    belowNext (p,pnode) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr facts.hasParent)
  refine ⟨downId,down,pnode,rest,found,hasDown,facts,?_,answer,consumed,rfl,records,short⟩
  rw [device]
  exact split_device_parent (bump d) key cidr _ (widthOf family) pid downId p down pnode owner hasPeer
    hasDown facts.hasParent downBelow parentBelow facts.different

#print axioms split_step_parent

/-- THE SPLIT CASE, ROOT SUB-CASE, SOURCE SIDE. `v4` is `family == 4`. -/
theorem split_step_root {d : Device} {family key cidr pid : Nat} {exact : Bool}
    {outcomes : List Bool} {owner : Peer}
    (ord : ordered d = true)
    (case : (step d family key cidr pid none exact outcomes).case = .split)
    (walked : walk (bump d) (rootOf d family) key cidr (widthOf family) none exact = true)
    (hasPeer : d.peers.get? pid = some owner)
    (belowNext : ∀ pair ∈ d.nodes.toList, pair.1 < d.nextNode) :
    ∃ downId down rest,
      (bump d).nodes.get? downId = some down ∧
      (if family == 4 then (bump d).peerAllowedips.root4 else (bump d).peerAllowedips.root6) = some downId ∧
      (if family == 4 then (bump d).peerAllowedips.root6 else (bump d).peerAllowedips.root4) ≠ some downId ∧
      SplitRootFacts key cidr (widthOf family)
        (min cidr (AllowedipsRelation.common (widthOf family) down.bits key)) down ∧
      (step d family key cidr pid none exact outcomes).device =
        intermediateRootInstalled (bump d) (family == 4) downId
          (down.bits/2^(widthOf family-1-min cidr (AllowedipsRelation.common (widthOf family) down.bits key))%2)
          (key/2^(widthOf family-1-min cidr (AllowedipsRelation.common (widthOf family) down.bits key))%2)
          key cidr (min cidr (AllowedipsRelation.common (widthOf family) down.bits key)) (widthOf family) pid
          down owner ∧
      (step d family key cidr pid none exact outcomes).answer = 0 ∧
      (step d family key cidr pid none exact outcomes).consumed = 2 ∧
      exact = false ∧ outcomes = true :: true :: rest ∧ cidr ≤ widthOf family := by
  obtain ⟨rootId,downId,down,rest,short,rootEq,inexact,records,found,hasDown,notCover,device,answer,consumed⟩ :=
    step_split_inv (bits := widthOf family) rfl rfl case
  subst inexact
  have same : rootId = downId := Option.some.inj found
  subst same
  rw [rootOf_slot] at rootEq
  rw [rootEq] at walked
  have facts := split_root_facts walked hasDown notCover
  have rootHere : (if family == 4 then (bump d).peerAllowedips.root4 else (bump d).peerAllowedips.root6) =
      some rootId := by
    rw [←rootEq]
    unfold rootOf
    split <;> rfl
  have downBelow : rootId < d.nextNode :=
    belowNext (rootId,down) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown)
  refine ⟨rootId,down,rest,hasDown,rootHere,?_,facts,?_,answer,consumed,rfl,records,short⟩
  · exact split_other_root (d := bump d) (v4 := family == 4) ord rootHere
  · rw [device]
    exact split_device_root (bump d) (family == 4) key cidr _ (widthOf family) pid rootId down owner hasPeer
      hasDown downBelow

#print axioms split_step_root

end Binary.Statements.C1.Proof
