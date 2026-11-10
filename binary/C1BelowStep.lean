import C1Interfaces

/-! Result C1, work package 3: `C1Step.step` read backwards for the cases
below the placement. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1

/-- The family's root slot. -/
def rootSlot (family : Nat) : Slot := if family == 4 then .root4 else .root6

/-- The device after the first allocation and the attachment to the peer's list. -/
def attached (d : Device) (family key cidr pid : Nat) : Device :=
  addTail (alloc (bump d) (newNode key cidr (widthOf family) (some pid))) pid (bump d).nextNode

/-- `min(cidr, common_bits(down, key))`. -/
def leastOf (family key cidr : Nat) (down : AipNode) : Nat :=
  min cidr (AllowedipsRelation.common (widthOf family) down.bits key)

/-- `step`'s device in case `cover`. -/
def coverDevice (d : Device) (family key cidr pid : Nat) (placed : Option NodeId) (downId : NodeId) : Device :=
  match placed with
  | none => connect (chooseConnect (attached d family key cidr pid) (bump d).nextNode downId)
      (rootSlot family) (bump d).nextNode
  | some p => chooseConnect (chooseConnect (attached d family key cidr pid) (bump d).nextNode downId)
      p (bump d).nextNode

/-- `step`'s device in case `split`, for the intermediate prefix length `least`. -/
def splitDevice (d : Device) (family key cidr pid : Nat) (placed : Option NodeId) (downId : NodeId)
    (least : Nat) : Device :=
  let d1 := attached d family key cidr pid
  let middle := d1.nextNode
  let d2 := chooseConnect (chooseConnect
    (alloc d1 (newNode key least (widthOf family) none)) middle downId) middle (bump d).nextNode
  match placed with
  | none => connect d2 (rootSlot family) middle
  | some p => chooseConnect d2 p middle

/-- `step`'s device in case `splitNoMem`. -/
def rollbackDevice (d : Device) (family key cidr pid : Nat) : Device :=
  {delete (attached d family key cidr pid) (bump d).nextNode with
    nodes := (delete (attached d family key cidr pid) (bump d).nextNode).nodes.erase (bump d).nextNode}

/-- `step` in a case below the placement: the prefix fits, the root is
occupied, the walk was not exact, the first allocation succeeded, a node
lies below the placement, and per case the comparison, the second outcome,
the answer and the device. -/
structure Below (d : Device) (family key cidr pid : Nat) (placed : Option NodeId) (exact : Bool)
    (outcomes : List Bool) (st : Step) (rootId downId : NodeId) (down : AipNode) (rest : List Bool) : Prop where
  fits : cidr ≤ widthOf family
  inexact : exact = false
  root : slotOf (bump d) (rootSlot family) = some rootId
  first : outcomes = true :: rest
  hasBelow : below (bump d) (some rootId) key placed = some downId
  hasDown : (bump d).nodes.get? downId = some down
  cover : st.case = .cover → cidr = leastOf family key cidr down ∧ st.answer = 0 ∧
    st.device = coverDevice d family key cidr pid placed downId
  split : st.case = .split → cidr ≠ leastOf family key cidr down ∧ (∃ tail, rest = true :: tail) ∧
    st.answer = 0 ∧ st.device = splitDevice d family key cidr pid placed downId (leastOf family key cidr down)
  rollback : st.case = .splitNoMem → cidr ≠ leastOf family key cidr down ∧ rest.head? ≠ some true ∧
    st.answer = -ENOMEM ∧ st.device = rollbackDevice d family key cidr pid

theorem step_below {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool} {st : Step}
    (model : st = step d family key cidr pid placed exact outcomes)
    (case : st.case = .cover ∨ st.case = .split ∨ st.case = .splitNoMem) :
    ∃ rootId downId down rest, Below d family key cidr pid placed exact outcomes st rootId downId down rest := by
  unfold step at model
  simp only [show (if (family == 4) = true then 32 else 128) = widthOf family from rfl,
    show (if (family == 4) = true then Slot.root4 else Slot.root6) = rootSlot family from rfl] at model
  split at model
  · subst model; simp at case
  rename_i fits
  split at model
  · split at model <;> subst model <;> simp at case
  rename_i rootId root
  split at model
  · split at model <;> subst model <;> simp at case
  rename_i inexact
  split at model
  · rename_i rest
    split at model
    · split at model <;> subst model <;> simp at case
    · rename_i downId down found
      have located : below (bump d) (some rootId) key placed = some downId ∧
          (bump d).nodes.get? downId = some down := by
        cases h : below (bump d) (some rootId) key placed with
        | none => simp [h] at found
        | some id =>
          simp only [h,Option.bind_some,Option.map_eq_some_iff,Prod.mk.injEq] at found
          obtain ⟨n,read,same,node⟩ := found
          subst same; subst node
          exact ⟨rfl,read⟩
      refine ⟨rootId,downId,down,rest,Nat.le_of_not_lt fits,by simpa using inexact,root,rfl,
        located.1,located.2,?_,?_,?_⟩
      · split at model
        · rename_i equal
          subst model
          exact fun _ => ⟨eq_of_beq equal,rfl,by cases placed <;> rfl⟩
        · split at model <;> subst model <;> intro h <;> cases h
      · split at model
        · subst model; intro h; cases h
        · rename_i differ
          split at model
          · subst model
            exact fun _ => ⟨fun same => differ (by rw [beq_iff_eq]; exact same),⟨_,rfl⟩,rfl,by cases placed <;> rfl⟩
          · subst model; intro h; cases h
      · split at model
        · subst model; intro h; cases h
        · rename_i differ
          split at model
          · subst model; intro h; cases h
          · rename_i refused
            subst model
            refine fun _ => ⟨fun same => differ (by rw [beq_iff_eq]; exact same),?_,rfl,rfl⟩
            intro head
            match rest, head, refused with
            | true :: tail, _, refused => exact refused tail rfl
  · subst model; simp at case

#print axioms step_below
end Binary.Statements.C1.Proof
