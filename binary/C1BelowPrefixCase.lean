import C1Interfaces

/-! Result C1, work package 3, prefix: what the three cases below the
placement say about the mirror's device, read off `C1Step.step` and
`C1Invariant.walk`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1

theorem slotOf_root (d : Device) (family : Nat) :
    slotOf (bump d) (if family = 4 then Slot.root4 else Slot.root6)=rootOf d family := by
  unfold rootOf
  by_cases four : family = 4 <;> simp [four,slotOf,bump]

/-- In the three cases below the placement the prefix is within the width,
the trie's root is present, the walk was not exact, and a node lies below
the placement. -/
theorem case_below {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool} {st : Step}
    (model : st=step d family key cidr pid placed exact outcomes)
    (case : st.case = .cover ∨ st.case = .split ∨ st.case = .splitNoMem) :
    cidr≤widthOf family ∧ exact=false ∧ ∃ rootId downId down,
      rootOf d family=some rootId ∧ below (bump d) (some rootId) key placed=some downId ∧
      (bump d).nodes.get? downId=some down := by
  subst model
  by_cases long : (if family = 4 then 32 else 128)<cidr
  · simp [step,long] at case
  cases rooted : rootOf d family with
  | none =>
    rcases outcomes with _|⟨_|_,_⟩ <;> simp [step,long,slotOf_root,rooted] at case
  | some rootId =>
    cases exact with
    | true =>
      simp [step,long,slotOf_root,rooted] at case
      split at case <;> simp at case
    | false =>
      rcases outcomes with _|⟨_|_,rest⟩
      · simp [step,long,slotOf_root,rooted] at case
      · simp [step,long,slotOf_root,rooted] at case
      · cases found : (below (bump d) (some rootId) key placed).bind fun id =>
            (bump d).nodes[id]?.map fun n => (id,n) with
        | none => cases placed <;> simp [step,long,slotOf_root,rooted,found] at case
        | some pair =>
          obtain ⟨downId,down⟩ := pair
          refine ⟨by unfold widthOf; by_cases four : family = 4 <;> simp [four] at long ⊢ <;> omega,rfl,rootId,downId,down,rfl,?_⟩
          cases hbelow : below (bump d) (some rootId) key placed with
          | none => rw [hbelow] at found; simp at found
          | some id =>
            rw [hbelow] at found
            simp only [Option.bind_some,Option.map_eq_some_iff,Prod.mk.injEq] at found
            obtain ⟨node,present,same,rfl⟩ := found
            subst same
            exact ⟨rfl,by rw [Std.TreeMap.get?_eq_getElem?]; exact present⟩

#print axioms case_below
/-- The walk's facts about a placed node, when the walk was not exact and a
node lies below: same width, strictly shorter prefix, the slot on the key's
side occupied by the node below. -/
theorem walk_parent {dd : Device} {root : Option NodeId} {key cidr bits p downId : Nat}
    (walked : walk dd root key cidr bits (some p) false=true)
    (lower : below dd root key (some p)=some downId) :
    ∃ pn, dd.nodes.get? p=some pn ∧ pn.bitlen=bits ∧ pn.cidr<cidr ∧
      pn.bit[key/2^(pn.bitlen-1-pn.cidr)%2]?=some (some downId) := by
  unfold below at lower
  simp only [Std.TreeMap.get?_eq_getElem?] at lower ⊢
  cases present : dd.nodes[p]? with
  | none => simp [present] at lower
  | some pn =>
    simp only [present] at lower
    refine ⟨pn,rfl,?_⟩
    simp only [walk,Std.TreeMap.get?_eq_getElem?,present,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,Bool.false_eq,
      beq_eq_false_iff_ne,ne_eq] at walked
    obtain ⟨⟨⟨⟨width,short⟩,inexact⟩,_⟩,_⟩ := walked
    refine ⟨width,by omega,?_⟩
    cases slot : pn.bit[key/2^(pn.bitlen-1-pn.cidr)%2]? with
    | none => simp [slot] at lower
    | some inner => simpa [slot] using lower

/-- The node below the placement has the family's width. -/
theorem walk_down {dd : Device} {root : Option NodeId} {key cidr bits downId : Nat}
    {placed : Option NodeId} {down : AipNode}
    (walked : walk dd root key cidr bits placed false=true)
    (lower : below dd root key placed=some downId) (present : dd.nodes.get? downId=some down) :
    down.bitlen=bits := by
  simp only [walk,lower,present,Bool.and_eq_true,Bool.false_or,beq_iff_eq] at walked
  exact walked.2.1.1.1.1

#print axioms walk_parent
#print axioms walk_down
end Binary.Statements.C1.Proof
