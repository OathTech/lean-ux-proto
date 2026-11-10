import C1BelowCoverFacts
import C1BelowCoverRootSource
import C1BelowSplitOrder

/-! Result C1, work package 3, covering path at the root: the step's device
and the walk's facts in the terms the data side consumes. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1

/-- At the root, the step's device is the data side's endpoint. -/
theorem coverDevice_root (d : Device) (family key cidr pid downId : Nat) (down : AipNode) (owner : Peer)
    (hasDown : (bump d).nodes[downId]?=some down) (hasPeer : (bump d).peers[pid]?=some owner)
    (freshDown : (bump d).nextNode≠downId) :
    coverDevice d family key cidr pid none downId=
      C1Cover.coverRootInstalled (bump d) (family == 4) downId (down.bits/2^(widthOf family-1-cidr)%2)
        key cidr (widthOf family) pid down owner := by
  by_cases four : family=4
  all_goals simp [coverDevice,attached,rootSlot,chooseConnect,connect,setSlot,addTail,alloc,side,
    C1Cover.coverRootInstalled,newNode,hasDown,hasPeer,Std.TreeMap.getElem?_insert,
    Std.TreeMap.getElem_insert,freshDown,Ne.symm freshDown,four]

/-- What the walk's facts say when the fresh node covers the family's root. -/
theorem walk_cover_root (d : Device) (root : Option NodeId) (key cidr bits downId : Nat) (down : AipNode)
    (walked : walk d root key cidr bits none false=true)
    (belowEq : below d root key none=some downId) (hasDown : d.nodes.get? downId=some down)
    (covers : cidr=min cidr (AllowedipsRelation.common bits down.bits key)) :
    root=some downId ∧ down.bitlen=bits ∧ cidr<down.cidr ∧ down.bits/2^(bits-cidr)=key/2^(bits-cidr) := by
  unfold walk at walked
  rw [belowEq] at walked
  simp only [hasDown] at walked
  rw [←covers] at walked
  simp only [Bool.false_or,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,Bool.not_false,Bool.true_and,
    Bool.and_true] at walked
  obtain ⟨⟨⟨downWidth,downMeasure⟩,downPrefix⟩,_⟩ := walked
  exact ⟨belowEq,downWidth,downMeasure,downPrefix⟩

#print axioms coverDevice_root
#print axioms walk_cover_root
end Binary.Statements.C1.Proof
