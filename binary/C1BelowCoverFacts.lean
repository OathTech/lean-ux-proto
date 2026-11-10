import C1BelowStep
import C1BelowCoverSource

/-! Result C1, work package 3, covering path: the step's device of case
`.cover` (`C1BelowStep.coverDevice`) and the walk's facts, in the terms the
data side consumes. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1

/-- Below a parent, the step's device is the data side's endpoint. -/
theorem coverDevice_parent (d : Device) (family key cidr pid p downId : Nat)
    (down parentNode : AipNode) (owner : Peer)
    (hasDown : (bump d).nodes[downId]?=some down) (hasParent : (bump d).nodes[p]?=some parentNode)
    (hasPeer : (bump d).peers[pid]?=some owner)
    (freshDown : (bump d).nextNode≠downId) (freshParent : (bump d).nextNode≠p) (different : downId≠p) :
    coverDevice d family key cidr pid (some p) downId=
      C1Cover.coverInstalled (bump d) downId (down.bits/2^(widthOf family-1-cidr)%2) p
        (key/2^(parentNode.bitlen-1-parentNode.cidr)%2) key cidr (widthOf family) pid down parentNode owner := by
  simp [coverDevice,attached,chooseConnect,connect,setSlot,addTail,alloc,side,
    C1Cover.coverInstalled,newNode,hasDown,hasParent,hasPeer,Std.TreeMap.getElem?_insert,Std.TreeMap.getElem_insert,
    different,freshDown,freshParent,Ne.symm freshDown]
#print axioms coverDevice_parent

/-- What the walk's facts say when the fresh node covers the node below a
placed node: the data side's ordering hypotheses. -/
theorem walk_cover_parent (d : Device) (root : Option NodeId) (key cidr bits p downId : Nat) (down : AipNode)
    (walked : walk d root key cidr bits (some p) false=true)
    (belowEq : below d root key (some p)=some downId) (hasDown : d.nodes.get? downId=some down)
    (covers : cidr=min cidr (AllowedipsRelation.common bits down.bits key)) :
    ∃ parentNode, d.nodes.get? p=some parentNode ∧ parentNode.bitlen=bits ∧ parentNode.cidr<cidr ∧
      key/2^(bits-parentNode.cidr)=parentNode.bits/2^(bits-parentNode.cidr) ∧
      parentNode.bit[key/2^(parentNode.bitlen-1-parentNode.cidr)%2]?=some (some downId) ∧
      down.bitlen=bits ∧ cidr<down.cidr ∧ down.bits/2^(bits-cidr)=key/2^(bits-cidr) := by
  unfold walk at walked
  rw [belowEq] at walked
  simp only [hasDown] at walked
  unfold below at belowEq
  cases hp : d.nodes.get? p with
  | none => simp only [hp] at belowEq; cases belowEq
  | some parentNode =>
    simp only [hp] at belowEq walked
    rw [←covers] at walked
    simp only [Bool.false_or,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at walked
    obtain ⟨⟨⟨⟨width,_⟩,_⟩,prefixEq⟩,⟨⟨⟨⟨downWidth,downMeasure⟩,downPrefix⟩,measure⟩,_⟩⟩ := walked
    exact ⟨parentNode,rfl,width,measure,prefixEq,Option.join_eq_some_iff.mp belowEq,downWidth,downMeasure,downPrefix⟩

#print axioms walk_cover_parent
end Binary.Statements.C1.Proof
