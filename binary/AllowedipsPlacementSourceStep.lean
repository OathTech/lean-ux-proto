import PairAllowedipsPlacementSource
import Leanux.Proofs.WG.AllowedIps.ArithmeticMirror

namespace Binary.Pair.Allowedips.Placement
open Leanux Leanux.WG

def recordCmp (a : Ambient) (d : Decision) (outcome : Bool) (x y : Int) : Ambient :=
  {a with steps := a.steps.push {decision := d,outcome,operands := some (x,y),netRx := a.netRxSection}}

theorem branch_run (d : Decision) (b : Bool) (store : AipStore) (a : Ambient) :
    ((branch d b : AipM Bool).run store).run a=
      .ok ((b,store),Leanux.Proofs.WG.AllowedIps.record a d b) := rfl

theorem branchCmp_run (d : Decision) (b : Bool) (x y : Int) (store : AipStore) (a : Ambient) :
    ((branchCmp d b x y : AipM Bool).run store).run a=.ok ((b,store),recordCmp a d b x y) := rfl

theorem common_run (node : AipNode) (key bits : Nat) (store : AipStore) (a : Ambient) :
    ((WG.commonBits node key bits : AipM Nat).run store).run a=
      .ok ((AllowedipsRelation.common bits node.bits key,store),
        Leanux.Proofs.WG.AllowedIps.commonRecords a bits (node.bits ^^^ key)) := by
  by_cases h32 : bits=32
  · subst bits; rfl
  · by_cases h128 : bits=128
    · subst bits
      by_cases high : (node.bits ^^^ key)/2^64=0
      all_goals simp [WG.commonBits,StateT.run_bind,StateT.run_pure,branch_run,
        Source.except_ok_bind,Source.except_pure,AllowedipsRelation.common,
        Leanux.Proofs.WG.AllowedIps.commonRecords,high] <;> rfl
    · simp [WG.commonBits,StateT.run_bind,StateT.run_pure,branch_run,
        Source.except_ok_bind,Source.except_pure,AllowedipsRelation.common,
        Leanux.Proofs.WG.AllowedIps.commonRecords,h32,h128] <;> rfl

theorem prefix_run (node : AipNode) (key bits : Nat) (store : AipStore) (a : Ambient) :
    ((WG.prefixMatches node key bits : AipM Bool).run store).run a=
      .ok ((decide (node.cidr≤AllowedipsRelation.common bits node.bits key),store),
        Leanux.Proofs.WG.AllowedIps.commonRecords a bits (node.bits ^^^ key)) := by
  unfold WG.prefixMatches
  simp only [StateT.run_bind,common_run,Source.except_ok_bind]
  rfl

/-- A proof projection of the actual iteration: only its accumulator and
component store are observed; source decision records remain in Ambient. -/
def selectStep (store : AipStore) (key cidr bits : Nat) (acc : Acc) : Option (ForInStep Acc) := do
  match acc.2.1 with
  | none => return .done (some (acc.2.2,false),none,acc.2.2)
  | some id =>
    let n ← store.nodes.get? id
    if cidr<n.cidr then return .done (some (acc.2.2,false),some id,acc.2.2)
    if AllowedipsRelation.common bits n.bits key<n.cidr then
      return .done (some (acc.2.2,false),some id,acc.2.2)
    if n.cidr=cidr then return .done (some (some id,true),some id,some id)
    if n.cidr≥n.bitlen then none else do
      let next ← n.bit[key/2^(n.bitlen-1-n.cidr)%2]?
      return .yield (none,next,some id)

theorem iteration_projection (key cidr bits : Nat) (acc : Acc) (store : AipStore) (a : Ambient) :
    (((iteration key cidr bits acc).run store).run a).toOption.map (fun ((step,entries),_) => (step,entries))=
      (selectStep store key cidr bits acc).map (fun step => (step,store)) := by
  rcases acc with ⟨answer,current,parent⟩
  cases current with
  | none => rfl
  | some id =>
    cases present : store.nodes[id]? with
    | none =>
      simp [iteration,selectStep,getNode,StateT.run_bind,branch_run,
        Source.except_ok_bind,present,invariant,Except.toOption]
      rfl
    | some node =>
      by_cases long : cidr<node.cidr <;>
        by_cases matching : AllowedipsRelation.common bits node.bits key<node.cidr <;>
        by_cases exactLength : node.cidr=cidr <;>
        by_cases invalid : node.cidr≥node.bitlen <;>
        cases child : node.bit[key/2^(node.bitlen-1-node.cidr)%2]?
      all_goals try simp only [exactLength] at long matching invalid child
      all_goals simp [iteration,selectStep,getNode,StateT.run_bind,StateT.run_pure,branch_run,branchCmp_run,
        Source.except_ok_bind,Source.except_pure,prefix_run,present,choose,AipNode.bitAt,
        invariant,Except.toOption,long,matching,exactLength,invalid,child]
      all_goals rfl

theorem iteration_accepted {key cidr bits acc store a step entries final}
    (accepted : ((iteration key cidr bits acc).run store).run a=.ok ((step,entries),final)) :
    selectStep store key cidr bits acc=some step ∧ entries=store := by
  have projected := iteration_projection key cidr bits acc store a
  rw [accepted] at projected
  change some (step,entries)=(selectStep store key cidr bits acc).map (fun step => (step,store)) at projected
  cases selected : selectStep store key cidr bits acc with
  | none => rw [selected] at projected; cases projected
  | some value =>
    rw [selected] at projected
    have eq : (step,entries)=(value,store) := Option.some.inj projected
    exact ⟨by rw [(Prod.mk.inj eq).1],(Prod.mk.inj eq).2⟩

theorem yield_open {store key cidr bits acc next}
    (selected : selectStep store key cidr bits acc=some (.yield next)) : next.1=none := by
  rcases acc with ⟨answer,current,parent⟩
  cases current with
  | none => cases selected
  | some id =>
    cases present : store.nodes[id]? with
    | none => simp [selectStep,present] at selected
    | some node =>
      by_cases long : cidr<node.cidr <;>
        by_cases matching : AllowedipsRelation.common bits node.bits key<node.cidr <;>
        by_cases exactLength : node.cidr=cidr <;>
        by_cases invalid : node.cidr≥node.bitlen <;>
        cases child : node.bit[key/2^(node.bitlen-1-node.cidr)%2]?
      all_goals try simp only [exactLength] at long matching invalid child
      all_goals simp [selectStep,present,long,matching,exactLength,invalid,child] at selected
      all_goals cases selected; rfl

#print axioms iteration_accepted

#print axioms common_run
#print axioms prefix_run
end Binary.Pair.Allowedips.Placement
