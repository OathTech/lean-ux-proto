import AllowedipsSourceBody
import AllowedipsLoopSetup

namespace Binary.AllowedipsSource
open Leanux Leanux.WG MirrorHistory

/-- Source event projection retains the actual recorded decision operand,
including its NET_RX section. Calls and returns have no decision operand. -/
def eventView (p : Point) : CommonBits.EventView :=
  (p.tag,match p.tag with | .decision _ => p.world.steps.back? | _ => none)

def bodyChoices (bits key : Nat) (node : AipNode) : Choices :=
  if node.cidr ≤ commonValue node key bits then
    [(.findNodePrefixMatches,true),(.findNodeHasPeer,node.peer.isSome),(.findNodeFullLength,node.cidr==bits)]
  else [(.findNodePrefixMatches,false)]

def bodyPoints (bits key : Nat) (node : AipNode) (w : World) : List Point :=
  [⟨.call "common_bits",w⟩] ++ choicePoints w (commonChoices node key bits) ++
    [⟨.returned "common_bits",records w (commonChoices node key bits)⟩] ++
    choicePoints (records w (commonChoices node key bits)) (bodyChoices bits key node)

def bodyWorld (bits key : Nat) (node : AipNode) (w : World) : World :=
  records (records w (commonChoices node key bits)) (bodyChoices bits key node)

private theorem except_ok_bind (value : α) (f : α → Except Stop β) :
    (Except.ok value >>= f) = f value := rfl
private theorem except_pure (value : α) : (pure value : Except Stop α) = .ok value := rfl
private theorem except_map (f : α → β) (value : α) :
    f <$> (Except.ok value : Except Stop α) = .ok (f value) := rfl
private theorem throw_run (e : Stop) (w : World) : (throw e : M α).run w = .error e := rfl
private theorem except_error_bind (e : Stop) (f : α → Except Stop β) :
    (Except.error e >>= f) = .error e := rfl

/-- Every accepted nonempty source body has exactly these source worlds.
The selector premise identifies the result, not the history or execution. -/
theorem nodeBody_run (bits key id : Nat) (previous : Option NodeId) (node : AipNode)
    (w : World) (history : List Point) (step : ForInStep Acc)
    (present : nodeView w id = some node)
    (selected : selectStep (nodeView w) bits key (none,some id,previous) = some step) :
    ((nodeBody bits key id previous).run history).run w =
      .ok ((step,history ++ bodyPoints bits key node w),bodyWorld bits key node w) := by
  cases device : w.k.wg with
  | none => simp [nodeView,device] at present
  | some dev =>
    have nodeGet : dev.nodes.get? id = some node := by simpa only [nodeView,device,Option.bind_some] using present
    have nodeAt : dev.nodes[id]? = some node := nodeGet
    by_cases mismatch : commonValue node key bits < node.cidr <;>
      cases hasPeer : node.peer.isSome <;>
      by_cases full : node.cidr = bits <;>
      by_cases invalid : node.cidr ≥ node.bitlen <;>
      cases child : node.bit[key/2^(node.bitlen-1-node.cidr)%2]?
    all_goals try simp only [full] at mismatch
    all_goals
      simp [selectStep,nodeView,device,nodeAt,mismatch,hasPeer,full,invalid,child] at selected
    all_goals try omega
    all_goals try cases selected
    all_goals
      simp [nodeBody,StateT.run_lift,StateT.run_bind,StateT.run_pure,getNode,getDev,getK,
        device,nodeAt,prefixMatches_run,branchLogged,mark,branch,choose,AipNode.bitAt,invariant,
        bodyPoints,bodyWorld,bodyChoices,records,choicePoints,LookupMirror.record,
        records_steps,except_ok_bind,except_pure,except_map,throw_run,except_error_bind,
        mismatch,hasPeer,full,invalid,child,List.append_assoc,←Nat.not_lt]
    all_goals
      have short : node.cidr < node.bitlen := by omega
      simp [short,StateT.run_pure,except_pure,except_ok_bind,except_map,
        AipNode.bitAt,child,full]
    all_goals rfl

theorem records_rx (w : World) (choices : Choices) : (records w choices).netRxSection = w.netRxSection := by
  induction choices generalizing w with
  | nil => rfl
  | cons choice rest ih => exact ih (LookupMirror.record w choice.1 choice.2)

theorem choicePoints_events (w : World) (choices : Choices) :
    (choicePoints w choices).map eventView =
      choices.map (fun (d,b) => CommonBits.decisionView w.netRxSection d b) := by
  induction choices generalizing w with
  | nil => rfl
  | cons choice rest ih =>
    rcases choice with ⟨d,b⟩
    simp [choicePoints,eventView,LookupMirror.record,ih,CommonBits.decisionView]

theorem bodyPoints_events (bits key : Nat) (node : AipNode) (w : World) :
    (bodyPoints bits key node w).map eventView =
      AllowedipsLoop.commonSignature w.netRxSection bits key node ++
        (bodyChoices bits key node).map (fun (d,b) => CommonBits.decisionView w.netRxSection d b) := by
  simp only [bodyPoints,List.map_append,List.map_cons,List.map_nil,choicePoints_events,records_rx]
  rfl

theorem bodyPoints_done (bits key : Nat) (node : AipNode) (w : World) (acc : Acc) :
    (bodyPoints bits key node w).map eventView =
      AllowedipsLoop.stepSignature w.netRxSection bits key node (.done acc) := by
  rw [bodyPoints_events]
  simp only [bodyChoices,AllowedipsLoop.common_value,AllowedipsLoop.stepSignature]
  by_cases matching : node.cidr ≤ AllowedipsRelation.common bits node.bits key
  all_goals simp [matching,List.append_assoc]

theorem bodyPoints_yield (bits key : Nat) (node : AipNode) (w : World) (acc : Acc)
    (matching : node.cidr ≤ AllowedipsRelation.common bits node.bits key) :
    (bodyPoints bits key node w).map eventView ++
        [CommonBits.decisionView w.netRxSection .findNodeNode acc.2.1.isSome] =
      AllowedipsLoop.stepSignature w.netRxSection bits key node (.yield acc) := by
  rw [bodyPoints_events]
  simp [bodyChoices,AllowedipsLoop.common_value,AllowedipsLoop.stepSignature,matching,List.append_assoc]

theorem bodyWorld_kernel (bits key : Nat) (node : AipNode) (w : World) :
    (bodyWorld bits key node w).k = w.k := by
  simp only [bodyWorld,records_kernel]

theorem bodyWorld_rx (bits key : Nat) (node : AipNode) (w : World) :
    (bodyWorld bits key node w).netRxSection = w.netRxSection := by
  simp only [bodyWorld,records_rx]

#print axioms nodeBody_run
#print axioms bodyPoints_done
#print axioms bodyPoints_yield
end Binary.AllowedipsSource
