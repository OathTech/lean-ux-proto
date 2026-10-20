import AllowedipsLoopSetup

namespace Binary.AllowedipsLoop
open TrustBase AllowedipsRelation LookupObservation
local instance : Labels := Image.linkedLabels

/-- Execute one actual nonempty trie body. The chosen source step is proved
from the represented node; neither its execution nor its result is assumed. -/
theorem node_body (fetch : Int64 → Option Decoded) (base s : MachineData)
    (coverage : CommonBitsCoverage.Context) (c : Config) (view : AllowedipsSource.NodeView)
    (setup : Setup fetch base coverage c view) (id : Nat) (previous : Option Nat)
    (reached : Reached view c.root c.bits c.key id)
    (atNode : s.regs.rbx.toBitVec = c.nodes id)
    (atPrevious : s.regs.rbp.toBitVec = pointer c.nodes previous)
    (frame : Frame base coverage s)
    (history : List MachineState) (events : List Point)
    (observed : observeHistory (AllowedipsObservation.edge c.rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s,AllowedipsImage.Lookup.entry+0xd5⟩) :
    Eventually (historyStep fetch) (fun t => ∃ node step delta,
      view id = some node ∧
      AllowedipsSource.selectStep view c.bits c.key (none,some id,previous) = some step ∧
      StepPost c.nodes step t.machine ∧
      delta.map CommonBits.pointView = stepSignature c.rxSection c.bits c.key node step ∧
      Trace base coverage c.rxSection history (events++delta) t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0xd5⟩,history⟩ := by
  obtain ⟨node,present,fields⟩ := setup.heap.2.2 id reached
  have apart : ∀ a, NodeReads c.nodes c.bits c.key id node a → ¬writes base.regs.rsp coverage a :=
    fun a read => setup.apart a ⟨id,node,reached,present,read⟩
  have first := node_prefix fetch setup.decoder setup.callbacks setup.cmp1 base s coverage
    c.nodes c.peers c.bits c.key id node setup.heap.1 setup.familyByte atNode fields apart setup.words setup.queryApart
    frame c.rxSection history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro t1 ⟨pc1,bx1,bp1,cidr1,commonDelta,commonSig,trace1⟩
  by_cases matching : node.cidr ≤ common c.bits node.bits c.key
  · have sourceMatch : ¬AllowedipsSource.commonValue node c.key c.bits < node.cidr := by
      rw [common_value]; omega
    simp only [matching,decide_true,ite_true] at pc1 trace1
    have atNode1 : t1.machine.data.regs.rbx.toBitVec = c.nodes id := by rw [bx1]; exact atNode
    have chosen : (if node.peer.isSome then t1.machine.data.regs.rbx else t1.machine.data.regs.rbp).toBitVec =
        pointer c.nodes (selectedNode id node previous) :=
      selected_pointer c.nodes id node previous t1.machine.data atNode1 (by rw [bp1]; exact atPrevious)
    by_cases full : node.cidr = c.bits
    · have sourceMatchFull : ¬AllowedipsSource.commonValue node c.key c.bits < c.bits := by simpa only [full] using sourceMatch
      have matchedFull : c.bits ≤ common c.bits node.bits c.key := by simpa only [full] using matching
      have second := matched_guard fetch setup.decoder setup.callbacks.pc setup.cmp1 base t1.machine.data coverage
        c.nodes c.peers c.bits c.key id node atNode1 setup.width cidr1 fields matching apart trace1.frame
        c.rxSection t1.history _ trace1.observed (by rw [←pc1]; exact trace1.last)
      rw [cursor_eq t1 _ pc1] at second
      apply eventually_weaken (historyStep fetch) _ _ _ _ second
      rintro t2 ⟨pc2,bx2,bp2,peerPoint,peerPC,trace2⟩
      simp only [full,beq_self_eq_true,ite_true] at pc2 trace2
      let step : ForInStep AllowedipsSource.Acc := .done (some (selectedNode id node previous),some id,selectedNode id node previous)
      refine ⟨node,step,commonDelta ++
        [decision c.rxSection .findNodePrefixMatches true t1.machine,
         decision c.rxSection .findNodeHasPeer node.peer.isSome peerPoint,
         decision c.rxSection .findNodeFullLength true t2.machine],present,?_,?_,?_,?_⟩
      · simp [AllowedipsSource.selectStep,present,sourceMatchFull,full,selectedNode,step]
      · exact ⟨pc2,by rw [bp2]; exact chosen⟩
      · simp [List.map_append,commonSig,stepSignature,matchedFull,step,full,
          CommonBits.pointView,CommonBits.decisionView,decision,List.append_assoc]
      · simpa only [List.append_assoc,List.cons_append,List.nil_append] using trace1.trans trace2
    · have short : node.cidr < c.bits := by
        have bounded := common_bound c.bits node.bits c.key setup.heap.1
        omega
      obtain ⟨next,atChild⟩ := node_child fields matching short
      have second := matched_continue fetch setup.decoder setup.callbacks.pc setup.cmp1 base t1.machine.data coverage
        c.nodes c.peers c.bits c.key id node next setup.heap.1 atNode1 setup.width cidr1 fields matching short atChild
        apart setup.words setup.queryApart trace1.frame c.rxSection t1.history _ trace1.observed
        (by rw [←pc1]; exact trace1.last)
      rw [cursor_eq t1 _ pc1] at second
      apply eventually_weaken (historyStep fetch) _ _ _ _ second
      rintro t2 ⟨pc2,bx2,bp2,peerPoint,fullPoint,peerPC,fullPC,trace2⟩
      let step : ForInStep AllowedipsSource.Acc := .yield (none,next,selectedNode id node previous)
      refine ⟨node,step,commonDelta ++
        [decision c.rxSection .findNodePrefixMatches true t1.machine,
         decision c.rxSection .findNodeHasPeer node.peer.isSome peerPoint,
         decision c.rxSection .findNodeFullLength false fullPoint,
         decision c.rxSection .findNodeNode next.isSome t2.machine],present,?_,?_,?_,?_⟩
      · have width := ((fields.2.2.2.2 matching).2.2 short).1
        have valid : ¬node.cidr ≥ node.bitlen := by omega
        have child := atChild
        change node.bit[c.key / 2^(node.bitlen-1-node.cidr) % 2]? = some next at child
        simp [AllowedipsSource.selectStep,present,sourceMatch,full,valid,child,selectedNode,step]
      · exact ⟨pc2,bx2,by rw [bp2]; exact chosen⟩
      · simp [List.map_append,commonSig,stepSignature,matching,step,full,
          CommonBits.pointView,CommonBits.decisionView,decision,List.append_assoc]
      · simpa only [List.append_assoc,List.cons_append,List.nil_append] using trace1.trans trace2
  · have sourceMismatch : AllowedipsSource.commonValue node c.key c.bits < node.cidr := by
      rw [common_value]; omega
    simp only [matching,decide_false] at pc1 trace1
    let step : ForInStep AllowedipsSource.Acc := .done (some previous,some id,previous)
    apply Eventually.done
    refine ⟨node,step,commonDelta ++ [decision c.rxSection .findNodePrefixMatches false t1.machine],present,?_,?_,?_,?_⟩
    · simp [AllowedipsSource.selectStep,present,sourceMismatch,step]
    · exact ⟨pc1,by rw [bp1]; exact atPrevious⟩
    · simp [List.map_append,commonSig,stepSignature,matching,
        CommonBits.pointView,CommonBits.decisionView,decision]
    · simpa only [List.append_assoc] using trace1

#print axioms node_body
end Binary.AllowedipsLoop
