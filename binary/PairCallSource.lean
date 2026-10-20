import SourceAdapter
import PairCallSearch
import AllowedipsAdequacySource

namespace Binary.Pair.Trie
open Leanux Leanux.WG

/-- Accepted source execution supplies the live-hit bound; it is never an
entry restriction. Histories are used internally to reuse source inversion. -/
theorem lookup_effect {w final : World} {d : Device} {root : Option NodeId} {bits key : Nat}
    {answer : Option PeerId} (device : w.wg.dev = some d)
    (accepted : (Source.lookup root bits key).run w = .ok (answer,final)) :
    ∃ source searched selected,
      source.wg.dev = some d ∧
      (Source.findNode root bits key).run source = .ok (selected,searched) ∧
      AllowedipsSource.select (fun id => d.nodes.get? id) root bits key = some selected ∧
      (match selected with
      | none => answer=none ∧ final.wg.dev=some d
      | some id => ∃ node pid peer,
          d.nodes.get? id=some node ∧ node.peer=some pid ∧ d.peers.get? pid=some peer ∧
          answer=some pid ∧ peer.refcount≠0 ∧ peer.refcount+1<2^31 ∧
          final.wg.dev=some {d with peers := d.peers.insert pid {peer with refcount := peer.refcount+1}}) := by
  obtain ⟨points,logged⟩ := AllowedipsSource.lookup_accepted root bits key [] w final answer accepted
  rw [AllowedipsSource.lookup_split] at logged
  obtain ⟨inner,body,_⟩ := AllowedipsSource.called_accepted logged
  obtain ⟨selected,searchPoints,searchWorld,search,suffix⟩ := AllowedipsSource.accepted_bind _ _ _ _ _ body
  have searchKernel := (AllowedipsSource.frames_searchPrefix (fun k => k) root bits key w.wg
    [⟨.call "lookup",w⟩] w selected searchPoints searchWorld rfl
    (by intro p member; cases List.mem_singleton.mp member; rfl) search).1
  change searchWorld.wg=w.wg at searchKernel
  obtain ⟨ignored,swapped,source,swap,rest⟩ := AllowedipsSource.accepted_bind _ _ _ _ _ search
  rw [AllowedipsSource.swapEndian_run] at swap
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := Prod.mk.inj (Except.ok.inj swap)
  obtain ⟨found,foundPoints,searched,find,done⟩ := AllowedipsSource.accepted_bind _ _ _ _ _ rest
  have same : found=selected := by
    simp only [MirrorHistory.branch_run,StateT.run_bind] at done
    exact congrArg (fun x => x.1.1) (Except.ok.inj done)
  subst found
  have sourceKernel := congrArg World.wg (AllowedipsSource.records_world w (AllowedipsSource.swapChoices bits))
  have sourceDevice : (AllowedipsSource.records w (AllowedipsSource.swapChoices bits)).wg.dev=some d := by
    rw [sourceKernel]; exact device
  have actual := AllowedipsSource.findNode_erases root bits key
    ([⟨.call "lookup",w⟩] ++ AllowedipsSource.choicePoints w (AllowedipsSource.swapChoices bits))
    (AllowedipsSource.records w (AllowedipsSource.swapChoices bits)) d sourceDevice
  simp only [List.nil_append] at find
  rw [find] at actual
  have run : (Source.findNode root bits key).run (AllowedipsSource.records w (AllowedipsSource.swapChoices bits))=
      .ok (selected,searched) := actual.symm
  have select := (AllowedipsSource.findNode_accepted_select root bits key _ searched selected run).1
  have nodeView : AllowedipsSource.nodeView (AllowedipsSource.records w (AllowedipsSource.swapChoices bits))=
      (fun id => d.nodes.get? id) := by funext id; simp [AllowedipsSource.nodeView,sourceDevice]
  rw [nodeView] at select
  refine ⟨_,searched,selected,sourceDevice,run,select,?_⟩
  cases selected with
  | none =>
    change Except.ok ((none,searchPoints),searchWorld)=Except.ok ((answer,inner),final) at suffix
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := Prod.mk.inj (Except.ok.inj suffix)
    exact ⟨rfl,by rw [searchKernel]; exact device⟩
  | some id =>
    obtain ⟨d',node,pid,peer,_,device',nodePresent,word,peerPresent,result,nonzero,bound,_,finalEq,_⟩ :=
      AllowedipsSource.suffix_live id _ _ _ _ _ suffix
    have same : d'=d := Option.some.inj (device'.symm.trans (by rw [searchKernel]; exact device))
    subst d'
    refine ⟨node,pid,peer,nodePresent,word,peerPresent,result,nonzero,bound,?_⟩
    rw [finalEq]
    simp [LookupMirror.record,PeerMirror.peerFinal,PeerMirror.countRecords,PeerMirror.recordCmp,nonzero,device']

#print axioms lookup_effect
end Binary.Pair.Trie
