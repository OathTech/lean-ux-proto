import AllowedipsTableFrame

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

theorem mapM_update {xs : List α} {ys : List β} {f : α → Except ε β} {g : α → Except ε γ}
    (project : β → γ) (run : xs.mapM f=.ok ys)
    (step : ∀ x ∈ xs, ∀ y, f x=.ok y → g x=.ok (project y)) : xs.mapM g=.ok (ys.map project) := by
  induction xs generalizing ys with
  | nil => cases run; rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at run ⊢
    obtain ⟨y,head,run⟩ := bind_ok run
    obtain ⟨tail,rest,run⟩ := bind_ok run
    cases Except.ok.inj run
    rw [step x (by simp) y head,ok_bind,ih rest (fun a member => step a (List.mem_cons_of_mem x member))]
    rfl

/-- Assemble memory-local decoder updates in the original interpretation
order. It is applied to executed write effects, not assumed as a service. -/
theorem reconstruct_update {names o before after s}
    (nodeUpdate : NodeId×AipNode → NodeId×AipNode)
    (peerUpdate : PeerId×Nat×List NodeId → PeerId×Nat×List NodeId)
    (run : reconstruct names o before=.ok s)
    (tableSame : ∀ offset ∈ [AllowedipsMutationLayout.root4,AllowedipsMutationLayout.root6,AllowedipsMutationLayout.seq],
      ∀ path, word after path (names.table+offset) 8=word before path (names.table+offset) 8)
    (nodes : ∀ pair ∈ names.trie.nodes, ∀ entry,
      decodeNode names o before pair.1 pair.2=.ok entry → decodeNode names o after pair.1 pair.2=.ok (nodeUpdate entry))
    (peers : ∀ pair ∈ names.trie.peers, ∀ entry,
      decodePeer names o before pair.1 pair.2=.ok entry → decodePeer names o after pair.1 pair.2=.ok (peerUpdate entry)) :
    reconstruct names o after=.ok {s with nodes := s.nodes.map nodeUpdate,peers := s.peers.map peerUpdate} := by
  unfold reconstruct at run
  obtain ⟨_,valid,run⟩ := bind_ok run
  obtain ⟨r4,root4,run⟩ := bind_ok run
  obtain ⟨root4Value,root4Decoded,run⟩ := bind_ok run
  obtain ⟨r6,root6,run⟩ := bind_ok run
  obtain ⟨root6Value,root6Decoded,run⟩ := bind_ok run
  obtain ⟨seq,seqRead,run⟩ := bind_ok run
  obtain ⟨beforeNodes,nodeReads,run⟩ := bind_ok run
  obtain ⟨beforePeers,peerReads,run⟩ := bind_ok run
  cases Except.ok.inj run
  have ns := mapM_update nodeUpdate nodeReads nodes
  have ps := mapM_update peerUpdate peerReads peers
  simp only [reconstruct,valid,ok_bind,tableSame AllowedipsMutationLayout.root4 (by simp) "table.root4",root4,root4Decoded,
    tableSame AllowedipsMutationLayout.root6 (by simp) "table.root6",root6,root6Decoded,
    tableSame AllowedipsMutationLayout.seq (by simp) "table.seq",seqRead,ns,ps]
  rfl

def reassignNode (id pid : Nat) (entry : NodeId×AipNode) : NodeId×AipNode :=
  (entry.1,if entry.1=id then {entry.2 with peer := some pid} else entry.2)

def reassignPeer (id pid : Nat) (entry : PeerId×Nat×List NodeId) : PeerId×Nat×List NodeId :=
  (entry.1,entry.2.1,if entry.1=pid then entry.2.2.filter (· != id)++[id] else entry.2.2.filter (· != id))

def reassign (id pid : Nat) (s : State) : State :=
  {s with nodes := s.nodes.map (reassignNode id pid),peers := s.peers.map (reassignPeer id pid)}

theorem Exact.effect_reconstructs {names o s memory regs d id base node pid peer owner}
    (related : Corresponds names o s.dmem d) (heap : heap names (target d) s.dmem=.ok ())
    (named : (id,base) ∈ names.trie.nodes) (present : d.nodes.get? id=some node)
    (peerNamed : (pid,peer) ∈ names.trie.peers) (hasPeer : d.peers.get? pid=some owner)
    (nodeAt : s.regs.rbx.toNat=base) (peerAt : s.regs.r14.toNat=peer)
    (checked : Exact.effect s=.ok (memory,regs)) :
    reconstruct names o memory=.ok (reassign id pid (target d)) := by
  have core := Trie.reconstruct_fields related.trie
  have g := geometry related
  have layout : o.nodeSize=72 := core.layout.1
  have frame := Exact.effect_list_frame related heap named present peerNamed hasPeer nodeAt peerAt checked
  have lists := Exact.effect_lists related heap named present peerNamed hasPeer nodeAt peerAt checked
  have full := reconstruct_fields related
  apply reconstruct_update (reassignNode id pid) (reassignPeer id pid) related
  · intro offset member path
    have within : offset+8≤24 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl <;> decide
    rw [←Trie.word_frame frame path (names.table+offset) 8 (table_list_apart related within)]
    exact table_owner_frame related named within path
  · rintro ⟨current,address⟩ currentNamed ⟨nextId,value⟩ read
    have identity : current=nextId := (decodeNode_fields read).1
    subst nextId
    rw [node_record_list_frame_from related currentNamed frame]
    exact owner_update related named currentNamed peerNamed read
  · rintro ⟨current,address⟩ currentNamed ⟨nextId,count,entries⟩ read
    obtain ⟨identity,countRead,_⟩ := decodePeer_fields read
    dsimp only at identity
    subst nextId
    have member : (current,count,entries) ∈ (target d).peers := by
      obtain ⟨value,member,valueRead⟩ := full.peers.left (current,address) currentNamed
      have equal := Except.ok.inj (valueRead.symm.trans read)
      exact equal ▸ member
    have listRead := lists current address count entries currentNamed member
    have countSame : word memory "peer.refcount" (address+o.peerRefcount) 4=.ok count := by
      have countLayout : o.peerRefcount=Layouts.peer_refcount := core.layout.2.2.2.2.2.2.2.2
      rw [←Trie.word_frame frame "peer.refcount" (address+o.peerRefcount) 4 (by
        rw [countLayout]; exact peer_count_list_apart g layout currentNamed)]
      rw [peer_owner_frame related currentNamed named]
      exact countRead
    unfold decodePeer
    rw [countSame]
    obtain ⟨first,headRead,run⟩ := bind_ok listRead
    change word memory "peer.list.head" (address+AllowedipsMutationLayout.allowedips_list) 8=.ok first at headRead
    change peerList names memory (address+AllowedipsMutationLayout.allowedips_list)
      (names.trie.nodes.length+1) first (address+AllowedipsMutationLayout.allowedips_list) []=_ at run
    simp only [ok_bind,headRead,run,reassignPeer]
    rfl

#print axioms Exact.effect_reconstructs
end Binary.Pair.Allowedips
