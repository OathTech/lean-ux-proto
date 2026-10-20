import AllowedipsExactList

namespace Binary.Pair.Allowedips
open Leanux Leanux.WG

/-- Facts extracted from the existing executable reconstruction, including
the full node records and ordered ownership lists needed by mutations. -/
structure Reconstructed (names : Names) (o : AllowedipsProbe.Offsets) (m : DataMem) (s : State) : Prop where
  valid : validate names o=.ok ()
  root4 : ∃ raw, word m "table.root4" (names.table+AllowedipsMutationLayout.root4) 8=.ok raw ∧
    Trie.pointer names.trie.nodes "table.root4" raw=.ok s.table.root4
  root6 : ∃ raw, word m "table.root6" (names.table+AllowedipsMutationLayout.root6) 8=.ok raw ∧
    Trie.pointer names.trie.nodes "table.root6" raw=.ok s.table.root6
  seq : word m "table.seq" (names.table+AllowedipsMutationLayout.seq) 8=.ok s.table.seq
  nodes : Mapped (fun pair entry => decodeNode names o m pair.1 pair.2=.ok entry) names.trie.nodes s.nodes
  peers : Mapped (fun pair entry => decodePeer names o m pair.1 pair.2=.ok entry) names.trie.peers s.peers
  nextNode : s.nextNode=names.nextNode

theorem reconstruct_fields {names o m s} (run : reconstruct names o m=.ok s) : Reconstructed names o m s := by
  unfold reconstruct at run
  obtain ⟨_,valid,run⟩ := bind_ok run
  obtain ⟨r4,root4,run⟩ := bind_ok run
  obtain ⟨root4Value,root4Decoded,run⟩ := bind_ok run
  obtain ⟨r6,root6,run⟩ := bind_ok run
  obtain ⟨root6Value,root6Decoded,run⟩ := bind_ok run
  obtain ⟨seq,seqRead,run⟩ := bind_ok run
  obtain ⟨nodes,nodeReads,run⟩ := bind_ok run
  obtain ⟨peers,peerReads,run⟩ := bind_ok run
  cases Except.ok.inj run
  exact ⟨valid,⟨r4,root4,root4Decoded⟩,⟨r6,root6,root6Decoded⟩,seqRead,mapM_ok nodeReads,mapM_ok peerReads,rfl⟩

theorem decodePeer_fields {names o m id base current count entries}
    (run : decodePeer names o m id base=.ok (current,count,entries)) :
    id=current ∧ word m "peer.refcount" (base+o.peerRefcount) 4=.ok count ∧
    (do
      let first ← word m "peer.list.head" (base+1096) 8
      peerList names m (base+1096) (names.trie.nodes.length+1) first (base+1096) [])=.ok entries := by
  unfold decodePeer at run
  obtain ⟨c,countRead,run⟩ := bind_ok run
  obtain ⟨first,firstRead,run⟩ := bind_ok run
  obtain ⟨entries',entriesRead,run⟩ := bind_ok run
  cases Except.ok.inj run
  refine ⟨rfl,countRead,?_⟩
  change (do
    let first ← word m "peer.list.head" (base+AllowedipsMutationLayout.allowedips_list) 8
    peerList names m (base+AllowedipsMutationLayout.allowedips_list)
      (names.trie.nodes.length+1) first (base+AllowedipsMutationLayout.allowedips_list) [])=_
  rw [firstRead]
  exact entriesRead

theorem Reconstructed.peer {names o m s id count entries}
    (fields : Reconstructed names o m s) (member : (id,count,entries) ∈ s.peers) :
    ∃ base, (id,base) ∈ names.trie.peers ∧
      word m "peer.refcount" (base+o.peerRefcount) 4=.ok count ∧
      (do
        let first ← word m "peer.list.head" (base+1096) 8
        peerList names m (base+1096) (names.trie.nodes.length+1) first (base+1096) [])=.ok entries := by
  obtain ⟨⟨current,base⟩,named,run⟩ := fields.peers.right _ member
  obtain ⟨equal,countRead,listRead⟩ := decodePeer_fields run
  exact ⟨base,equal ▸ named,countRead,listRead⟩

theorem decodeNode_fields {names o m id base current node}
    (run : decodeNode names o m id base=.ok (current,node)) :
    id=current ∧ Trie.decodeNode names.trie o m base=.ok (Trie.targetNode node) := by
  unfold decodeNode at run
  obtain ⟨core,coreRead,run⟩ := bind_ok run
  obtain ⟨raw,rawRead,run⟩ := bind_ok run
  obtain ⟨slot,slotRead,run⟩ := bind_ok run
  cases Except.ok.inj run
  exact ⟨rfl,coreRead⟩

theorem Reconstructed.node {names o m s id node}
    (fields : Reconstructed names o m s) (member : (id,node) ∈ s.nodes) :
    ∃ base, (id,base) ∈ names.trie.nodes ∧ decodeNode names o m id base=.ok (id,node) := by
  obtain ⟨⟨current,base⟩,named,run⟩ := fields.nodes.right _ member
  have equal := (decodeNode_fields run).1
  dsimp only at equal
  subst current
  exact ⟨base,named,run⟩

#print axioms reconstruct_fields
#print axioms Reconstructed.peer
end Binary.Pair.Allowedips
