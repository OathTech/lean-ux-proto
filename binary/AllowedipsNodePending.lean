import AllowedipsNodeCore
import AllowedipsNodeResourceFrame
import AllowedipsNodeLists

namespace Binary.Pair.Allowedips.NodeInit
open Leanux Leanux.WG Root

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- Derived resources while a fresh node is initialized but not yet published.
This is an intermediate proof postcondition, not a new environmental premise
or an alternative relation. Each publication path consumes these decoder facts. -/
structure Pending (names : Names) (before : MachineData) (d : Device)
    (key cidr pid base : Nat) (memory : DataMem) : Prop where
  core : Trie.decodeNode (names.allocated base).trie nodeOffsets memory base=
    .ok (Trie.targetNode (newNode key cidr before.regs.rbp.toNat (some pid)))
  nodes : ∀ pair ∈ names.trie.nodes, ∀ value,
    decodeNode names nodeOffsets before.dmem pair.1 pair.2=.ok value →
    decodeNode (names.allocated base) nodeOffsets memory pair.1 pair.2=.ok value
  peers : ∀ pair ∈ names.trie.peers, ∀ value,
    decodePeer names nodeOffsets before.dmem pair.1 pair.2=.ok value →
    decodePeer (names.allocated base) nodeOffsets memory pair.1 pair.2=
      .ok (appendOwner names.nextNode pid value)
  table : ∀ offset size, offset+size≤24 → ∀ path,
    word memory path (names.table+offset) size=word before.dmem path (names.table+offset) size
  internal : ∀ current node, (current,node) ∈ (target d).nodes → node.peer=none →
    internalListCheck (names.allocated base) memory current=.ok ()

theorem pending_of_effect {names world machine key cidr pid base memory d}
    (fields : BoundaryFields names nodeOffsets world machine key cidr pid base)
    (related : Corresponds names nodeOffsets machine.data.dmem d)
    (shape : heap names (target d) machine.data.dmem=.ok ())
    (checked : effect machine.data=.ok (memory,base)) :
    Pending names machine.data d key cidr pid base memory := by
  obtain ⟨attached,initialized,attachment,headerCheck,copyCheck⟩ := effect_parts fields.original checked
  have result := core_of_effect fields checked
  obtain ⟨owner,peerNamed,hasPeer⟩ := peer_of_address fields.owner related
  have facts := allocated_facts fields.allocated
  have extent : base+72<2^64 := facts.2.2.1
  have initFrame := header_copy_frame (by omega : base<2^64) headerCheck copyCheck
  have listsApart := fields.initialization_lists_apart related
  have g := fields.geometry related
  have lists := attach_lists related shape g (by omega) fields.fresh peerNamed hasPeer
    (fields.zero_word _ 56 8 (by decide)) (fields.zero_word _ 64 8 (by decide)) attachment
  refine ⟨result.1,?_,?_,?_,?_⟩
  · intro pair member value read
    exact fields.old_node_frame related member result.2 read
  · rintro ⟨current,address⟩ named ⟨actual,count,entries⟩ read
    obtain ⟨identity,countRead,_⟩ := decodePeer_fields read
    dsimp only at identity
    subst actual
    have member : (current,count,entries) ∈ (target d).peers := by
      obtain ⟨value,member,valueRead⟩ := (reconstruct_fields related).peers.left (current,address) named
      exact Except.ok.inj (valueRead.symm.trans read) ▸ member
    have attachedList := lists current address count entries named member
    have listAfter := (list_read_frame (names:=names.allocated base) initFrame listsApart (.peer named)).symm.trans attachedList
    have countAfter : word memory "peer.refcount" (address+nodeOffsets.peerRefcount) 4=.ok count := by
      change word memory "peer.refcount" (address+Layouts.peer_refcount) 4=.ok count
      rw [←Trie.word_frame result.2 "peer.refcount" _ _ (fields.count_apart related named)]
      exact countRead
    unfold decodePeer
    rw [countAfter]
    obtain ⟨first,headRead,run⟩ := bind_ok listAfter
    change word memory "peer.list.head" (address+AllowedipsMutationLayout.allowedips_list) 8=.ok first at headRead
    change peerList (names.allocated base) memory (address+AllowedipsMutationLayout.allowedips_list)
      ((names.allocated base).trie.nodes.length+1) first (address+AllowedipsMutationLayout.allowedips_list) []=_ at run
    simp only [ok_bind,headRead,run,appendOwner]
    rfl
  · intro offset size within path
    exact (Trie.word_frame result.2 path _ _ (fields.table_field_apart related within)).symm
  · intro current node member internal
    have old := attach_internal related shape g fields.fresh peerNamed hasPeer attachment member internal
    exact (internal_list_frame (names.allocated base) initFrame listsApart current) ▸ old

#print axioms pending_of_effect
end Binary.Pair.Allowedips.NodeInit
