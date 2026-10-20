import PairAllowedipsState
import PairExcept

namespace Binary.Pair.Allowedips.Ring
open Leanux Leanux.WG

abbrev Nodes := List (Nat × NodeId)

def first (head : Nat) (nodes : Nodes) : Nat := nodes.head?.map Prod.fst |>.getD head

structure Fields (names : Names) (m : DataMem) (head previous link next : Nat) (id : NodeId) : Prop where
  known : names.trie.nodes.any (fun (_,a) => link==a+AllowedipsMutationLayout.peer_list)=true
  notHead : link≠head
  valid : AllowedipsMutationLayout.peer_list≤link
  owner : Trie.pointer names.trie.nodes "peer.list.node" (link-AllowedipsMutationLayout.peer_list)=.ok (some id)
  back : word m "peer.list.prev" (link+8) 8=.ok previous
  forward : word m "peer.list.next" link 8=.ok next

/-- A finite presentation of successful executable list reconstruction. The
sentinel's backward word is retained even when the represented list is empty. -/
inductive Chain (names : Names) (m : DataMem) (head : Nat) : Nat → Nodes → Prop
  | nil {previous} (back : word m "peer.list.prev" (head+8) 8=.ok previous) :
      Chain names m head previous []
  | cons {previous link id rest}
      (fields : Fields names m head previous link (first head rest) id)
      (tail : Chain names m head link rest) : Chain names m head previous ((link,id)::rest)

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

theorem peerList_head (names : Names) (m : DataMem) (head fuel previous : Nat) (seen : List Nat)
    (back : word m "peer.list.prev" (head+8) 8=.ok previous) :
    peerList names m head (fuel+1) head previous seen=.ok [] := by
  simp only [peerList,beq_self_eq_true,Bool.true_or,Bool.not_true,Bool.false_eq_true,ite_false,back,ok_bind]
  rfl

theorem peerList_shape {names m head fuel link previous seen entries}
    (checked : peerList names m head fuel link previous seen=.ok entries) :
    ∃ nodes : Nodes, entries=nodes.map Prod.snd ∧ link=first head nodes ∧
      Chain names m head previous nodes ∧ nodes.length<fuel ∧
      (nodes.map Prod.fst).Nodup ∧ ∀ p ∈ nodes.map Prod.fst, p ∉ seen := by
  induction fuel generalizing link previous seen entries with
  | zero => cases checked
  | succ fuel ih =>
    rw [peerList] at checked
    by_cases known : (link==head || names.trie.nodes.any (fun (_,a) => link==a+AllowedipsMutationLayout.peer_list))=true
    · simp only [known,Bool.not_true,Bool.false_eq_true,ite_false] at checked
      obtain ⟨back,backRead,checked⟩ := bind_ok checked
      obtain ⟨backEq,checked⟩ := check_ok _ _ _ _ checked
      have backEq' : back=previous := eq_of_beq backEq
      subst back
      simp only [beq_self_eq_true,ite_true] at checked
      by_cases isHead : link=head
      · subst link
        simp only [beq_self_eq_true,ite_true] at checked
        have equal : entries=[] := (Except.ok.inj checked).symm
        exact ⟨[],equal,rfl,.nil backRead,by simp,by simp,by simp⟩
      · simp only [show (link==head)=false from beq_eq_false_iff_ne.mpr isHead,Bool.false_eq_true,ite_false] at checked
        by_cases cycle : seen.contains link=true
        · simp only [cycle,ite_true] at checked; cases checked
        · simp only [show seen.contains link=false from by simpa using cycle,Bool.false_eq_true,ite_false] at checked
          by_cases valid : AllowedipsMutationLayout.peer_list≤link
          · simp only [valid,ite_true] at checked
            obtain ⟨owner,ownerRead,checked⟩ := bind_ok checked
            cases owner with
            | none => cases checked
            | some id =>
              obtain ⟨next,nextRead,checked⟩ := bind_ok checked
              obtain ⟨rest,restRead,checked⟩ := bind_ok checked
              have result : id::rest=entries := Except.ok.inj checked
              obtain ⟨nodes,equal,atHead,shape,length,distinct,fresh⟩ := ih restRead
              have named : names.trie.nodes.any (fun (_,a) => link==a+AllowedipsMutationLayout.peer_list)=true := by
                simpa only [show (link==head)=false from beq_eq_false_iff_ne.mpr isHead,Bool.false_or] using known
              refine ⟨(link,id)::nodes,?_,rfl,.cons ⟨named,isHead,valid,ownerRead,backRead,?_⟩ shape,
                by simpa using Nat.succ_lt_succ length,?_,?_⟩
              · rw [←result,equal]; rfl
              · simpa only [atHead] using nextRead
              · simp only [List.map_cons,List.nodup_cons]
                exact ⟨fun member => fresh link member (by simp),distinct⟩
              · intro p member
                rcases List.mem_cons.mp member with rfl | member
                · simpa using cycle
                · exact fun old => fresh p member (by simp [old])
          · simp only [valid,ite_false] at checked; cases checked
    · have rejected : (link==head || names.trie.nodes.any (fun (_,a) => link==a+AllowedipsMutationLayout.peer_list))=false := by
        simpa using known
      simp only [rejected,Bool.not_false,ite_true] at checked
      cases checked

/-- Edits reestablish this presentation and then recover the same executable
reconstruction, including its fuel and no-cycle checks. -/
theorem Chain.decode {names m head previous nodes} (shape : Chain names m head previous nodes)
    (fuel : Nat) (seen : List Nat) (length : nodes.length<fuel)
    (distinct : (nodes.map Prod.fst).Nodup) (fresh : ∀ p ∈ nodes.map Prod.fst, p ∉ seen) :
    peerList names m head fuel (first head nodes) previous seen=.ok (nodes.map Prod.snd) := by
  induction shape generalizing fuel seen with
  | nil back =>
    cases fuel with
    | zero => simp at length
    | succ fuel => exact peerList_head names m head fuel _ seen back
  | @cons previous link id rest fields tail ih =>
    cases fuel with
    | zero => simp at length
    | succ fuel =>
      have notSeen : link ∉ seen := fresh link (by simp)
      have nd := List.nodup_cons.mp distinct
      have recurse := ih fuel (link::seen) (by simpa using length) nd.2 (by
        intro p member present
        rcases List.mem_cons.mp present with rfl | old
        · exact nd.1 member
        · exact fresh p (by simp [member]) old)
      change peerList names m head (fuel+1) link previous seen=.ok (id::rest.map Prod.snd)
      rw [peerList]
      simp only [fields.known,Bool.or_true,Bool.not_true,Bool.false_eq_true,ite_false,
        fields.back,ok_bind,beq_self_eq_true,ite_true,
        show (link==head)=false from beq_eq_false_iff_ne.mpr fields.notHead,
        show seen.contains link=false from by simpa using notSeen,
        fields.valid,fields.owner,fields.forward,recurse]
      rfl

#print axioms peerList_shape
#print axioms Chain.decode
end Binary.Pair.Allowedips.Ring
