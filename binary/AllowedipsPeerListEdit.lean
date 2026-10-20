import AllowedipsPeerListShape
import PairBucketErase

namespace Binary.Pair.Allowedips.Ring
open Leanux Leanux.WG
open Index (skip)

def erase (removed : Nat) (nodes : Nodes) : Nodes := nodes.filter (fun node => node.1 != removed)

theorem erase_absent {removed : Nat} {nodes : Nodes} (absent : removed ∉ nodes.map Prod.fst) :
    erase removed nodes=nodes := by
  apply List.filter_eq_self.mpr
  intro node member
  have ne : node.1≠removed := by intro equal; exact absent (List.mem_map.mpr ⟨node,member,equal⟩)
  simpa using ne

theorem Chain.first_erase {names m head previous nodes removed oldPrev oldNext id}
    (shape : Chain names m head previous nodes) (focus : Fields names m head oldPrev removed oldNext id)
    (distinct : (nodes.map Prod.fst).Nodup) :
    first head (erase removed nodes)=skip removed oldNext (first head nodes) := by
  cases shape with
  | nil => simp [Ring.erase,first,skip,Ne.symm focus.notHead]
  | @cons previous link current rest fields tail =>
    by_cases same : link=removed
    · subst link
      have nd := List.nodup_cons.mp distinct
      have unchanged := erase_absent nd.1
      have next : first head rest=oldNext := word_values fields.forward focus.forward
      simp only [Ring.erase,List.filter_cons,show (removed != removed)=false from by simp,Bool.false_eq_true,ite_false]
      change first head (erase removed rest)=skip removed oldNext removed
      rw [unchanged,next]
      simp [skip]
    · simp only [Ring.erase,List.filter_cons,show (link != removed)=true from by simpa using same,ite_true]
      simp [first,skip,same]

/-- Rebuild a circular list after the two unlink stores. The local word
contracts include the sentinel, so singleton and tail deletion are covered. -/
theorem Chain.erase {names before after head previous nodes removed oldPrev oldNext id}
    (shape : Chain names before head previous nodes)
    (focus : Fields names before head oldPrev removed oldNext id)
    (distinct : (nodes.map Prod.fst).Nodup)
    (sentinel : ∀ p, word before "peer.list.prev" (head+8) 8=.ok p →
      word after "peer.list.prev" (head+8) 8=.ok (skip removed oldPrev p))
    (updated : ∀ link current p q, (link,current) ∈ nodes → link≠removed →
      Fields names before head p link q current →
      Fields names after head (skip removed oldPrev p) link (skip removed oldNext q) current) :
    Chain names after head (skip removed oldPrev previous) (erase removed nodes) := by
  induction shape with
  | nil back => exact .nil (sentinel _ back)
  | @cons previous link current rest fields tail ih =>
    have nd := List.nodup_cons.mp distinct
    have restShape := ih nd.2 (fun link current p q member =>
      updated link current p q (List.mem_cons_of_mem _ member))
    by_cases same : link=removed
    · subst link
      have prev : previous=oldPrev := word_values fields.back focus.back
      simpa only [Ring.erase,List.filter_cons,show (removed != removed)=false from by simp,Bool.false_eq_true,
        ite_false,skip,prev,ite_true,ite_self] using restShape
    · have next := tail.first_erase focus nd.2
      have newFields := updated link current previous (first head rest) (by simp) same fields
      rw [←next] at newFields
      rw [show skip removed oldPrev link=link from ite_eq_right same] at restShape
      simpa only [Ring.erase,List.filter_cons,show (link != removed)=true from by simpa using same,ite_true]
        using Chain.cons newFields restShape

/-- Recover the actual executable decoder after an unlink; the only new facts
are local word effects, never a presumed successful post-state decode. -/
theorem peerList_erase {names before after head fuel link previous seen entries removed oldPrev oldNext id}
    (decoded : peerList names before head fuel link previous seen=.ok entries)
    (focus : Fields names before head oldPrev removed oldNext id)
    (sentinel : ∀ p, word before "peer.list.prev" (head+8) 8=.ok p →
      word after "peer.list.prev" (head+8) 8=.ok (skip removed oldPrev p))
    (updated : ∀ nodes : Nodes, entries=nodes.map Prod.snd → link=first head nodes →
      Chain names before head previous nodes →
      ∀ addr current p q, (addr,current) ∈ nodes → addr≠removed →
        Fields names before head p addr q current →
        Fields names after head (skip removed oldPrev p) addr (skip removed oldNext q) current) :
    ∃ nodes : Nodes, entries=nodes.map Prod.snd ∧ link=first head nodes ∧
      Chain names before head previous nodes ∧
      peerList names after head fuel (skip removed oldNext link) (skip removed oldPrev previous) seen=
        .ok ((erase removed nodes).map Prod.snd) := by
  obtain ⟨nodes,equal,atHead,shape,length,distinct,fresh⟩ := peerList_shape decoded
  have edited := shape.erase focus distinct sentinel (updated nodes equal atHead shape)
  have nd : ((erase removed nodes).map Prod.fst).Nodup :=
    distinct.sublist (List.Sublist.map Prod.fst List.filter_sublist)
  have unseen : ∀ p ∈ (erase removed nodes).map Prod.fst, p ∉ seen := by
    intro p member
    exact fresh p (List.Sublist.subset (List.Sublist.map Prod.fst List.filter_sublist) member)
  have run := edited.decode fuel seen (Nat.lt_of_le_of_lt (List.length_filter_le _ _) length) nd unseen
  rw [shape.first_erase focus distinct,←atHead] at run
  exact ⟨nodes,equal,atHead,shape,run⟩

theorem Chain.first_append {names m head previous nodes} (shape : Chain names m head previous nodes)
    (link id : Nat) : first head (nodes++[(link,id)])=skip head link (first head nodes) := by
  cases shape with
  | nil => simp [first,skip]
  | cons fields tail => simp [first,skip,fields.notHead]

/-- Append uses the destination list after any unlink. The traversal changes
only its former tail's next link and the sentinel's previous link. -/
theorem Chain.append {names nextNames before after head previous nodes link id}
    (shape : Chain names before head previous nodes)
    (sentinel : word after "peer.list.prev" (head+8) 8=.ok link)
    (added : ∀ p, word before "peer.list.prev" (head+8) 8=.ok p →
      Fields nextNames after head p link head id)
    (updated : ∀ a current p q, (a,current) ∈ nodes → Fields names before head p a q current →
      Fields nextNames after head p a (skip head link q) current) :
    Chain nextNames after head previous (nodes++[(link,id)]) := by
  induction shape with
  | nil back => exact .cons (added _ back) (.nil sentinel)
  | @cons previous a current rest fields tail ih =>
    have changed := updated a current previous (first head rest) (by simp) fields
    rw [←tail.first_append link id] at changed
    exact .cons changed (ih (fun a current p q member => updated a current p q (by simp [member])))

#print axioms peerList_erase
#print axioms Chain.append
end Binary.Pair.Allowedips.Ring
