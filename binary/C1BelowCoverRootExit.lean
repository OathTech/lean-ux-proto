import C1BelowCoverSegment
import C1BelowCoverRootData
import C1BelowCoverRootFacts

/-! Result C1, work package 3, covering path at the root: from the prefix's
comparison state to `AtExit`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase AllowedipsChild
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root Binary.AllowedipsRelation
local instance : Labels := Image.linkedLabels

theorem cover_root_exit {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator}
    (premises : Premises fetch L A)
    {c : Context} {s : MachineState} {w w' : World} {family key cidr pid : Nat} {ra : UInt64}
    {answer : Int} {d : Device} {stream : List HiddenRecord} {placed : Option NodeId} {exact : Bool}
    {st : Step} {names : Allowedips.Names} {base : Nat} {e : MachineState}
    (inv : Inv L A w s.data.dmem)
    (ready : insertReady L A c s family key cidr pid ra=.ok ())
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (case : st.case = .cover)
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (extra : CutExtra L s e family)
    (placedEq : placed=none)
    {downId child : Nat} {downNode : AipNode} {m : DataMem} {t : MachineState}
    (belowEq : below (bump d) (rootOf d family) key placed=some downId)
    (hasDown : (bump d).nodes.get? downId=some downNode)
    (summary : NodeInit.effect e.data=.ok (m,base))
    (named : (downId,child) ∈ names.trie.nodes)
    (comp : Compared names c e.data (bump d) key cidr pid base child (widthOf family) downNode.bits m t)
    (compared : AtCompare L A c s e names base cidr stream m t) :
    Eventually (instructionStep fetch) (AtExit L A c s e w' answer) t := by
  subst placedEq
  have rfacts := ready_facts ready
  have fields := NodeInit.boundary_fields cut.boundary
  obtain ⟨related,checked⟩ := cut.related
  have res := resources rfacts cut extra
  have held := comp.held
  have width := extra.width
  -- the step
  obtain ⟨rootId,downId',down',rest,low⟩ := step_below facts.model (.inl case)
  obtain ⟨covers,answerZero,deviceEq⟩ := low.cover case
  have walked := (facts.walked (by rw [case]; decide) (by rw [case]; decide) (by rw [case]; decide)).2
  rw [low.inexact] at walked
  have sameRoot : some rootId=rootOf d family := low.root.symm.trans (rootOf_slot d family)
  have idEq : downId'=downId := by
    have h := low.hasBelow
    rw [sameRoot] at h
    exact Option.some.inj (h.symm.trans belowEq)
  subst idEq
  have nodeEq : down'=downNode := Option.some.inj (low.hasDown.symm.trans hasDown)
  subst nodeEq
  obtain ⟨rootEq,downWidth,downMeasure,downPrefix⟩ :=
    walk_cover_root (bump d) _ key cidr (widthOf family) downId' down' walked belowEq hasDown covers
  have covered : cidr ≤ common (widthOf family) down'.bits key := by
    unfold leastOf at covers
    omega
  obtain ⟨owner,_,hasPeer⟩ := peer_of_address fields.owner related
  -- the root slot
  have arena : C1Split.Arena (names.allocated base) := C1Split.arena_of_valid fields.allocated
  have tableFacts := C1Split.table_facts (reconstruct_fields related).valid
  have offsetEq : (if family=4 then AllowedipsMutationLayout.root4 else AllowedipsMutationLayout.root6)=
      C1Split.rootOffset (family == 4) := by
    by_cases four : family=4 <;> simp [four,C1Split.rootOffset] <;> rfl
  have offsetBound : C1Split.rootOffset (family == 4)+8≤24 := by
    cases (family == 4) <;> decide
  have slotSmall : names.table+C1Split.rootOffset (family == 4)<2^64 := by have := tableFacts.2; omega
  have tableEq : names.table=L.table := cut.table
  have otherHeap : ∀ a, InRange (.ofNat 64 (names.table+C1Split.rootOffset (family == 4))) 8 a → L.Heap a := by
    intro a h
    rw [tableEq] at h
    refine fixed_table (offset:=C1Split.rootOffset (family == 4)) (size:=8) ?_ h
    cases (family == 4) <;> simp [tableFields,C1Split.rootOffset] <;> decide
  have apart := cover_apart ready cut extra held.stack named
    (InRange (.ofNat 64 (names.table+C1Split.rootOffset (family == 4))) 8) otherHeap
    (fun a h => C1Split.node_root_apart arena (List.mem_append_left _ named) (offset:=0) (size:=72)
      (by decide) (family == 4) a h)
    (fun a h => C1Split.node_root_apart arena (allocated_node names base) (offset:=0) (size:=72)
      (by decide) (family == 4) a h)
  have linked := cover_linked premises ready cut extra hasDown summary named comp compared covered
    downMeasure downWidth _ apart
  have rbxZero : t.data.regs.rbx=0 := by
    have address := cut.placedAt
    have zero : e.data.regs.rbx.toNat=0 := (Except.ok.inj address).symm
    rw [held.bx]
    exact UInt64.toNat_inj.mp zero
  have slotRead : t.data.dmem.loadInt (t.data.regs.rsp.toBitVec+8) 8=
      some ((BitVec.ofNat 64 (names.table+C1Split.rootOffset (family == 4))).toNat : Int) := by
    rw [compared.slotWord,extra.slot,BitVec.toNat_ofNat,Nat.mod_eq_of_lt slotSmall,offsetEq,tableEq]
  have a48 : (BitVec.ofNat 64 base+48 : BitVec 64)=.ofNat 64 (base+48) := by
    rw [BitVec.ofNat_add]; rfl
  have rootMapped : (t.data.dmem.loadInt (.ofNat 64 (names.table+C1Split.rootOffset (family == 4))) 8).isSome=true := by
    apply held.mapped
    obtain ⟨r4,read4,_⟩ := (reconstruct_fields related).root4
    obtain ⟨r6,read6,_⟩ := (reconstruct_fields related).root6
    cases (family == 4)
    · exact Option.isSome_of_eq_some (word_loadInt _ _ _ _ _ read6)
    · exact Option.isSome_of_eq_some (word_loadInt _ _ _ _ _ read4)
  have bBound : down'.bits/2^(widthOf family-1-cidr)%2<2 := Nat.mod_lt _ (by decide)
  have whole : Eventually (instructionStep fetch) (fun x => ∃ mid,
      C1Cover.Done c t.data (.ofNat 64 child) (.ofNat 64 base)
        (InRange (.ofNat 64 (names.table+C1Split.rootOffset (family == 4))) 8) mid
        (C1Cover.coverRoot mid (.ofNat 64 child) (.ofNat 64 base)
          (.ofNat 64 (names.table+C1Split.rootOffset (family == 4)))
          (down'.bits/2^(widthOf family-1-cidr)%2)) x) t := by
    apply eventually_trans (instructionStep fetch) _ _ _ linked
    rintro y ⟨mid,link⟩
    apply eventually_weaken (instructionStep fetch) _ _ _ _
      (C1Cover.root_half fetch premises.insertion premises.tracePc c t.data _ _ _ _ mid y
        apart bBound link rbxZero slotRead
        (by rw [a48]
            exact held.mapped _ _ (Option.isSome_of_eq_some
              (word_loadInt _ _ _ _ _ (fields.zero_word "fresh" 48 8 (by omega)))))
        rootMapped)
    exact fun x done => ⟨mid,done⟩
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (eventually_flight whole)
  rintro x ⟨⟨mid,done⟩,mapped,flag⟩
  have apartRead : ∀ a, (InRange t.data.regs.rsp.toBitVec 48 a ∨ C1Cover.CallWrites t.data.regs.rsp c a) →
      (Zone e.data.regs.rsp a ∨ c.writes a) := by
    rw [held.stack]
    rintro a (locals|word|buffer)
    · exact .inl (zone_locals (by decide) locals)
    · exact .inl (zone_word word)
    · exact .inr buffer
  have rootHere : (if (family == 4)=true then (Allowedips.target (bump d)).table.root4
      else (Allowedips.target (bump d)).table.root6)=some downId' := by
    have h := rootEq
    unfold rootOf at h
    exact h
  have data := C1Cover.root_data owner (family == 4) fields related checked held.pending done
    (fun span member a inside h => res.projection span member a inside (apartRead a h))
    (fun a inside h => res.table a inside (apartRead a h))
    named hasDown hasPeer (width ▸ bBound) rootHere
    (split_other_root (d:=bump d) facts.trie rootHere) width (downWidth.trans width.symm) downMeasure
    (width ▸ downPrefix) (by rw [width])
  have freshDown : (bump d).nextNode≠downId' := by
    have := target_nodes_below related (downId',down') (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown)
    exact fun same => by rw [same] at this; exact Nat.lt_irrefl _ this
  have device := coverDevice_root d family key cidr pid downId' down' owner hasDown hasPeer freshDown
  rw [←deviceEq,←width] at device
  exact cover_at_exit premises inv ready facts case answerZero cut extra compared held.stack named
    otherHeap
    (fun a h arenaAt => by
      exfalso
      obtain ⟨span,member,within⟩ := arenaAt
      rw [tableEq] at h
      refine spansApart_sound cut.apart (l:=(L.table,AllowedipsMutationLayout.tableSize)) (by simp [objectsOf])
        member ?_ within
      exact Undo.range_slice (n:=AllowedipsMutationLayout.tableSize) offsetBound h)
    done.pc done.rbx done.rsp done.ready done.frame mapped flag data.1 data.2
    (by rw [device,width]) (by cases (family == 4) <;> rfl)

#print axioms cover_root_exit
end Binary.Statements.C1.Proof
