import C1BelowCoverSegment

/-! Result C1, work package 3, covering path below a parent: from the
prefix's comparison state to `AtExit`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase AllowedipsChild
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root Binary.AllowedipsRelation
local instance : Labels := Image.linkedLabels

theorem cover_parent_exit {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator}
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
    {p : NodeId} (placedEq : placed=some p)
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
  have idEq : downId'=downId := Option.some.inj (low.hasBelow.symm.trans belowEq)
  subst idEq
  have nodeEq : down'=downNode := Option.some.inj (low.hasDown.symm.trans hasDown)
  subst nodeEq
  obtain ⟨covers,answerZero,deviceEq⟩ := low.cover case
  have walked := (facts.walked (by rw [case]; decide) (by rw [case]; decide) (by rw [case]; decide)).2
  rw [low.inexact] at walked
  obtain ⟨parentNode,hasParent,pWidth,measure,prefixEq,occupied,downWidth,downMeasure,downPrefix⟩ :=
    walk_cover_parent (bump d) _ key cidr (widthOf family) p downId' down' walked belowEq hasDown covers
  have covered : cidr ≤ common (widthOf family) down'.bits key := by
    unfold leastOf at covers
    omega
  have parentNamed : (p,e.data.regs.rbx.toNat) ∈ names.trie.nodes := named_of_address cut.placedAt
  obtain ⟨owner,_,hasPeer⟩ := peer_of_address fields.owner related
  have different : downId'≠p := by
    rintro rfl
    have same : down'=parentNode := Option.some.inj (hasDown.symm.trans hasParent)
    rw [same] at downMeasure
    omega
  have g := fields.geometry related
  have rbxT : t.data.regs.rbx.toBitVec=.ofNat 64 e.data.regs.rbx.toNat := by rw [held.bx,ofNat_uint64]
  have otherHeap : ∀ a, InRange t.data.regs.rbx.toBitVec 72 a → L.Heap a :=
    fun a h => node_heap (cut.arena _ parentNamed) (rbxT ▸ h)
  have apart := cover_apart ready cut extra held.stack named (InRange t.data.regs.rbx.toBitVec 72) otherHeap
    (fun a h o => nodes_apart g (List.mem_append_left _ named) (List.mem_append_left _ parentNamed)
      (fun same => different (congrArg Prod.fst same)) a h (rbxT ▸ o))
    (fun a h o => nodes_apart g (allocated_node names base) (List.mem_append_left _ parentNamed)
      (fun same => fields.fresh _ parentNamed (congrArg Prod.snd same).symm) a h (rbxT ▸ o))
  have linked := cover_linked premises ready cut extra hasDown summary named comp compared covered
    downMeasure downWidth _ apart
  -- the parent's selectors and the fresh node's key
  have decodedDown := held.pending.old_node related named hasDown
  have bounded : down'.cidr ≤ down'.bitlen := (Trie.decodeNode_fields decodedDown).bounded
  have decodedParent := held.pending.old_node related parentNamed hasParent
  have pFields := Trie.decodeNode_fields decodedParent
  have pFamily : parentNode.bitlen=32 ∨ parentNode.bitlen=128 := pFields.family
  have pShort : parentNode.cidr<parentNode.bitlen := by omega
  have pPosition := selector_position parentNode.bitlen parentNode.cidr pFamily pShort
  have freshWords : QueryWords t.data.dmem (.ofNat 64 (base+32)) parentNode.bitlen key := by
    have words := key_words held.pending.core
    rw [pWidth,←width]
    exact words
  have keyRead := queryByte_read t.data.dmem (.ofNat 64 (base+32)) parentNode.bitlen key
    (byteSelector parentNode.bitlen parentNode.cidr) pFamily pPosition.2 freshWords
  have dirEq := queryByte_select parentNode.bitlen key parentNode.cidr pFamily pShort
  have parentRange := (Trie.reconstruct_fields related.trie).nodeRange _ _ parentNamed
  have parentNonzero : t.data.regs.rbx≠0 := by
    intro zero
    have nat : e.data.regs.rbx.toNat=0 := by rw [←held.bx,zero]; rfl
    have := parentRange.1
    omega
  have index16 : byteSelector parentNode.bitlen parentNode.cidr<16 := by
    rcases pFamily with four|four <;> rw [four] at pPosition <;> rw [four] <;> omega
  have a25 : (BitVec.ofNat 64 e.data.regs.rbx.toNat+25 : BitVec 64)=.ofNat 64 (e.data.regs.rbx.toNat+25) := by
    rw [BitVec.ofNat_add]; rfl
  have a26 : (BitVec.ofNat 64 e.data.regs.rbx.toNat+26 : BitVec 64)=.ofNat 64 (e.data.regs.rbx.toNat+26) := by
    rw [BitVec.ofNat_add]; rfl
  have a8 : (BitVec.ofNat 64 e.data.regs.rbx.toNat+8 : BitVec 64)=.ofNat 64 (e.data.regs.rbx.toNat+8) := by
    rw [BitVec.ofNat_add]; rfl
  have a16 : (BitVec.ofNat 64 e.data.regs.rbx.toNat+16 : BitVec 64)=.ofNat 64 (e.data.regs.rbx.toNat+16) := by
    rw [BitVec.ofNat_add]; rfl
  have a32 : (BitVec.ofNat 64 base+32 : BitVec 64)=.ofNat 64 (base+32) := by
    rw [BitVec.ofNat_add]; rfl
  have a48 : (BitVec.ofNat 64 base+48 : BitVec 64)=.ofNat 64 (base+48) := by
    rw [BitVec.ofNat_add]; rfl
  have bBound : down'.bits/2^(widthOf family-1-cidr)%2<2 := Nat.mod_lt _ (by decide)
  have whole : Eventually (instructionStep fetch) (fun x => ∃ mid,
      C1Cover.Done c t.data (.ofNat 64 child) (.ofNat 64 base) (InRange t.data.regs.rbx.toBitVec 72) mid
        (C1Cover.coverParent mid (.ofNat 64 child) (.ofNat 64 base) t.data.regs.rbx.toBitVec
          (down'.bits/2^(widthOf family-1-cidr)%2)
          (selected (queryByte parentNode.bitlen key (byteSelector parentNode.bitlen parentNode.cidr))
            (7-parentNode.cidr%8))) x) t := by
    apply eventually_trans (instructionStep fetch) _ _ _ linked
    rintro y ⟨mid,link⟩
    apply eventually_weaken (instructionStep fetch) _ _ _ _
      (C1Cover.parent_half fetch premises.insertion premises.tracePc c t.data _ _ _ mid y
        (byteSelector parentNode.bitlen parentNode.cidr) (7-parentNode.cidr%8)
        (queryByte parentNode.bitlen key (byteSelector parentNode.bitlen parentNode.cidr))
        apart bBound link parentNonzero index16 (by omega) (queryByte_bound _ _ _)
        (by rw [rbxT,a25]; exact word_loadInt _ _ _ _ _ pFields.byteSelector)
        (by rw [rbxT,a26]; exact word_loadInt _ _ _ _ _ pFields.bitSelector)
        (by rw [a32]; exact keyRead)
        (by rw [a48]
            exact held.mapped _ _ (Option.isSome_of_eq_some
              (word_loadInt _ _ _ _ _ (fields.zero_word "fresh" 48 8 (by omega)))))
        (by rw [rbxT,a8]; exact (children_mapped decodedParent).1)
        (by rw [rbxT,a16]; exact (children_mapped decodedParent).2))
    exact fun x done => ⟨mid,done⟩
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (eventually_flight whole)
  rintro x ⟨⟨mid,done⟩,mapped,flag⟩
  rw [rbxT,dirEq] at done
  have apartRead : ∀ a, (InRange t.data.regs.rsp.toBitVec 48 a ∨ C1Cover.CallWrites t.data.regs.rsp c a) →
      (Zone e.data.regs.rsp a ∨ c.writes a) := by
    rw [held.stack]
    rintro a (locals|word|buffer)
    · exact .inl (zone_locals (by decide) locals)
    · exact .inl (zone_word word)
    · exact .inr buffer
  have data := C1Cover.parent_data owner fields related checked held.pending done
    (fun span member a inside h => res.projection span member a inside (apartRead a h))
    (fun a inside h => res.table a inside (apartRead a h))
    named parentNamed hasDown hasParent hasPeer (Nat.mod_lt _ (by decide)) (width ▸ bBound) occupied
    (width.trans pWidth.symm) measure (pWidth ▸ prefixEq) rfl downMeasure (width ▸ downPrefix) (by rw [width])
  have below := target_nodes_below related
  have freshDown : (bump d).nextNode≠downId' := by
    have := below (downId',down') (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasDown)
    exact fun same => by rw [same] at this; exact Nat.lt_irrefl _ this
  have freshParent : (bump d).nextNode≠p := by
    have := below (p,parentNode) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasParent)
    exact fun same => by rw [same] at this; exact Nat.lt_irrefl _ this
  have device := coverDevice_parent d family key cidr pid p downId' down' parentNode owner
    hasDown hasParent hasPeer freshDown freshParent different
  rw [←deviceEq,←width] at device
  exact cover_at_exit premises inv ready facts case answerZero cut extra compared held.stack named
    otherHeap
    (fun a h _ => ⟨e.data.regs.rbx.toNat,
      List.mem_append_left _ (List.mem_map.mpr ⟨(p,e.data.regs.rbx.toNat),parentNamed,rfl⟩),rbxT ▸ h⟩)
    done.pc done.rbx done.rsp done.ready (rbxT ▸ done.frame) mapped flag data.1 data.2
    (by rw [device,width]) rfl

#print axioms cover_parent_exit
end Binary.Statements.C1.Proof
