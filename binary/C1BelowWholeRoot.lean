import C1BelowWholeFinish
import C1BelowWholeRootFix

/-! Result C1, work package 3, the split path, root sub-case: from
`add+0x338` through the two connections and the root publication to
`AtExit`, by `C1Split.split_root_from_step_nat` with its hypotheses
discharged from the bundle. The saved root-slot pointer comes from
`CutExtra.slot`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root AllowedipsChild Binary.AllowedipsRelation
open Binary.SplitStage3 Binary.SplitStage3.Path
local instance : Labels := Image.linkedLabels

namespace SplitCtx
variable {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator} {c : Context}
  {s : MachineState} {ra : UInt64} {w : World} {d : Device} {family key cidr pid : Nat}
  {stream : List HiddenRecord} {names : Allowedips.Names} {base : Nat}
  {e a t : MachineState} {m : DataMem} {downId child : Nat} {downNode : AipNode}
  {rest : List HiddenRecord} {base2 : Nat}
  (x : SplitCtx fetch L A c s ra w d family key cidr pid stream none names base e a t m downId child
    downNode rest base2)
  {u : MachineState}
  (k : AtConnect c e t u base base2 child (widthOf family)
    (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)) key (chosen family key cidr downNode))
include x k

theorem root_exit (premises : Premises fetch L A) {w' : World} {answer : Int} {exact : Bool} {st : Step}
    (inv : Inv L A w s.data.dmem)
    (facts : StepFacts w family key cidr pid answer w' d stream none exact st)
    (case : st.case = .split)
    (dropped : stream.drop st.consumed = rest) (zero : answer = 0)
    (found : below (bump d) (rootOf d family) key none = some downId) :
    Eventually (instructionStep fetch) (AtExit L A c s e w' answer) u := by
  have position := x.frame
  have top := x.top2
  obtain ⟨related,heapOk⟩ := x.cut.related
  obtain ⟨owner,_,hasPeer⟩ := peer_of_address x.fields.owner related
  have walked := (facts.walked (by rw [case]; decide) (by rw [case]; decide) (by rw [case]; decide)).2
  obtain ⟨_,_,_,_,inverted⟩ := step_below facts.model (.inr (.inl case))
  have seq : st.device.peerAllowedips.seq = (bump d).peerAllowedips.seq := by
    rw [(inverted.split case).2.2.2]; exact seq_splitDevice ..
  have model := facts.model
  subst model
  have rooted : rootOf d family = some downId := found
  -- the root slot
  have valid := (reconstruct_fields related).valid
  obtain ⟨_,tableTop⟩ := C1Split.table_facts valid
  have tableEq : names.table = L.table := x.cut.table
  have offset : (if family = 4 then AllowedipsMutationLayout.root4 else AllowedipsMutationLayout.root6) =
      C1Split.rootOffset (family == 4) := by
    rcases facts.families with four|six
    · subst four; rfl
    · subst six; rfl
  have offsetSmall : C1Split.rootOffset (family == 4) = 0 ∨ C1Split.rootOffset (family == 4) = 8 := by
    unfold C1Split.rootOffset; split <;> simp
  generalize slotAt : names.table + C1Split.rootOffset (family == 4) = trie at *
  have trieBound : trie + 8 ≤ 2^64 := by omega
  have trieFixed {y : BitVec 64} (inside : InRange (.ofNat 64 trie) 8 y) : ∃ span ∈ L.fixed, span.contains y := by
    refine ⟨(trie,8),?_,inside⟩
    apply List.mem_append_left
    rw [←slotAt,tableEq]
    rcases offsetSmall with zero|eight
    · rw [zero]; exact List.mem_map.mpr ⟨(0,8),by decide,rfl⟩
    · rw [eight]; exact List.mem_map.mpr ⟨(8,8),by decide,rfl⟩
  have trieHeap {y : BitVec 64} (inside : InRange (.ofNat 64 trie) 8 y) : L.Heap y := by
    obtain ⟨span,member,within⟩ := trieFixed inside
    exact ⟨span,List.mem_append_left _ member,within⟩
  have childBound := x.childBound
  have baseBound := x.baseBound
  have entry := x.entryU k rfl
  have selBound := entry.directionBound
  have conn {b2 : Nat} (two : b2 < 2) {y : BitVec 64}
      (written : SplitStage3.Writes u.data.regs.r12.toBitVec u.data.regs.rdi.toBitVec u.data.regs.r8.toBitVec
        (chosen family key cidr downNode) b2 y) := x.connNat k selBound two written
  have nodeTop {y : BitVec 64} (inside : InRange (u.data.regs.r12.toBitVec + 48) 8 y) :
      base2 + 48 ≤ y.toNat ∧ y.toNat < base2 + 56 := by
    rw [r12bv k] at inside
    exact natRange (off := 48) (Nat.le_of_lt top) (by decide) inside
  have selected2 (byte shift : Nat) : selected byte shift < 2 := by unfold selected; omega
  have nodeParent : (u.data.dmem.loadInt (BitVec.ofNat 64 base2 + 48) 8).isSome = true := by
    apply k.mapped
    have part := MemoryBytes.loadInt_subword _ _ _ _ (Trie.readNat_loadInt x.grown.zero) 48 8 (by decide)
    exact Option.isSome_of_eq_some part
  have rspE : e.data.regs.rsp.toBitVec.toNat = e.data.regs.rsp.toNat := rfl
  have stackT : t.data.regs.rsp.toNat = e.data.regs.rsp.toNat := by rw [x.stackT]
  have pushBelow {r : UInt64} (same : r = e.data.regs.rsp) {y : BitVec 64}
      (push : InRange (r.toBitVec - 8) 8 y) : y.toNat < e.data.regs.rsp.toNat := by
    rw [same] at push
    obtain ⟨i,small,location⟩ := push
    have value : y.toNat = e.data.regs.rsp.toNat - 8 + i := by rw [location]; bv_omega
    omega
  have slotBytes {r : UInt64} (same : r = e.data.regs.rsp) {y : BitVec 64}
      (inside : InRange (r.toBitVec + 8) 8 y) :
      e.data.regs.rsp.toNat + 8 ≤ y.toNat ∧ y.toNat < e.data.regs.rsp.toNat + 16 := by
    rw [same] at inside
    obtain ⟨i,small,location⟩ := inside
    have value : y.toNat = e.data.regs.rsp.toNat + 8 + i := by rw [location]; bv_omega
    omega
  have slotRead : u.data.dmem.loadInt (u.data.regs.rsp.toBitVec + 8) 8 =
      some ((BitVec.ofNat 64 trie).toNat : Int) := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),k.rsp]
    have atCut := x.extra.slot
    rw [offset,←tableEq,slotAt] at atCut
    have atA := x.ac.slotWord
    rw [x.stackA] at atA
    have atT := x.localSame 8 8 (by decide)
    have atU : t.data.dmem.loadInt (e.data.regs.rsp.toBitVec + 8) 8 =
        u.data.dmem.loadInt (e.data.regs.rsp.toBitVec + 8) 8 := by
      apply k.frame.loadInt
      intro i small written
      have bytes := slotBytes rfl (y := e.data.regs.rsp.toBitVec + 8 + BitVec.ofNat 64 i) ⟨i,small,rfl⟩
      rcases written with node|saved|push|buffer
      · exact (x.heapFar (nodeHeap x.grown.arena node)).1 (by omega)
      · have := range_nat (by omega) saved
        omega
      · have := pushBelow x.stackT push
        omega
      · exact x.contextFar (writes_bytes buffer) (by omega)
    rw [←atU]
    exact (atT.trans atA).trans atCut
  have rootMapped : (u.data.dmem.loadInt (BitVec.ofNat 64 trie) 8).isSome = true := by
    apply x.mappedU k
    have full := reconstruct_fields related
    rw [←slotAt]
    rcases offsetSmall with zero|eight
    · obtain ⟨raw,read,_⟩ := full.root4
      rw [zero]
      exact Option.isSome_of_eq_some (word_loadInt _ _ _ _ _ read)
    · obtain ⟨raw,read,_⟩ := full.root6
      rw [eight]
      exact Option.isSome_of_eq_some (word_loadInt _ _ _ _ _ read)
  have noParent : u.data.regs.rbx = 0 := by
    rw [k.rbx]
    have at0 := x.cut.placedAt
    have nat : e.data.regs.rbx.toNat = 0 := (Except.ok.inj at0).symm
    exact UInt64.toNat_inj.mp nat
  have run := eventually_flight (C1Split.split_root_from_step_nat fetch premises.insertion premises.tracePc c u.data
    (chosen family key cidr downNode) _ _ _ (family == 4)
    (machine := e) (memory := u.data.dmem) (d := bump d) (d0 := d) (family := family) (downId := downId)
    (downBase := child) (base := base) (base2 := base2) (names := names) owner
    (entry := entry) (noParent := noParent) (ready := k.ready)
    (contextApart := fun y read written =>
      (x.heapFar (x.keptHeap (x.keptOf (by have := conn (selected2 _ _) written; omega)))).2.1 read)
    (contextApartRoot := by
      rw [slotAt]
      rintro y read (node|slotWord)
      · have := nodeTop node
        exact (x.heapFar (x.keptHeap (x.keptOf (by omega)))).2.1 read
      · exact (x.heapFar (trieHeap slotWord)).2.1 read)
    (slotRead := by rw [slotAt]; exact slotRead)
    (nodeParentMapped := by rw [r12bv k]; exact nodeParent)
    (rootMapped := by rw [slotAt]; exact rootMapped)
    (savedSlotApart := by
      intro y saved
      have bytes := slotBytes k.rsp saved
      constructor
      · intro written
        have := conn (selected2 _ _) written
        have kept := x.keptOf (y := y) (by omega)
        exact (x.heapFar (x.keptHeap kept)).1 ⟨by omega,by omega⟩
      · rintro (push|buffer)
        · have := pushBelow k.rsp push
          omega
        · exact x.contextFar (writes_bytes buffer) (by omega))
    (wordsApart := by
      rw [slotAt]
      intro y words
      apply x.callFar k
      rcases words with node|slotWord
      · have := nodeTop node
        exact x.keptHeap (x.keptOf (by omega))
      · exact trieHeap slotWord)
    (node := r12bv k) (down := rdibv k) (leaf := r8bv k)
    (readApart := fun span member y inside => x.callFar k (x.readHeap2 span member y inside))
    (metadataApart := fun span member y inside =>
      x.callFar k (x.readHeap2 span (Placement.metadata_read member) y inside))
    (related := related) (heapBefore := heapOk) (pending := x.pendingU k) (valid2 := x.valid2) (init := x.init k)
    (downNamed := x.named) (hasPeer := hasPeer)
    (cut := rfl) (width := x.extra.width) (fam := rfl) (ord := facts.trie) (case := case) (walked := walked)
    (found := rooted) (downFacts := x.downFacts))
  rw [slotAt] at run
  apply Rollback.start_at k.pc
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro v ⟨⟨pc,rbx,rsp,_,_,_,_,_,readyV,frameV,relatedV,shapeV,_,_⟩,mappedV,flagV⟩
  refine x.finish k premises inv facts dropped zero seq _ pc rbx rsp relatedV shapeV readyV frameV ?_ mappedV flagV
  rintro y (written|call|node|slotWord)
  · have := conn (selected2 _ _) written
    exact .inl (.inl (x.keptOf (by omega)))
  · exact .inr call
  · have := nodeTop node
    exact .inl (.inl (x.keptOf (by omega)))
  · exact .inl (.inr (trieFixed slotWord))

end SplitCtx

#print axioms SplitCtx.root_exit
end Binary.Statements.C1.Proof
