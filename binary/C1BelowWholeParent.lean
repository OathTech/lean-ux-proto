import C1BelowWholeFinish

/-! Result C1, work package 3, the split path, parent sub-case: from
`add+0x338` through the three connections to `AtExit`, by
`C1Split.split_parent_from_step` with its hypotheses discharged from the
bundle. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root AllowedipsChild Binary.AllowedipsRelation
open Binary.SplitStage3 Binary.SplitStage3.Path
local instance : Labels := Image.linkedLabels

/-- Two old nodes with different identities do not overlap. -/
theorem old_nodes_apart {names : Allowedips.Names} {m : DataMem} {dev : Device}
    (related : Allowedips.Corresponds names nodeOffsets m dev) {i j p q : Nat}
    (first : (i,p) ∈ names.trie.nodes) (second : (j,q) ∈ names.trie.nodes) (different : i ≠ j) :
    p + 72 ≤ q ∨ q + 72 ≤ p := by
  have arena := C1Split.arena_of_valid (reconstruct_fields related).valid
  have distinct := arena.address_ne first second different
  have apart := Trie.pairwise_mem_ne (R := fun a b : Pair.Span => disjointRanges a.1 a.2 b.1 b.2 = true)
    (fun a b h => by simpa only [disjointRanges,Bool.or_comm] using h) arena.geometry.apart
    (node_allocation (o := nodeOffsets) first) (node_allocation (o := nodeOffsets) second)
    (fun same => distinct (congrArg Prod.fst same))
  change disjointRanges p 72 q 72 = true at apart
  simp only [disjointRanges,Bool.or_eq_true] at apart
  exact apart.imp of_decide_eq_true of_decide_eq_true

namespace SplitCtx
variable {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator} {c : Context}
  {s : MachineState} {ra : UInt64} {w : World} {d : Device} {family key cidr pid : Nat}
  {stream : List HiddenRecord} {names : Allowedips.Names} {base : Nat}
  {e a t : MachineState} {m : DataMem} {downId child : Nat} {downNode : AipNode}
  {rest : List HiddenRecord} {base2 : Nat} {p : NodeId}
  (x : SplitCtx fetch L A c s ra w d family key cidr pid stream (some p) names base e a t m downId child
    downNode rest base2)
  {u : MachineState}
  (k : AtConnect c e t u base base2 child (widthOf family)
    (min cidr (AllowedipsRelation.common (widthOf family) downNode.bits key)) key (chosen family key cidr downNode))
include x k

theorem parent_exit (premises : Premises fetch L A) {w' : World} {answer : Int} {exact : Bool} {st : Step}
    (inv : Inv L A w s.data.dmem)
    (facts : StepFacts w family key cidr pid answer w' d stream (some p) exact st)
    (case : st.case = .split)
    (dropped : stream.drop st.consumed = rest) (zero : answer = 0)
    (found : below (bump d) (rootOf d family) key (some p) = some downId) :
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
  have belowNext : ∀ pair ∈ d.nodes.toList, pair.1 < d.nextNode :=
    target_nodes_below (d := bump d) related
  obtain ⟨downId',downNode',pnode,rest',found',hasDown',pf,_⟩ :=
    split_step_parent case walked hasPeer belowNext
  have sameId : downId' = downId := Option.some.inj (found'.symm.trans found)
  rw [sameId] at hasDown' pf
  have sameNode : downNode' = downNode := Option.some.inj (hasDown'.symm.trans x.hasDown)
  rw [sameNode] at pf
  -- the parent
  have parentNamed : (p,e.data.regs.rbx.toNat) ∈ names.trie.nodes := by
    have at0 := x.cut.placedAt
    unfold Trie.address at at0
    simp only [] at at0
    cases located : names.trie.nodes.find? (·.1 == p) with
    | none => rw [located] at at0; cases at0
    | some pair =>
      rw [located] at at0
      have member := List.mem_of_find?_eq_some located
      have matched : (pair.1 == p)=true := List.find?_some (p := fun y : Nat × Nat => y.1 == p) located
      have same : pair.1=p := eq_of_beq matched
      have address : pair.2=e.data.regs.rbx.toNat := Except.ok.inj at0
      rw [←same,←address]
      exact member
  generalize parentAt : e.data.regs.rbx.toNat = parentBase at parentNamed
  have parentLive : parentBase ∈ liveOf names base := nodeLive parentNamed
  have parentBound := x.liveBound parentLive
  have parentPositive := ((Trie.reconstruct_fields related.trie).nodeRange _ _ parentNamed).1
  have rbxbv : u.data.regs.rbx.toBitVec = .ofNat 64 parentBase := by
    rw [k.rbx,←parentAt]; exact (ofNat_uint64 _).symm
  have parentChild := old_nodes_apart related parentNamed x.named (Ne.symm pf.different)
  have parentSecond := x.freshApart parentLive
  have parentFirst := x.firstApart parentNamed
  have childSecond := x.freshApart (nodeLive (base := base) x.named)
  have childFirst := x.firstApart x.named
  have baseSecond := x.freshApart baseLive
  have childBound := x.childBound
  have baseBound := x.baseBound
  have pw : pnode.bitlen = widthOf family := pf.sameWidth.symm
  have short : pnode.cidr < pnode.bitlen := by
    have := pf.measure
    have := x.proper
    omega
  have pd := x.oldU k parentNamed pf.hasParent
  have pfields := Trie.decodeNode_fields pd
  have parentInside : byteSelector pnode.bitlen pnode.cidr < widthOf family / 8 := by
    have inside := (selector_position pnode.bitlen pnode.cidr pfields.family short).2
    have same : pnode.bitlen / 8 = widthOf family / 8 := by rw [pw]
    omega
  have bytes := x.wideBytes
  have indexWord := word_loadInt _ _ _ _ _ pfields.byteSelector
  have shiftWord := word_loadInt _ _ _ _ _ pfields.bitSelector
  rw [BitVec.ofNat_add] at indexWord shiftWord
  obtain ⟨_,_,lp,rp,_,leftWord,_,rightWord,_⟩ := pfields.children
  have leftLoad := word_loadInt _ _ _ _ _ leftWord
  have rightLoad := word_loadInt _ _ _ _ _ rightWord
  rw [BitVec.ofNat_add] at leftLoad
  have rightAddress : BitVec.ofNat 64 (parentBase+nodeOffsets.children+8) = BitVec.ofNat 64 parentBase + 16 := by
    rw [Nat.add_assoc,BitVec.ofNat_add]; rfl
  rw [rightAddress] at rightLoad
  have nodeWords := key_words (k.record names)
  have nodeByte := queryByte_read _ _ _ _ _ x.wide parentInside nodeWords
  rw [BitVec.ofNat_add] at nodeByte
  have nodeParent : (u.data.dmem.loadInt (BitVec.ofNat 64 base2 + 48) 8).isSome = true := by
    apply k.mapped
    have part := MemoryBytes.loadInt_subword _ _ _ _ (Trie.readNat_loadInt x.grown.zero) 48 8 (by decide)
    exact Option.isSome_of_eq_some part
  have entry := x.entryU k rfl
  have selBound := entry.directionBound
  -- positions of the ranges the connections touch
  have conn {b2 : Nat} (two : b2 < 2) {y : BitVec 64}
      (written : SplitStage3.Writes u.data.regs.r12.toBitVec u.data.regs.rdi.toBitVec u.data.regs.r8.toBitVec
        (chosen family key cidr downNode) b2 y) := x.connNat k selBound two written
  have nodeTop {y : BitVec 64} (inside : InRange (u.data.regs.r12.toBitVec + 48) 8 y) :
      base2 + 48 ≤ y.toNat ∧ y.toNat < base2 + 56 := by
    rw [r12bv k] at inside
    exact natRange (off := 48) (Nat.le_of_lt top) (by decide) inside
  have slotP {b : Nat} (small : b < 2) {y : BitVec 64} (inside : InRange (slot u.data.regs.rbx.toBitVec b) 8 y) :
      parentBase + 8 ≤ y.toNat ∧ y.toNat < parentBase + 24 := by
    rw [rbxbv] at inside
    have := natRange (off := 8+8*b) parentBound (by omega) inside
    omega
  have keptParent {y : BitVec 64} (low : parentBase ≤ y.toNat) (high : y.toNat < parentBase + 72) :
      Kept (liveOf names base ++ [base2]) y :=
    ⟨parentBase,List.mem_append_left _ parentLive,inObject low high⟩
  have selected2 (byte shift : Nat) : selected byte shift < 2 := by unfold selected; omega
  have run := eventually_flight (C1Split.split_parent_from_step fetch premises.insertion premises.tracePc c u.data
    (chosen family key cidr downNode) _ _ _ (byteSelector pnode.bitlen pnode.cidr) (7-pnode.cidr%8)
    (queryByte (widthOf family) key (byteSelector pnode.bitlen pnode.cidr))
    (machine := e) (memory := u.data.dmem) (d := bump d) (d0 := d) (family := family) (downId := downId)
    (downBase := child) (parentId := p) (parentBase := parentBase) (base := base) (base2 := base2) owner
    (entry := entry)
    (parent := by
      intro zero
      have := congrArg UInt64.toNat (k.rbx.symm.trans zero)
      rw [parentAt] at this
      have : parentBase = 0 := this
      omega)
    (ready := k.ready)
    (contextApart := fun y read written =>
      (x.heapFar (x.keptHeap (x.keptOf (by have := conn (selected2 _ _) written; omega)))).2.1 read)
    (contextApart3 := by
      rintro y read (node|slotWord)
      · have := nodeTop node
        exact (x.heapFar (x.keptHeap (x.keptOf (by omega)))).2.1 read
      · have := slotP (selected2 _ _) slotWord
        exact (x.heapFar (x.keptHeap (keptParent (by omega) (by omega)))).2.1 read)
    (indexRead := by rw [rbxbv]; exact indexWord)
    (shiftRead := by rw [rbxbv]; exact shiftWord)
    (byteRead := by rw [r12bv k]; exact nodeByte)
    (indexBound := by omega) (shiftBound := by omega) (byteBound := queryByte_bound _ _ _)
    (nodeParentMapped := by rw [r12bv k]; exact nodeParent)
    (parentLeft := by rw [rbxbv]; exact Option.isSome_of_eq_some leftLoad)
    (parentRight := by rw [rbxbv]; exact Option.isSome_of_eq_some rightLoad)
    (readsApart := by
      intro y read
      have bounds : (parentBase + 25 ≤ y.toNat ∧ y.toNat < parentBase + 27) ∨
          (base2 + 32 ≤ y.toNat ∧ y.toNat < base2 + 48) := by
        rcases read with index|shift|byte
        · rw [rbxbv] at index
          have := natRange (off := 25) parentBound (by decide) index
          omega
        · rw [rbxbv] at shift
          have := natRange (off := 26) parentBound (by decide) shift
          omega
        · rw [r12bv k] at byte
          have := natRange2 (o1 := 32) (Nat.le_of_lt top) (by omega) byte
          omega
      constructor
      · intro written
        have := conn (selected2 _ _) written
        omega
      · apply x.callFar k
        rcases bounds with parent|node
        · exact x.keptHeap (keptParent (by omega) (by omega))
        · exact x.keptHeap (x.keptOf (by omega)))
    (wordsApart := by
      intro y words
      apply x.callFar k
      rcases words with node|left|right
      · have := nodeTop node
        exact x.keptHeap (x.keptOf (by omega))
      · rw [rbxbv] at left
        have := natRange (off := 8) parentBound (by decide) left
        exact x.keptHeap (keptParent (by omega) (by omega))
      · rw [rbxbv] at right
        have := natRange (off := 16) parentBound (by decide) right
        exact x.keptHeap (keptParent (by omega) (by omega)))
    (node := r12bv k) (down := rdibv k) (leaf := r8bv k) (par := rbxbv)
    (readApart := fun span member y inside => x.callFar k (x.readHeap2 span member y inside))
    (metadataApart := fun span member y inside =>
      x.callFar k (x.readHeap2 span (Placement.metadata_read member) y inside))
    (related := related) (checked := heapOk) (pending := x.pendingU k) (valid2 := x.valid2) (init := x.init k)
    (downNamed := x.named) (parentNamed := parentNamed) (hasPeer := hasPeer)
    (cut := rfl) (width := x.extra.width) (case := case) (walked := walked) (found := found)
    (downFacts := x.downFacts))
  apply Rollback.start_at k.pc
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro v ⟨⟨pc,rbx,rsp,_,_,_,_,_,relatedV,shapeV,readyV,frameV,_,_⟩,mappedV,flagV⟩
  refine x.finish k premises inv facts dropped zero seq _ pc rbx rsp relatedV shapeV readyV frameV ?_ mappedV flagV
  rintro y (written|call|node|slotWord)
  · have := conn (selected2 _ _) written
    exact .inl (.inl (x.keptOf (by omega)))
  · exact .inr call
  · have := nodeTop node
    exact .inl (.inl (x.keptOf (by omega)))
  · have := slotP (selected2 _ _) slotWord
    exact .inl (.inl (keptParent (by omega) (by omega)))

end SplitCtx

#print axioms SplitCtx.parent_exit
end Binary.Statements.C1.Proof
