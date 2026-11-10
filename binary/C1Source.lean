import C1Interfaces
import PairAllowedipsHeapFrame
import PairAllowedipsFrame
import PairAllowedipsAssert
import PairCountUpdate
import PairLocalsProof
import AllowedipsValidateConstruct
import PairRequire
import AllowedipsSourceRun
import Init.Internal.Order.While

/-! Result C1, work package 1: the source side and the invariant's algebra. This module is the package's root in
`binary/lakefile.toml`. The brief is `binary/Statements/C1/proof/WP1.md`.

The package is this one file: the library lists its roots one by one, so a
module `C1SourceX` beside it is not a library module, and the lake file is
not the package's to edit. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1

/-- A sub-range of an object lies in any range that contains the object. -/
theorem inRange_widen {b a off size total : Nat} (lo : b ≤ a) (fits : a+off+size ≤ b+total)
    {x : BitVec 64} (inside : InRange (.ofNat 64 (a+off)) size x) :
    InRange (.ofNat 64 b) total x := by
  obtain ⟨i,hi,rfl⟩ := inside
  refine ⟨a-b+off+i,by omega,?_⟩
  rw [← BitVec.ofNat_add,← BitVec.ofNat_add]
  congr 1
  omega

theorem nodeFields_within : ∀ field ∈ nodeFields Root.nodeOffsets, field.1+field.2 ≤ nodeSize := by
  decide

/-- Every byte reconstruction reads is a heap byte. -/
theorem readSpans_heap {L : Layout} {names : Allowedips.Names}
    (table : names.table = L.table) (peers : names.trie.peers = L.peers)
    (arena : ∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2) :
    ∀ span ∈ readSpans names Root.nodeOffsets, ∀ a, span.contains a → L.Heap a := by
  intro span member a inside
  unfold readSpans at member
  rw [table,peers] at member
  rcases List.mem_append.mp member with tablePart | rest
  · exact ⟨span,List.mem_append_left _ (List.mem_append_left _ tablePart),inside⟩
  rcases List.mem_append.mp rest with nodePart | peerPart
  · obtain ⟨⟨id,base⟩,named,field⟩ := List.mem_flatMap.mp nodePart
    obtain ⟨⟨offset,size⟩,listed,rfl⟩ := List.mem_map.mp field
    obtain ⟨object,inArena,low,high⟩ := arena (id,base) named
    have bound := nodeFields_within (offset,size) listed
    refine ⟨object,List.mem_append_right _ inArena,?_⟩
    exact inRange_widen (total := object.2) low (by simp only at bound low high ⊢; omega) inside
  · exact ⟨span,List.mem_append_left _ (List.mem_append_right _ peerPart),inside⟩

theorem metadataSpans_subset (names : Allowedips.Names) (o : AllowedipsProbe.Offsets) :
    ∀ span ∈ metadataSpans names o, span ∈ readSpans names o := by
  intro span member
  unfold metadataSpans at member
  unfold readSpans
  rcases List.mem_append.mp member with tablePart | rest
  · exact List.mem_append_left _ tablePart
  rcases List.mem_append.mp rest with nodePart | peerPart
  · exact List.mem_append_right _ (List.mem_append_left _ nodePart)
  · obtain ⟨⟨id,base⟩,named,field⟩ := List.mem_flatMap.mp peerPart
    obtain ⟨⟨offset,size⟩,listed,rfl⟩ := List.mem_map.mp field
    refine List.mem_append_right _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨(id,base),named,List.mem_map.mpr ⟨(offset,size),?_,rfl⟩⟩))
    simp only [listFields,peerFields,List.mem_cons,List.not_mem_nil,or_false] at listed ⊢
    exact Or.inr listed

/-- The relation's decidable part and `Idle` across a change outside the heap. -/
theorem related_frame {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator}
    (contract : AllocatorContract fetch L A) {w : World} {m m' : Mem 64}
    (related : Related L A w m) (same : ∀ a, L.Heap a → m.get? a = m'.get? a) :
    Related L A w m' := by
  obtain ⟨names,stream,table,peers,asserted,armed,hidden,sites,apart,arena,idle⟩ := related
  have outside : EqualOutside (fun a => ¬L.Heap a) m m' := by
    intro a notWritten
    exact same a (Classical.not_not.mp notWritten)
  have reads : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ a, span.contains a → ¬¬L.Heap a :=
    fun span member a inside => not_not_intro (readSpans_heap table peers arena span member a inside)
  obtain ⟨d,device,corresponds,shape⟩ := assertAt_ok asserted
  have corresponds' : Allowedips.Corresponds names Root.nodeOffsets m' d := by
    unfold Allowedips.Corresponds at corresponds ⊢
    rw [← reconstruct_frame names Root.nodeOffsets outside reads]
    exact corresponds
  have shape' : heap names (target d) m' = .ok () := by
    rw [← heap_frame names Root.nodeOffsets (target d) outside
      (fun span member => reads span (metadataSpans_subset names _ span member))]
    exact shape
  refine ⟨names,stream,table,peers,assertAt_of_related device corresponds' shape',armed,hidden,sites,
    apart,arena,contract.frame m m' _ _ idle ?_⟩
  intro a inArena _
  obtain ⟨span,member,inside⟩ := inArena
  exact same a ⟨span,List.mem_append_right _ member,inside⟩

theorem framedHolds : FramedHolds := by
  intro fetch L A premises w m m' related same
  exact related_frame premises.allocator related same

#print axioms framedHolds

/-! ## `Initial` for `Inv`: the empty interpretation at a physically empty table -/

/-- What `emptyTable` checks, as propositions. -/
structure EmptyFacts (L : Layout) (m : Mem 64) (d : Device) : Prop where
  tablePositive : 0 < L.table
  tableAligned : L.table % 8 = 0
  root4 : readNat ⟨{dmem := m},0⟩ (L.table+AllowedipsMutationLayout.root4) 8 = .ok 0
  root6 : readNat ⟨{dmem := m},0⟩ (L.table+AllowedipsMutationLayout.root6) 8 = .ok 0
  seq : readNat ⟨{dmem := m},0⟩ (L.table+AllowedipsMutationLayout.seq) 8 = .ok d.peerAllowedips.seq.toNat
  mirror4 : d.peerAllowedips.root4 = none
  mirror6 : d.peerAllowedips.root6 = none
  nodes : d.nodes.toList = []
  identities : L.peers.map (·.1) = d.peers.toList.map (·.1)
  peers : ∀ x ∈ L.peers, ∃ p, d.peers.get? x.1 = some p ∧ 0 < x.2 ∧ x.2 % 8 = 0 ∧
    p.allowedipsList = [] ∧
    readNat ⟨{dmem := m},0⟩ (x.2+AllowedipsMutationLayout.allowedips_list) 8 =
      .ok (x.2+AllowedipsMutationLayout.allowedips_list) ∧
    readNat ⟨{dmem := m},0⟩ (x.2+AllowedipsMutationLayout.allowedips_list+8) 8 =
      .ok (x.2+AllowedipsMutationLayout.allowedips_list) ∧
    readNat ⟨{dmem := m},0⟩ (x.2+Root.nodeOffsets.peerRefcount) 4 = .ok p.refcount
  bounded : ∀ span ∈ objectsOf L, span.1+span.2 < 2^64
  apart : (objectsOf L).Pairwise (fun a b => disjointRanges a.1 a.2 b.1 b.2 = true)
  arena : spansApart (objectsOf L) L.arena = true

/-- The indexed check of `emptyTable` and `Trie.validate`, as a bound on every
element and a pairwise property. -/
theorem pairwise_of_zipIdx_all {α : Type} {xs : List α} {p : α → Bool} {q : α → α → Bool}
    (all : (xs.zipIdx.all fun x => p x.1 && (xs.drop (x.2+1)).all (q x.1)) = true) :
    (∀ x ∈ xs, p x = true) ∧ xs.Pairwise (fun a b => q a b = true) := by
  rw [List.all_eq_true] at all
  have at_ (i : Nat) (small : i < xs.length) :=
    Bool.and_eq_true_iff.mp (all (xs[i],i)
      (List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem small)))
  constructor
  · intro x member
    obtain ⟨i,small,rfl⟩ := List.getElem_of_mem member
    exact (at_ i small).1
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj lt
    have rest := List.all_eq_true.mp (at_ i hi).2
    exact rest xs[j] (List.mem_drop_iff_getElem.mpr ⟨j-(i+1),by omega,by congr 1; omega⟩)

theorem emptyTable_facts {L : Layout} {m : Mem 64} {d : Device}
    (ok : emptyTable L m d = .ok ()) : EmptyFacts L m d := by
  unfold emptyTable at ok
  dsimp only at ok
  obtain ⟨tableAddress,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨r4,root4,ok⟩ := bind_ok ok
  obtain ⟨r6,root6,ok⟩ := bind_ok ok
  obtain ⟨roots,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨sq,seq,ok⟩ := bind_ok ok
  obtain ⟨seqEq,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨mirror,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨identities,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨_,loop,ok⟩ := bind_ok ok
  obtain ⟨overlap,ok⟩ := require_bind_ok _ _ _ _ ok
  have arena := require_ok ok
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at tableAddress roots seqEq mirror identities
  obtain ⟨rfl,rfl⟩ := roots
  subst seqEq
  have shape := pairwise_of_zipIdx_all (p := fun x : Pair.Span => decide (x.1+x.2 < 2^64))
    (q := fun a b => disjointRanges a.1 a.2 b.1 b.2) overlap
  refine ⟨tableAddress.1,tableAddress.2,root4,root6,seq,by simpa using mirror.1.1,by simpa using mirror.1.2,
    List.isEmpty_iff.mp (by rw [Std.TreeMap.isEmpty_toList]; exact mirror.2),identities,?_,fun span member => by simpa using shape.1 span member,shape.2,arena⟩
  refine forIn_ok (P := fun x : PeerId × Nat => ∃ p, d.peers.get? x.1 = some p ∧ 0 < x.2 ∧ x.2 % 8 = 0 ∧
    p.allowedipsList = [] ∧
    readNat ⟨{dmem := m},0⟩ (x.2+AllowedipsMutationLayout.allowedips_list) 8 =
      .ok (x.2+AllowedipsMutationLayout.allowedips_list) ∧
    readNat ⟨{dmem := m},0⟩ (x.2+AllowedipsMutationLayout.allowedips_list+8) 8 =
      .ok (x.2+AllowedipsMutationLayout.allowedips_list) ∧
    readNat ⟨{dmem := m},0⟩ (x.2+Root.nodeOffsets.peerRefcount) 4 = .ok p.refcount) ?_ loop
  intro x _ before after run
  split at run
  · rename_i p present
    obtain ⟨address,run⟩ := require_bind_ok _ _ _ _ run
    obtain ⟨first,head,run⟩ := bind_ok run
    obtain ⟨second,back,run⟩ := bind_ok run
    obtain ⟨links,run⟩ := require_bind_ok _ _ _ _ run
    obtain ⟨count,refcount,run⟩ := bind_ok run
    have counted : (count == p.refcount) = true := by
      cases condition : count == p.refcount
      · rw [condition] at run
        cases run
      · rfl
    rw [counted] at run
    have yielded : Except.ok (ForInStep.yield PUnit.unit) = Except.ok after := run
    simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.isEmpty_iff] at address links counted
    obtain ⟨rfl,rfl⟩ := links
    subst counted
    exact ⟨PUnit.unit,(Except.ok.inj yielded).symm,p,present,address.1.1,address.1.2,address.2,head,back,refcount⟩
  · cases run

theorem initial_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem empty_decodePeer (names : Allowedips.Names) (empty : names.trie.nodes = [])
    {m : Mem 64} {id a count : Nat} (bound : a+Layouts.peerSize < 2^64)
    (head : readNat ⟨{dmem := m},0⟩ (a+AllowedipsMutationLayout.allowedips_list) 8 =
      .ok (a+AllowedipsMutationLayout.allowedips_list))
    (back : readNat ⟨{dmem := m},0⟩ (a+AllowedipsMutationLayout.allowedips_list+8) 8 =
      .ok (a+AllowedipsMutationLayout.allowedips_list))
    (counted : readNat ⟨{dmem := m},0⟩ (a+Root.nodeOffsets.peerRefcount) 4 = .ok count) :
    decodePeer names Root.nodeOffsets m id a = .ok (id,count,[]) := by
  have size : Layouts.peerSize = 1520 := rfl
  have list : AllowedipsMutationLayout.allowedips_list = 1096 := rfl
  have offset : Root.nodeOffsets.peerRefcount = 1056 := rfl
  have w1 : word m "peer.refcount" (a+Root.nodeOffsets.peerRefcount) 4 = .ok count :=
    Trie.word_of_loadInt "peer.refcount" (by omega) (Trie.readNat_loadInt counted)
  have w2 : word m "peer.list.head" (a+AllowedipsMutationLayout.allowedips_list) 8 =
      .ok (a+AllowedipsMutationLayout.allowedips_list) :=
    Trie.word_of_loadInt "peer.list.head" (by omega) (Trie.readNat_loadInt head)
  have w3 : word m "peer.list.prev" (a+AllowedipsMutationLayout.allowedips_list+8) 8 =
      .ok (a+AllowedipsMutationLayout.allowedips_list) :=
    Trie.word_of_loadInt "peer.list.prev" (by omega) (Trie.readNat_loadInt back)
  have list : peerList names m (a+AllowedipsMutationLayout.allowedips_list) 1
      (a+AllowedipsMutationLayout.allowedips_list) (a+AllowedipsMutationLayout.allowedips_list) [] = .ok [] := by
    simp only [peerList,empty,List.any_nil,Bool.or_false,beq_self_eq_true,Bool.not_true,
      Bool.false_eq_true,↓reduceIte,w3,initial_ok_bind]
    rfl
  unfold decodePeer
  simp only [w1,w2,empty,List.length_nil,Nat.zero_add,initial_ok_bind,list]
  rfl

/-- A traversal over two lists with the same keys. -/
theorem mapM_keys {ε β γ δ : Type} {f : Nat × γ → Except ε β} {g : Nat × δ → β}
    (xs : List (Nat × γ)) (ys : List (Nat × δ)) (keys : xs.map (·.1) = ys.map (·.1))
    (each : ∀ x ∈ xs, ∀ y ∈ ys, x.1 = y.1 → f x = .ok (g y)) : xs.mapM f = .ok (ys.map g) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => cases keys
  | cons x xs ih =>
    cases ys with
    | nil => cases keys
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at keys
      rw [List.mapM_cons,each x (by simp) y (by simp) keys.1,
        ih ys keys.2 (fun a ha b hb => each a (by simp [ha]) b (by simp [hb]))]
      rfl

theorem initial_bind_of {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {a : α} {v : β}
    (first : x = .ok a) (rest : f a = .ok v) : (x >>= f) = .ok v := by
  rw [first]
  exact rest

/-- The interpretation check for no nodes and the layout's peers. -/
theorem empty_validate {L : Layout} {m : Mem 64} {d : Device} (facts : EmptyFacts L m d)
    (nextNode : Nat) :
    Allowedips.validate ⟨L.table,⟨[],L.peers⟩,nextNode⟩ Root.nodeOffsets = .ok () := by
  have objects : objectsOf L = (L.table,AllowedipsMutationLayout.tableSize) ::
      L.peers.map (fun p => (p.2,Layouts.peerSize)) := rfl
  have apart := facts.apart
  rw [objects,List.pairwise_cons] at apart
  have bounded := facts.bounded
  rw [objects] at bounded
  have peerBound : ∀ x ∈ L.peers, x.2+Layouts.peerSize < 2^64 := fun x member =>
    bounded (x.2,Layouts.peerSize) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨x,member,rfl⟩))
  have newTrie : Trie.validate ⟨[],L.peers⟩ Root.nodeOffsets = .ok () := by
    apply trie_validate_construct (by decide)
    · intro pairs member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl
      · exact ⟨List.nodup_nil,List.nodup_nil⟩
      · constructor
        · rw [show L.peers.map Prod.fst = d.peers.keys from
            facts.identities.trans Std.TreeMap.map_fst_toList_eq_keys]
          exact Std.TreeMap.nodup_keys
        · have separate := apart.2
          rw [List.pairwise_map] at separate
          rw [List.Nodup,List.pairwise_map]
          refine separate.imp ?_
          intro a b separated equal
          have size : Layouts.peerSize = 1520 := rfl
          simp only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq,equal] at separated
          omega
    · intro span member
      simp only [List.map_nil,List.nil_append] at member
      obtain ⟨x,present,rfl⟩ := List.mem_map.mp member
      obtain ⟨p,_,positive,_⟩ := facts.peers x present
      exact ⟨positive,peerBound x present⟩
    · simpa only [List.map_nil,List.nil_append] using apart.2
  have tableBound := bounded (L.table,AllowedipsMutationLayout.tableSize) (List.mem_cons_self ..)
  have tableCheck : (decide (0 < L.table) && L.table % 8 == 0 &&
      decide (L.table+AllowedipsMutationLayout.tableSize < 2^64)) = true := by
    simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
    exact ⟨⟨facts.tablePositive,facts.tableAligned⟩,tableBound⟩
  unfold Allowedips.validate
  dsimp only
  rw [newTrie]
  refine initial_bind_of rfl ?_
  rw [ite_eq_left tableCheck]
  refine initial_bind_of (a := PUnit.unit) rfl ?_
  refine initial_bind_of (a := PUnit.unit) rfl ?_
  refine initial_bind_of (a := PUnit.unit) (forIn_yield ?_) rfl
  intro span member
  simp only [List.map_nil,List.nil_append] at member
  have separated := apart.1 span member
  have flipped : disjointRanges span.1 span.2 L.table AllowedipsMutationLayout.tableSize = true := by
    simp only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq] at separated ⊢
    omega
  rw [ite_eq_left flipped]
  rfl

/-- Reconstruction at a physically empty table gives the mirror's device. -/
theorem empty_reconstruct {L : Layout} {m : Mem 64} {d : Device} (facts : EmptyFacts L m d) :
    reconstruct ⟨L.table,⟨[],L.peers⟩,d.nextNode⟩ Root.nodeOffsets m = .ok (target d) := by
  have objects : objectsOf L = (L.table,AllowedipsMutationLayout.tableSize) ::
      L.peers.map (fun p => (p.2,Layouts.peerSize)) := rfl
  have bounded := facts.bounded
  rw [objects] at bounded
  have tableBound := bounded (L.table,AllowedipsMutationLayout.tableSize) (List.mem_cons_self ..)
  have size : AllowedipsMutationLayout.tableSize = 24 := rfl
  have o4 : AllowedipsMutationLayout.root4 = 0 := rfl
  have o6 : AllowedipsMutationLayout.root6 = 8 := rfl
  have os : AllowedipsMutationLayout.seq = 16 := rfl
  simp only at tableBound
  have w4 : word m "table.root4" (L.table+AllowedipsMutationLayout.root4) 8 = .ok 0 :=
    Trie.word_of_loadInt _ (by omega) (Trie.readNat_loadInt facts.root4)
  have w6 : word m "table.root6" (L.table+AllowedipsMutationLayout.root6) 8 = .ok 0 :=
    Trie.word_of_loadInt _ (by omega) (Trie.readNat_loadInt facts.root6)
  have ws : word m "table.seq" (L.table+AllowedipsMutationLayout.seq) 8 = .ok d.peerAllowedips.seq.toNat :=
    Trie.word_of_loadInt _ (by omega) (Trie.readNat_loadInt facts.seq)
  have peersRun : L.peers.mapM (fun (x : PeerId × Nat) =>
      decodePeer ⟨L.table,⟨[],L.peers⟩,d.nextNode⟩ Root.nodeOffsets m x.1 x.2) =
      .ok (d.peers.toList.map fun (y : PeerId × Peer) => (y.1,y.2.refcount,y.2.allowedipsList)) := by
    apply mapM_keys _ _ facts.identities
    rintro ⟨id,a⟩ present ⟨id',p⟩ listed same
    obtain rfl : id = id' := same
    obtain ⟨q,found,_,_,emptyList,head,back,counted⟩ := facts.peers (id,a) present
    have stored : d.peers.get? id = some p := by
      rw [Std.TreeMap.get?_eq_getElem?]
      exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp listed
    obtain rfl : q = p := Option.some.inj (found.symm.trans stored)
    have peerBound := bounded (a,Layouts.peerSize) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(id,a),present,rfl⟩))
    simp only [emptyList]
    exact empty_decodePeer _ rfl peerBound head back counted
  have table : d.peerAllowedips = ⟨none,none,d.peerAllowedips.seq⟩ := by
    have m4 := facts.mirror4
    have m6 := facts.mirror6
    cases stored : d.peerAllowedips
    rw [stored] at m4 m6
    simp only at m4 m6
    simp only [m4,m6]
  unfold Allowedips.reconstruct
  rw [empty_validate facts]
  refine initial_bind_of rfl ?_
  refine initial_bind_of w4 ?_
  refine initial_bind_of (a := none) rfl ?_
  refine initial_bind_of w6 ?_
  refine initial_bind_of (a := none) rfl ?_
  refine initial_bind_of ws ?_
  refine initial_bind_of (a := []) rfl ?_
  refine initial_bind_of peersRun ?_
  unfold Allowedips.target
  rw [facts.nodes]
  conv => rhs; rw [table]
  simp
  rfl

theorem empty_heap {L : Layout} {m : Mem 64} {d : Device} (facts : EmptyFacts L m d) :
    heap ⟨L.table,⟨[],L.peers⟩,d.nextNode⟩ (target d) m = .ok () := by
  unfold heap Allowedips.target
  simp only [facts.nodes,facts.mirror4,facts.mirror6]
  rfl

theorem initialHolds : InitialHolds := by
  intro fetch L A premises w d m stream device armed hidden sites empty idle
  have facts := emptyTable_facts empty
  let names : Allowedips.Names := ⟨L.table,⟨[],L.peers⟩,d.nextNode⟩
  refine ⟨names,stream,rfl,rfl,?_,armed,hidden,sites,facts.arena,?_,idle⟩
  · exact assertAt_of_related device (empty_reconstruct facts) (empty_heap facts)
  · intro node member
    cases member

#print axioms initialHolds

/-! ## The mirror's allocation records and primitives, for `RunIsStep` -/

/-- Copy of the mirror's private `AmbientM.allocRecord` (Leanux/Kernel/Defs.lean), text unchanged. -/
def allocRecordCopy (s : AllocSite) : AmbientM Bool := do
  let bs ← AmbientM.hidden (.alloc s)
  match bs.headD 2 with
  | 1 => return true
  | 0 => return false
  | b => throw (.hidden s!"{s.info.label}: outcome byte {b}, expected 0 or 1")

/-- Copy of the mirror's `AmbientM.hiddenAlloc`, text unchanged, with the placeholder encounter a parameter. -/
def hiddenAllocCopy (allocPlaceholder : AllocSite → AmbientM Bool) (s : AllocSite) : AmbientM Bool := do
  let i := s.info
  match i.count with
  | .laxZero => return true
  | .unrecorded => return true
  | .cut => AmbientM.invariant s!"{i.label} is a below-cut consumer, consumed only at a cut point"
  | .exact n =>
    let w ← get
    let placeholders := w.hidden.isNone && w.hiddenPlaceholders
    if !placeholders && !w.allocArmed.contains i.label then return true
    let encounter : AmbientM Bool := if placeholders then allocPlaceholder s else allocRecordCopy s
    let mut k := 0
    while k < n do
      if !(← encounter) then return false
      k := k + 1
    return true

theorem hiddenAlloc_copy : ∃ P, ∀ s, AmbientM.hiddenAlloc s = hiddenAllocCopy P s := ⟨_,fun _ => rfl⟩

theorem passive_sites : HiddenSite.passive 77 = false ∧ HiddenSite.passive 78 = false ∧ HiddenSite.passive 79 = false := by
  decide


theorem loop_unfold {β : Type} (st : β) (f : Unit → β → AmbientM (ForInStep β)) :
    forIn Lean.Loop.mk st f = (do
      match ← f () st with
      | .done v => pure v
      | .yield v => forIn Lean.Loop.mk v f) :=
  Lean.Loop.forIn_eq_of_monadTail

theorem loop_once (encounter : AmbientM Bool) :
    (do
      let mut k := 0
      while k < 1 do
        if !(← encounter) then return false
        k := k + 1
      return true : AmbientM Bool) = encounter := by
  dsimp only
  rw [loop_unfold]
  simp only [Nat.zero_lt_one, ↓reduceIte, bind_assoc]
  conv => rhs; rw [← bind_pure encounter]
  apply bind_congr
  intro b
  cases b
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
    rw [loop_unfold]
    simp


theorem hiddenAllocCopy_once (P : AllocSite → AmbientM Bool) (s : AllocSite)
    (count : s.info.count = .exact 1) :
    hiddenAllocCopy P s = (do
      let w ← get
      let placeholders := w.hidden.isNone && w.hiddenPlaceholders
      if !placeholders && !w.allocArmed.contains s.info.label then return true
      (if placeholders then P s else allocRecordCopy s)) := by
  unfold hiddenAllocCopy
  simp only [count]
  apply bind_congr
  intro w
  split
  · rfl
  · exact loop_once _


theorem alloc_site_facts {s : AllocSite} (site : s = .allocNode190 ∨ s = .allocNode205 ∨ s = .allocNode234) :
    s.info.count = .exact 1 ∧ (HiddenSite.alloc s).info.len = 40 ∧ (HiddenSite.alloc s).info.id = s.hiddenId ∧
    (s.hiddenId == (HiddenSite.sectionStart .netRx).info.id) = false := by
  rcases site with rfl | rfl | rfl <;> exact ⟨rfl,rfl,rfl,by decide⟩

theorem hidden_alloc_accepted {s : AllocSite} {a a' : Ambient} {bs : List UInt8} {r : HiddenRecord} {rest : List HiddenRecord}
    (site : s = .allocNode190 ∨ s = .allocNode205 ∨ s = .allocNode234)
    (hid : a.hidden = some (r :: rest)) (clean : HiddenSite.passive r.site = false)
    (run : (AmbientM.hidden (.alloc s)).run a = .ok (bs,a')) :
    r.site = s.hiddenId ∧ r.bytes.length = 40 ∧ bs = r.bytes.take 40 ∧ a' = {a with hidden := some rest} := by
  obtain ⟨count,len,ident,notRx⟩ := alloc_site_facts site
  simp only [AmbientM.hidden,AmbientM.skipAmbient,AmbientM.noteNetRxStart,StateT.run_bind,StateT.run_get,
    StateT.run_set,hid,len,ident,notRx,clean,List.dropWhile,
    Source.except_ok_bind,Source.except_pure,pure_bind,Bool.false_eq_true,↓reduceIte] at run
  split at run
  · cases run
  · rename_i sameSite
    split at run
    · cases run
    · rename_i wellFormed
      cases run
      refine ⟨by simpa using sameSite,?_,rfl,rfl⟩
      simp only [Bool.or_eq_true,bne_iff_ne,ne_eq,not_or,Decidable.not_not] at wellFormed
      omega

theorem hiddenAlloc_accepted {s : AllocSite} {a a' : Ambient} {b : Bool} {r : HiddenRecord} {rest : List HiddenRecord}
    (site : s = .allocNode190 ∨ s = .allocNode205 ∨ s = .allocNode234)
    (hid : a.hidden = some (r :: rest)) (arm : a.allocArmed.contains s.info.label = true)
    (clean : HiddenSite.passive r.site = false)
    (run : (AmbientM.hiddenAlloc s).run a = .ok (b,a')) :
    r.site = s.hiddenId ∧ (r.bytes.head? = some 0 ∨ r.bytes.head? = some 1) ∧
      b = (r.bytes.head? == some 1) ∧ a' = {a with hidden := some rest} := by
  obtain ⟨P,copy⟩ := hiddenAlloc_copy
  obtain ⟨count,len,ident,notRx⟩ := alloc_site_facts site
  rw [copy,hiddenAllocCopy_once P s count] at run
  simp only [StateT.run_bind,StateT.run_get,hid,arm,Option.isNone_some,Bool.false_and,Bool.not_false,
    Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte,Source.except_ok_bind,Source.except_pure,
    allocRecordCopy] at run
  cases consumed : (AmbientM.hidden (.alloc s)).run a with
  | error e => rw [consumed] at run; cases run
  | ok out =>
    obtain ⟨bs,a1⟩ := out
    obtain ⟨sameSite,length,rfl,rfl⟩ := hidden_alloc_accepted site hid clean consumed
    rw [consumed] at run
    cases bytes : r.bytes with
    | nil => rw [bytes] at length; cases length
    | cons x xs =>
      simp only [Source.except_ok_bind,bytes,List.take_succ_cons,List.headD_cons] at run
      split at run
      · cases run
        exact ⟨sameSite,.inr rfl,rfl,rfl⟩
      · cases run
        exact ⟨sameSite,.inl rfl,rfl,rfl⟩
      · cases run


/-! ## Accepted runs of the mirror's primitives, as the pure functions of `C1Step` -/

/-- Adapted from the T4 trial (`T4Source.bind_ok_run`). -/
theorem bind_ok_run {σ α β : Type} {x : StateT σ AmbientM α} {f : α → StateT σ AmbientM β}
    {g : σ} {a : Ambient} {r : (β × σ) × Ambient} (h : ((x >>= f).run g).run a = .ok r) :
    ∃ v g' a', (x.run g).run a = .ok ((v,g'),a') ∧ ((f v).run g').run a' = .ok r := by
  have unfolded : ((x >>= f).run g).run a =
      ((x.run g).run a >>= fun p => ((f p.1.1).run p.1.2).run p.2) := rfl
  rw [unfolded] at h
  cases hx : (x.run g).run a with
  | error e => rw [hx] at h; cases h
  | ok p => rw [hx] at h; exact ⟨p.1.1,p.1.2,p.2,rfl,h⟩

theorem ok_inj {σ α : Type} {x : Except Stop ((α × σ) × Ambient)} {v : α} {s : σ} {a : Ambient}
    (h : x = .ok ((v,s),a)) (v0 : α) (s0 : σ) (a0 : Ambient) (e : x = .ok ((v0,s0),a0)) :
    v0 = v ∧ s0 = s ∧ a0 = a := by
  cases e.symm.trans h
  exact ⟨rfl,rfl,rfl⟩

/-- The device with a component store written back, as `liftAip` does. -/
def asDev (d : Device) (s : AipStore) : Device :=
  {d with nodes := s.nodes, nextNode := s.nextNode, peerAllowedips := s.trie}

theorem liftAip_acc {α : Type} {x : AipM α} {g g' : WGWorld} {a a' : Ambient} {d : Device} {v : α}
    (device : g.dev = some d) (run : ((WG.liftAip x).run g).run a = .ok ((v,g'),a')) :
    ∃ s', (x.run (Source.Aip.store d)).run a = .ok ((v,s'),a') ∧ g' = {g with dev := some (asDev d s')} := by
  rw [Model.liftAip_run,device] at run
  cases inner : (x.run {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}).run a with
  | error e => simp only [inner] at run; cases run
  | ok p =>
    obtain ⟨⟨v',s'⟩,a''⟩ := p
    simp only [inner] at run
    cases run
    exact ⟨s',inner,rfl⟩

theorem world_same {g : WGWorld} {d : Device} (device : g.dev = some d) : ({g with dev := some d} : WGWorld) = g := by
  rw [← device]

theorem getNode_acc {id : NodeId} {s s' : AipStore} {a a' : Ambient} {n : AipNode}
    (run : ((getNode id).run s).run a = .ok ((n,s'),a')) : s.nodes.get? id = some n ∧ s' = s ∧ a' = a := by
  cases present : s.nodes[id]? with
  | none => simp [getNode,present,invariant,AmbientM.invariant] at run; cases run
  | some node =>
    simp [getNode,present] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact ⟨present,rfl,rfl⟩


theorem connectNode_acc {slot : Slot} {id : NodeId} {d : Device} {s' : AipStore} {a a' : Ambient}
    (run : ((connectNode slot id).run (Source.Aip.store d)).run a = .ok (((),s'),a')) :
    asDev d s' = connect d slot id ∧ a' = a := by
  unfold connectNode at run
  obtain ⟨n,s1,a1,read,r1⟩ := bind_ok_run run
  clear run
  obtain ⟨present,rfl,rfl⟩ := getNode_acc read
  clear read
  obtain ⟨u,s2,a2,write,r2⟩ := bind_ok_run r1
  clear r1
  obtain ⟨rfl,rfl,rfl⟩ := ok_inj write () _ _ rfl
  clear write
  have present' : d.nodes.get? id = some n := present
  cases slot with
  | root4 =>
    obtain ⟨_,rfl,rfl⟩ := ok_inj r2 () _ _ rfl
    refine ⟨?_,rfl⟩
    simp only [connect,present',setSlot]
    rfl
  | root6 =>
    obtain ⟨_,rfl,rfl⟩ := ok_inj r2 () _ _ rfl
    refine ⟨?_,rfl⟩
    simp only [connect,present',setSlot]
    rfl
  | child parent bit =>
    unfold slotSet at r2
    obtain ⟨p,s3,a3,readParent,r3⟩ := bind_ok_run r2
    clear r2
    obtain ⟨parentPresent,rfl,rfl⟩ := getNode_acc readParent
    clear readParent
    dsimp only at r3
    by_cases large : bit > 1
    · simp only [large,↓reduceIte] at r3
      obtain ⟨_,_,_,thrown,_⟩ := bind_ok_run r3
      cases thrown
    · simp only [large,↓reduceIte] at r3
      obtain ⟨_,rfl,rfl⟩ := ok_inj r3 () _ _ rfl
      refine ⟨?_,rfl⟩
      have parentPresent' : (d.nodes.insert id {n with parent := Slot.child parent bit}).get? parent = some p :=
        parentPresent
      simp only [connect,present',setSlot,parentPresent']
      rfl

end Binary.Statements.C1.Proof
