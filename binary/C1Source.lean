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
import PairAllowedipsLookupAdequacy
import AllowedipsSourceFrames
import AllowedipsStorage
import AllowedipsRootIncoming
import AllowedipsInternalFrame
import MemoryBytes
import AllowedipsAllocationNames
import PairAllowedipsPlacementSource
import TrieHeap
import PairCallSource
import AllowedipsPlacementSourceStep
import AllowedipsHeapChecks
import AllowedipsTrieEdgeFacts
import PairAllowedipsLookupFrame

/-! Result C1, work package 1: the source side and the invariant's algebra. This module is the package's root in
`binary/lakefile.toml`. The brief is `binary/Statements/C1/proof/WP1.md`.

The package is this one file: the library lists its roots one by one, so a
module `C1SourceX` beside it is not a library module, and the lake file is
not the package's to edit. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1
open Binary.CommonBitsCoverage
local instance : Labels := Image.linkedLabels

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


/-! ## `LookupStep` for `Inv` -/

/-! ## `LookupStep` for `Inv` -/

/-! ### The mirror's lookup leaves the pending records and the armed sites alone -/

/-- What `Related` reads of the ambient state. -/
def pendingView (w : World) : Option (List HiddenRecord) × List String :=
  (w.ambient.hidden,w.ambient.allocArmed)

open MirrorHistory LookupSourceFrame in
theorem frames_branch_pending (d : Decision) (b : Bool) :
    Frames pendingView (branchLogged d b) := by
  unfold branchLogged
  apply frames_bind (frames_lift (show Preserves pendingView (branch d b) from by
    intro w x w' run
    cases run
    rfl))
  intro answer
  apply frames_bind (frames_mark _ _)
  intro _
  exact frames_pure _ answer

open MirrorHistory LookupSourceFrame AllowedipsSource in
theorem frames_choices_pending (w : World) (choices : Choices) :
    pendingView (records w choices) = pendingView w ∧
      ∀ p ∈ choicePoints w choices, pendingView p.world = pendingView w :=
  ⟨(congrArg pendingView (records_world w choices)).trans rfl,
    fun p member => (congrArg pendingView (choicePoints_world w choices p member)).trans rfl⟩

open MirrorHistory LookupSourceFrame AllowedipsSource in
theorem frames_commonBits_pending (node : AipNode) (key bits : Nat) :
    Frames pendingView (AllowedipsSource.commonBits node key bits) := by
  intro initial history w answer points final same prior run
  rw [commonBits_run] at run
  cases run
  obtain ⟨after,during⟩ := frames_choices_pending w (commonChoices node key bits)
  refine ⟨after.trans same,?_⟩
  intro p member
  rcases List.mem_append.mp member with old | added
  · exact prior p old
  · exact (during p added).trans same

open MirrorHistory LookupSourceFrame AllowedipsSource in
theorem frames_swapEndian_pending (bits : Nat) :
    Frames pendingView (AllowedipsSource.swapEndian bits) := by
  intro initial history w answer points final same prior run
  rw [swapEndian_run] at run
  cases run
  obtain ⟨after,during⟩ := frames_choices_pending w (swapChoices bits)
  refine ⟨after.trans same,?_⟩
  intro p member
  rcases List.mem_append.mp member with old | added
  · exact prior p old
  · exact (during p added).trans same

open MirrorHistory LookupSourceFrame AllowedipsSource in
theorem frames_iteration_pending (bits key : Nat) (acc : Acc) :
    Frames pendingView (iteration bits key acc) := by
  unfold iteration
  cases acc.2.1 with
  | none =>
    apply frames_bind (frames_branch_pending _ _)
    intro _
    exact frames_pure _ _
  | some id =>
    apply frames_bind (frames_branch_pending _ _)
    intro _
    apply frames_bind (frames_lift (preserves_getNode _ id))
    intro n
    apply frames_bind (show Frames pendingView (AllowedipsSource.prefixMatches n key bits) from by
      unfold AllowedipsSource.prefixMatches
      apply frames_bind (frames_called _ (frames_commonBits_pending n key bits))
      intro common
      exact frames_pure _ _)
    intro matching
    apply frames_bind (frames_branch_pending _ _)
    intro matching
    cases matching with
    | false => exact frames_pure _ _
    | true =>
      apply frames_bind (frames_branch_pending _ _)
      intro hasPeer
      cases hasPeer <;> apply frames_bind (frames_branch_pending _ _) <;> intro full
      all_goals cases full with
      | true => exact frames_pure _ _
      | false =>
        apply frames_bind (frames_lift (preserves_choose _ n key))
        intro bit
        apply frames_bind (frames_lift (preserves_bitAt _ n bit))
        intro next
        exact frames_pure _ _

open MirrorHistory LookupSourceFrame AllowedipsSource in
theorem frames_findNode_pending (trie : Option NodeId) (bits key : Nat) :
    Frames pendingView (AllowedipsSource.findNode trie bits key) := by
  rw [findNode_bounded]
  have loops : ∀ fuel acc, Frames pendingView (loop bits key fuel acc) := by
    intro fuel
    induction fuel with
    | zero => intro acc; exact frames_pure _ acc
    | succ fuel ih =>
      intro acc
      unfold loop
      apply frames_bind (frames_iteration_pending bits key acc)
      intro step
      cases step with
      | done answer => exact frames_pure _ answer
      | yield next => exact ih next
  apply frames_bind (loops 130 _)
  intro acc
  unfold AllowedipsSource.finish
  cases acc.1 with
  | none => exact frames_lift (preserves_throw _ _)
  | some answer => exact frames_pure _ answer

open MirrorHistory LookupSourceFrame in
theorem frames_count_pending (old : Nat) : Frames pendingView (count old) := by
  intro initial history w answer points w' same prior run
  have erased := count_erases old history w
  rw [run] at erased
  have actual : (refcountIncNotZero old : M Bool).run w = .ok (answer,w') := erased.symm
  have small := PeerMirror.accepted_count_bound old w w' answer actual
  rw [count_run_logged old history w small] at run
  cases run
  refine ⟨?_,?_⟩
  · refine Eq.trans ?_ same
    unfold PeerMirror.countRecords
    split <;> rfl
  · intro p member
    rcases List.mem_append.mp member with original | added
    · exact prior p original
    · refine Eq.trans ?_ same
      by_cases zero : old = 0 <;>
        simp [countPoints, PeerMirror.countRecords, PeerMirror.recordCmp, LookupMirror.record, zero] at added <;>
        rcases added with rfl | rfl | rfl | rfl <;> rfl

open MirrorHistory LookupSourceFrame in
theorem frames_peerGet_pending (peer : Option PeerId) : Frames pendingView (peerGet peer) := by
  unfold MirrorHistory.peerGet
  apply frames_bind (frames_branch_pending _ _)
  intro null
  cases null with
  | true => exact frames_pure _ _
  | false =>
    cases peer with
    | none => exact frames_lift (preserves_throw _ _)
    | some pid =>
      apply frames_bind (frames_lift (preserves_pure pendingView ()))
      intro _
      apply frames_bind (frames_lift (preserves_getPeer pendingView pid))
      intro p
      apply frames_bind (frames_count_pending p.refcount)
      intro live
      apply frames_bind (frames_branch_pending _ _)
      intro dead
      cases dead with
      | true => exact frames_pure _ _
      | false =>
        apply frames_bind (frames_lift (show Preserves pendingView (Source.setPeer pid _) from by
          intro w x w' run
          cases run
          rfl))
        intro _
        exact frames_pure _ _

open MirrorHistory LookupSourceFrame AllowedipsSource in
theorem frames_lookup_pending (root : Option NodeId) (bits key : Nat) :
    Frames pendingView (AllowedipsSource.lookup root bits key) := by
  unfold AllowedipsSource.lookup
  apply frames_called
  apply frames_bind (frames_swapEndian_pending bits)
  intro _
  apply frames_bind (frames_findNode_pending root bits key)
  intro node
  apply frames_bind (frames_branch_pending _ _)
  intro found
  cases found with
  | false => exact frames_pure _ _
  | true =>
    cases node with
    | none =>
      apply frames_bind (frames_lift (preserves_throw _ _))
      intro _
      exact frames_pure _ _
    | some id =>
      apply frames_bind (frames_lift (preserves_getNode _ id))
      intro n
      apply frames_bind (frames_called _ (frames_peerGet_pending n.peer))
      intro peer
      apply frames_bind (frames_branch_pending _ _)
      intro gone
      cases gone with
      | false => exact frames_pure _ _
      | true =>
        apply frames_bind (frames_lift (show Preserves pendingView
          (unsupported "lookup retry after a dying peer" : M Unit) from by
            intro w x w' run
            cases run))
        intro _
        exact frames_pure _ _

/-- An accepted lookup of the mirror consumes no record and arms or disarms no site. -/
theorem lookup_pending {root : Option NodeId} {bits key : Nat} {w final : World}
    {answer : Option PeerId} (accepted : (Source.lookup root bits key).run w = .ok (answer,final)) :
    final.ambient.hidden = w.ambient.hidden ∧ final.ambient.allocArmed = w.ambient.allocArmed := by
  obtain ⟨points,logged⟩ := AllowedipsSource.lookup_accepted root bits key [] w final answer accepted
  have framed := (frames_lookup_pending root bits key (pendingView w) [] w answer points final rfl
    (by intro p member; cases member) logged).1
  exact ⟨congrArg Prod.fst framed,congrArg Prod.snd framed⟩

#print axioms lookup_pending

/-! ### Span arithmetic for the executable separations -/

theorem spansApart_of {left right : List Pair.Span}
    (h : ∀ a ∈ left, ∀ b ∈ right,
      a.1+a.2 ≤ 2^64 ∧ b.1+b.2 ≤ 2^64 ∧ (a.1+a.2 ≤ b.1 ∨ b.1+b.2 ≤ a.1)) :
    spansApart left right = true := by
  unfold spansApart
  simp only [List.all_eq_true,Bool.and_eq_true,decide_eq_true_eq,disjointRanges,Bool.or_eq_true]
  intro a ha b hb
  obtain ⟨x,y,z⟩ := h a ha b hb
  exact ⟨⟨x,y⟩,z⟩

theorem spansApart_mem {left right : List Pair.Span} (ok : spansApart left right = true)
    {a b : Pair.Span} (ha : a ∈ left) (hb : b ∈ right) :
    a.1+a.2 ≤ 2^64 ∧ b.1+b.2 ≤ 2^64 ∧ (a.1+a.2 ≤ b.1 ∨ b.1+b.2 ≤ a.1) := by
  have checked := List.all_eq_true.mp (List.all_eq_true.mp ok a ha) b hb
  have parts : (a.1+a.2 ≤ 2^64 ∧ b.1+b.2 ≤ 2^64) ∧ (a.1+a.2 ≤ b.1 ∨ b.1+b.2 ≤ a.1) := by
    simpa [disjointRanges] using checked
  exact ⟨parts.1.1,parts.1.2,parts.2⟩

/-- Every span of the first list lies, as a range of numbers, inside a span of the second. -/
def Within (inner outer : List Pair.Span) : Prop :=
  ∀ a ∈ inner, ∃ b ∈ outer, b.1 ≤ a.1 ∧ a.1+a.2 ≤ b.1+b.2

theorem Within.of_subset {inner outer : List Pair.Span} (subset : ∀ a ∈ inner, a ∈ outer) :
    Within inner outer := fun a member => ⟨a,subset a member,Nat.le_refl _,Nat.le_refl _⟩

theorem Within.append {left right outer : List Pair.Span}
    (l : Within left outer) (r : Within right outer) : Within (left ++ right) outer := by
  intro a member
  rcases List.mem_append.mp member with h | h
  · exact l a h
  · exact r a h

theorem Within.trans {a b c : List Pair.Span} (ab : Within a b) (bc : Within b c) : Within a c := by
  intro x member
  obtain ⟨y,my,l,h⟩ := ab x member
  obtain ⟨z,mz,l',h'⟩ := bc y my
  exact ⟨z,mz,by omega,by omega⟩

theorem spansApart_within {left right inner inner' : List Pair.Span}
    (ok : spansApart left right = true) (l : Within inner left) (r : Within inner' right) :
    spansApart inner inner' = true := by
  apply spansApart_of
  intro a ha b hb
  obtain ⟨a',ma,la,ua⟩ := l a ha
  obtain ⟨b',mb,lb,ub⟩ := r b hb
  obtain ⟨x,y,z⟩ := spansApart_mem ok ma mb
  refine ⟨by omega,by omega,?_⟩
  rcases z with z | z
  · exact .inl (by omega)
  · exact .inr (by omega)

/-! ### What `lookupReady` gives -/

structure FrameFacts (L : Layout) (c : Context) (s : MachineState) (ra : UInt64)
    (query : Pair.Span) : Prop where
  abi : (s.data.regs.rsp.toNat % 8 == 0 &&
    s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 == some (ra.toNat : Int)) = true
  stack : ((List.range lookupWindow).all fun i =>
    (s.data.dmem.get? (s.data.regs.rsp.toBitVec - .ofNat 64 (i+1))).isSome) = true
  coverage : Trie.coverageCheck c s.data.dmem = true
  coverageBh : Trie.coverageDataCheck ⟨c.coverage,c.preempt+512⟩ s.data.dmem = true
  hardirq : ((c.preempt+512) &&& 0x000f0000 == 0) = true
  pending : (if LookupPendingRead c.preempt then
    s.data.dmem.loadInt softirqPendingAddress 2 == some 0 else true) = true
  heap : spansApart L.heap (callerSpans s lookupWindow query false ++ Trie.callServices c ++
    Trie.callBuffers c) = true
  service : spansApart (Trie.callServices c) [(callerSpans s lookupWindow query false).head!] = true
  buffer : spansApart (Trie.callBuffers c) (callerSpans s lookupWindow query false ++
    Trie.callMetadata c ++ [(preemptCountAddress.toNat,4)]) = true
  preempt : spansApart ([(callerSpans s lookupWindow query false).head!] ++ Trie.callMetadata c ++
    Trie.callHeaders c) [(preemptCountAddress.toNat,4)] = true
  caller : spansApart [((s.data.regs.rsp.toBitVec - .ofNat 64 lookupWindow).toNat,lookupWindow)]
    (callerSpans s lookupWindow query false).tail! = true

theorem frameReady_lookup {L : Layout} {c : Context} {s : MachineState} {ra : UInt64}
    {query : Pair.Span} (run : frameReady L c s ra lookupWindow query false true = .ok ()) :
    FrameFacts L c s ra query := by
  unfold frameReady at run
  obtain ⟨abi,run⟩ := require_bind_ok _ _ _ _ run
  obtain ⟨stack,run⟩ := require_bind_ok _ _ _ _ run
  obtain ⟨coverage,run⟩ := require_bind_ok _ _ _ _ run
  simp only [Bool.false_eq_true,↓reduceIte] at run
  obtain ⟨coverageBh,run⟩ := require_bind_ok _ _ _ _ run
  obtain ⟨hardirq,run⟩ := require_bind_ok _ _ _ _ run
  obtain ⟨pending,run⟩ := require_bind_ok _ _ _ _ run
  obtain ⟨heap,run⟩ := require_bind_ok _ _ _ _ run
  obtain ⟨service,run⟩ := require_bind_ok _ _ _ _ run
  obtain ⟨buffer,run⟩ := require_bind_ok _ _ _ _ run
  obtain ⟨preempt,run⟩ := require_bind_ok _ _ _ _ run
  exact ⟨abi,stack,coverage,coverageBh,hardirq,pending,heap,service,buffer,preempt,require_ok run⟩

structure ReadyFacts (L : Layout) (c : Context) (s : MachineState) (family key : Nat)
    (ra : UInt64) : Prop where
  families : family = 4 ∨ family = 6
  entry : s.pc = AllowedipsImage.Lookup.entry
  root : readNat s (L.table + (if family == 4 then AllowedipsMutationLayout.root4
    else AllowedipsMutationLayout.root6)) 8 = .ok s.data.regs.rdi.toNat
  width : s.data.regs.rsi.toNat = (if family == 4 then 32 else 128)
  address : Trie.networkKeyCheck s.data.dmem s.data.regs.rdx.toBitVec (if family == 4 then 32 else 128) key = true
  frame : FrameFacts L c s ra (s.data.regs.rdx.toNat,(if family == 4 then 32 else 128)/8)

theorem lookupReady_facts {L : Layout} {c : Context} {s : MachineState} {family key : Nat}
    {ra : UInt64} (run : lookupReady L c s family key ra = .ok ()) : ReadyFacts L c s family key ra := by
  unfold lookupReady at run
  obtain ⟨familyOk,run⟩ := require_bind_ok _ _ _ _ run
  obtain ⟨entry,run⟩ := require_bind_ok _ _ _ _ run
  obtain ⟨word,read,run⟩ := bind_ok run
  obtain ⟨root,run⟩ := require_bind_ok _ _ _ _ run
  obtain ⟨width,run⟩ := require_bind_ok _ _ _ _ run
  obtain ⟨address,run⟩ := require_bind_ok _ _ _ _ run
  refine ⟨by simpa using familyOk,by simpa using entry,?_,by simpa using width,address,frameReady_lookup run⟩
  have equal : s.data.regs.rdi.toNat = word := by simpa using root
  rw [equal]
  exact read

/-! ### The heap's spans, as ranges of numbers -/

theorem nodeField_arena {L : Layout} {names : Allowedips.Names}
    (arena : ∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2)
    {id base offset size : Nat} (named : (id,base) ∈ names.trie.nodes)
    (field : (offset,size) ∈ nodeFields Root.nodeOffsets) :
    ∃ b ∈ L.arena, b.1 ≤ base+offset ∧ base+offset+size ≤ b.1+b.2 := by
  obtain ⟨object,inArena,low,high⟩ := arena (id,base) named
  have bound := nodeFields_within (offset,size) field
  simp only at bound low high
  exact ⟨object,inArena,by omega,by omega⟩

theorem readSpans_within {L : Layout} {names : Allowedips.Names}
    (table : names.table = L.table) (peers : names.trie.peers = L.peers)
    (arena : ∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2) :
    Within (readSpans names Root.nodeOffsets) L.heap := by
  intro span member
  unfold readSpans at member
  rw [table,peers] at member
  rcases List.mem_append.mp member with tablePart | rest
  · exact ⟨span,List.mem_append_left _ (List.mem_append_left _ tablePart),Nat.le_refl _,Nat.le_refl _⟩
  rcases List.mem_append.mp rest with nodePart | peerPart
  · obtain ⟨⟨id,base⟩,named,field⟩ := List.mem_flatMap.mp nodePart
    obtain ⟨⟨offset,size⟩,listed,rfl⟩ := List.mem_map.mp field
    obtain ⟨object,inArena,low,high⟩ := nodeField_arena arena named listed
    exact ⟨object,List.mem_append_right _ inArena,low,high⟩
  · exact ⟨span,List.mem_append_left _ (List.mem_append_right _ peerPart),Nat.le_refl _,Nat.le_refl _⟩

theorem count_fixed {L : Layout} {names : Allowedips.Names} (peers : names.trie.peers = L.peers) :
    ∀ span ∈ Trie.countSpans names.trie Root.nodeOffsets, span ∈ L.fixed := by
  intro span member
  unfold Trie.countSpans at member
  rw [peers] at member
  obtain ⟨⟨id,base⟩,named,rfl⟩ := List.mem_map.mp member
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨(id,base),named,
    List.mem_map.mpr ⟨(Root.nodeOffsets.peerRefcount,4),by simp [peerFields],rfl⟩⟩)

theorem trieSpans_within {L : Layout} {names : Allowedips.Names}
    (arena : ∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2) :
    Within (Trie.trieSpans names.trie Root.nodeOffsets) L.arena := by
  intro span member
  obtain ⟨⟨id,base⟩,named,field⟩ := List.mem_flatMap.mp member
  obtain ⟨⟨offset,size⟩,listed,rfl⟩ := List.mem_map.mp field
  exact nodeField_arena arena named (List.mem_append_left _ listed)

theorem decoderSpans_within {L : Layout} {names : Allowedips.Names}
    (peers : names.trie.peers = L.peers)
    (arena : ∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2) :
    Within (Trie.decoderSpans names.trie Root.nodeOffsets) L.heap := by
  intro span member
  rcases List.mem_append.mp member with node | count
  · obtain ⟨b,inArena,low,high⟩ := trieSpans_within arena span node
    exact ⟨b,List.mem_append_right _ inArena,low,high⟩
  · exact ⟨span,List.mem_append_left _ (count_fixed peers span count),Nat.le_refl _,Nat.le_refl _⟩

theorem count_objects {L : Layout} {names : Allowedips.Names} (peers : names.trie.peers = L.peers) :
    Within (Trie.countSpans names.trie Root.nodeOffsets)
      ([(L.table,AllowedipsMutationLayout.tableSize)] ++ L.peers.map fun (_,a) => (a,Layouts.peerSize)) := by
  intro span member
  unfold Trie.countSpans at member
  rw [peers] at member
  obtain ⟨⟨id,base⟩,named,rfl⟩ := List.mem_map.mp member
  refine ⟨(base,Layouts.peerSize),List.mem_append_right _ (List.mem_map.mpr ⟨(id,base),named,rfl⟩),?_,?_⟩
  · exact Nat.le_add_right _ _
  · simp only [Root.nodeOffsets,Layouts.peer_refcount,Layouts.peerSize]
    omega

theorem spansApart_append_right {left first second : List Pair.Span}
    (a : spansApart left first = true) (b : spansApart left second = true) :
    spansApart left (first ++ second) = true := by
  apply spansApart_of
  intro x hx y hy
  rcases List.mem_append.mp hy with h | h
  · exact spansApart_mem a hx h
  · exact spansApart_mem b hx h

theorem spansApart_symm {left right : List Pair.Span} (ok : spansApart left right = true) :
    spansApart right left = true := by
  apply spansApart_of
  intro x hx y hy
  obtain ⟨p,q,r⟩ := spansApart_mem ok hy hx
  exact ⟨q,p,r.symm⟩

/-! ### The table against the named objects, from the interpretation check -/

theorem table_apart {names : Allowedips.Names} {o : AllowedipsProbe.Offsets}
    (valid : Allowedips.validate names o = .ok ()) :
    names.table+AllowedipsMutationLayout.tableSize < 2^64 ∧
    ∀ span ∈ allocations names o,
      disjointRanges span.1 span.2 names.table AllowedipsMutationLayout.tableSize = true := by
  unfold Allowedips.validate at valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨tableOk,valid⟩ := check_ok _ _ _ _ valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨_,_,valid⟩ := bind_ok valid
  obtain ⟨_,valid,_⟩ := bind_ok valid
  have bound : (0 < names.table ∧ names.table % 8 = 0) ∧
      names.table+AllowedipsMutationLayout.tableSize < 2^64 := by simpa using tableOk
  refine ⟨bound.2,?_⟩
  exact forIn_ok (P := fun span : Nat×Nat =>
      disjointRanges span.1 span.2 names.table AllowedipsMutationLayout.tableSize = true)
    (fun span _ _ _ run => by
      rcases span with ⟨a,size⟩
      dsimp only at run ⊢
      by_cases apart : disjointRanges a size names.table AllowedipsMutationLayout.tableSize = true
      · simp only [apart,↓reduceIte] at run
        exact ⟨(),(Except.ok.inj run).symm,apart⟩
      · simp only [apart] at run
        cases run) valid

/-- The words the structural check reads are apart from the peers' counts. -/
theorem metadata_count_apart {names : Allowedips.Names} {m : DataMem} {d : Device}
    (related : Allowedips.Corresponds names Root.nodeOffsets m d) :
    spansApart (metadataSpans names Root.nodeOffsets)
      (Trie.countSpans names.trie Root.nodeOffsets) = true := by
  have g := geometry related
  obtain ⟨tableBound,tableApart⟩ := table_apart (Allowedips.reconstruct_fields related).valid
  have symmetric : ∀ a b : Pair.Span, disjointRanges a.1 a.2 b.1 b.2 = true →
      disjointRanges b.1 b.2 a.1 a.2 = true := by
    intro a b h
    simpa only [disjointRanges,Bool.or_comm] using h
  apply spansApart_of
  intro a ha b hb
  obtain ⟨⟨pid,p⟩,peerNamed,rfl⟩ := List.mem_map.mp hb
  have peerObject : (p,Layouts.peerSize) ∈ allocations names Root.nodeOffsets :=
    List.mem_append_right _ (List.mem_map.mpr ⟨(pid,p),peerNamed,rfl⟩)
  have peerBound := g.bounded _ peerObject
  have count : Root.nodeOffsets.peerRefcount = 1056 := rfl
  have size : Layouts.peerSize = 1520 := rfl
  simp only [count,size] at peerBound ⊢
  rcases List.mem_append.mp ha with tablePart | rest
  · obtain ⟨⟨offset,width⟩,field,rfl⟩ := List.mem_map.mp tablePart
    have inside : offset+width ≤ 24 := by
      simp only [tableFields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at field
      rcases field with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
    have apart := tableApart _ peerObject
    simp only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq,size,
      show AllowedipsMutationLayout.tableSize = 24 from rfl] at apart tableBound
    simp only
    omega
  rcases List.mem_append.mp rest with nodePart | peerPart
  · obtain ⟨⟨id,base⟩,named,field⟩ := List.mem_flatMap.mp nodePart
    obtain ⟨⟨offset,width⟩,listed,rfl⟩ := List.mem_map.mp field
    have inside := nodeFields_within (offset,width) listed
    have nodeObject : (base,Root.nodeOffsets.nodeSize) ∈ allocations names Root.nodeOffsets :=
      List.mem_append_left _ (List.mem_map.mpr ⟨(id,base),named,rfl⟩)
    have nodeBound := g.bounded _ nodeObject
    have different : (base,Root.nodeOffsets.nodeSize) ≠ (p,Layouts.peerSize) := by
      intro equal
      have sizes : Root.nodeOffsets.nodeSize = Layouts.peerSize := congrArg Prod.snd equal
      exact absurd sizes (by decide)
    have apart := Trie.pairwise_mem_ne symmetric g.apart nodeObject peerObject different
    simp only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq,size,
      show Root.nodeOffsets.nodeSize = 72 from rfl] at apart nodeBound
    simp only [show nodeSize = 72 from rfl] at inside
    simp only
    omega
  · obtain ⟨⟨id,base⟩,named,field⟩ := List.mem_flatMap.mp peerPart
    obtain ⟨⟨offset,width⟩,listed,rfl⟩ := List.mem_map.mp field
    have otherObject : (base,Layouts.peerSize) ∈ allocations names Root.nodeOffsets :=
      List.mem_append_right _ (List.mem_map.mpr ⟨(id,base),named,rfl⟩)
    have otherBound := g.bounded _ otherObject
    have inside : (offset = 1096 ∨ offset = 1104) ∧ width = 8 := by
      simp only [listFields,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq,
        show AllowedipsMutationLayout.allowedips_list = 1096 from rfl] at listed
      rcases listed with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨.inl rfl,rfl⟩
      · exact ⟨.inr rfl,rfl⟩
    simp only [size] at otherBound
    by_cases same : base = p
    · subst base
      simp only
      omega
    · have different : (base,Layouts.peerSize) ≠ (p,Layouts.peerSize) :=
        fun equal => same (congrArg Prod.fst equal)
      have apart := Trie.pairwise_mem_ne symmetric g.apart otherObject peerObject different
      simp only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq,size] at apart
      simp only
      omega

/-! ### The landed entry check from `Inv` and `lookupReady` -/

theorem loadInt_mapped (m : Mem 64) (base : BitVec 64) (n : Nat)
    (mapped : ∀ i < n, (m.get? (base + .ofNat 64 i)).isSome = true) :
    (m.loadInt base n).isSome = true := by
  have bytes : m.loadBytes base n =
      some ((List.range n).map fun i => (m.get? (base + .ofNat 64 i)).getD 0) := by
    rw [MemoryBytes.loadBytes_iff]
    refine ⟨by simp,?_⟩
    intro i hi
    have bound : i < n := by simpa using hi
    have present := mapped i bound
    simp only [List.getElem_map,List.getElem_range]
    cases read : m.get? (base + .ofNat 64 i) with
    | none => rw [read] at present; cases present
    | some b => rfl
  simp only [Mem.loadInt,bytes,Option.map_some,Option.isSome_some]

theorem root_family {s : State} {id : NodeId} {node : AipNode}
    (ok : structureCheck s id node = .ok ()) :
    (s.table.root4 = some id → node.bitlen = 32) ∧ (s.table.root6 = some id → node.bitlen = 128) := by
  rw [structureCheck_walk] at ok
  obtain ⟨incoming,roots,_⟩ := bind_ok ok
  have each := forIn_ok (P := fun entry : Option NodeId×Slot×Nat =>
      entry.1 = some id → node.bitlen = entry.2.2)
    (fun entry _ before after run => by
      unfold rootStep at run
      by_cases here : entry.1 = some id
      · simp only [here,beq_self_eq_true,↓reduceIte] at run
        obtain ⟨width,run⟩ := check_ok _ _ _ _ run
        exact ⟨_,(Except.ok.inj run).symm,fun _ => eq_of_beq width⟩
      · have differs : (entry.1 == some id) = false := by simpa using here
        simp only [differs,Bool.false_eq_true,↓reduceIte] at run
        exact ⟨_,(Except.ok.inj run).symm,fun at_ => absurd at_ here⟩) roots
  exact ⟨each (s.table.root4,.root4,32) (by simp),each (s.table.root6,.root6,128) (by simp)⟩

/-- A root word the reconstruction decoded: it is the address the interpretation
gives the root, and the node there has the slot's family. -/
theorem root_slot {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {m : DataMem} {d : Device}
    (related : Allowedips.Corresponds names o m d) {path : String} {raw width : Nat}
    {root : Option NodeId} (decoded : Trie.pointer names.trie.nodes path raw = .ok root)
    (family : ∀ (id : NodeId) (node : AipNode), root = some id →
      (id,node) ∈ (Allowedips.target d).nodes → node.bitlen = width) :
    Trie.address names.trie.nodes root = .ok raw ∧
    ∀ id, root = some id → ∃ node, Trie.decodeNode names.trie o m raw = .ok node ∧ node.width = width := by
  have fields := Allowedips.reconstruct_fields related
  have unique := (Trie.reconstruct_fields related.trie).nodeIds
  unfold Trie.pointer at decoded
  by_cases zero : raw = 0
  · subst raw
    have equal : none = root := Except.ok.inj decoded
    subst root
    exact ⟨rfl,by intro id h; cases h⟩
  · simp only [beq_iff_eq,zero,↓reduceIte] at decoded
    cases found : names.trie.nodes.find? (·.2 == raw) with
    | none => rw [found] at decoded; cases decoded
    | some pair =>
      rw [found] at decoded
      have equal : some pair.1 = root := Except.ok.inj decoded
      subst root
      have member := List.mem_of_find?_eq_some found
      have address : pair.2 = raw := by simpa using List.find?_some found
      subst raw
      refine ⟨?_,?_⟩
      · simp only [Trie.address,Trie.find_identity unique member]
        rfl
      · intro id atRoot
        cases Option.some.inj atRoot
        obtain ⟨⟨current,node⟩,listed,run⟩ := fields.nodes.left pair member
        obtain ⟨same,core⟩ := Allowedips.decodeNode_fields run
        subst current
        exact ⟨Trie.targetNode node,core,family pair.1 node rfl listed⟩

theorem trie_assertAt {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {m : DataMem}
    {w : World} {d : Device} (device : w.wg.dev = some d)
    (related : Allowedips.Corresponds names o m d) (shape : heap names (target d) m = .ok ()) :
    Trie.assertAt names.trie o m w = .ok () := by
  have core : Trie.heap (Trie.target d) [d.peerAllowedips.root4,d.peerAllowedips.root6] = .ok () := by
    rw [← trieState_target]
    exact ((heap_checks names (target d) m).mp shape).1
  have trie : Trie.reconstruct names.trie o m = .ok (Trie.target d) := related.trie
  unfold Trie.assertAt
  rw [device,trie]
  dsimp only [Except.mapError,Bind.bind,Except.bind]
  simpa only [beq_self_eq_true,↓reduceIte] using core

/-- The probe input the landed lookup theorem is instantiated at: only its
offsets are read by the entry check. -/
def lookupInput : AllowedipsProbe.Input :=
  { instructions := #[], labels := #[], hooks := #[], offsets := Root.nodeOffsets, entry := 0,
    commonEntry := 0, preempt := 0, entryPreempt := 0, budget := 0, trace := .null, operation := 0 }

theorem callerSpans_lookup (s : MachineState) (query : Pair.Span) :
    callerSpans s lookupWindow query false =
      [((s.data.regs.rsp.toBitVec-144).toNat,152),query] := rfl

theorem network_key_bound {m : DataMem} {base : BitVec 64} {family key : Nat}
    (checked : Trie.networkKeyCheck m base (if family == 4 then 32 else 128) key = true) :
    key < 2^(if family == 4 then 32 else 128) := by
  unfold Trie.networkKeyCheck at checked
  by_cases v4 : (family == 4) = true
  · simp only [v4,↓reduceIte,beq_self_eq_true] at checked ⊢
    cases read : load32 m base with
    | none => rw [read] at checked; cases checked
    | some word =>
      rw [read] at checked
      have equal : (Allowedips.swap32 word).toNat = key := by simpa using checked
      rw [← equal]
      exact (Allowedips.swap32 word).isLt
  · simp only [v4,Bool.false_eq_true,↓reduceIte] at checked ⊢
    cases high : load64 m base with
    | none => simp [high] at checked
    | some hi =>
      cases low : load64 m (base+8) with
      | none => rw [high,low] at checked; cases checked
      | some lo =>
        rw [high,low] at checked
        have equal : (Allowedips.swap64 hi).toNat*2^64+(Allowedips.swap64 lo).toNat = key := by
          simpa using checked
        have a := (Allowedips.swap64 hi).isLt
        have b := (Allowedips.swap64 lo).isLt
        omega

theorem callInput_of {names : Trie.Names} {o : AllowedipsProbe.Offsets} {m : DataMem}
    {root : Option NodeId} {width key raw : Nat} (widths : width = 32 ∨ width = 128)
    (bound : key < 2^width) (address : Trie.address names.nodes root = .ok raw)
    (node : ∀ id, root = some id → ∃ node, Trie.decodeNode names o m raw = .ok node ∧ node.width = width) :
    Trie.callInput names o m root width key = .ok () := by
  unfold Trie.callInput
  have valid : ((width == 32 || width == 128) && decide (key < 2^width)) = true := by
    rcases widths with rfl | rfl <;> simpa using bound
  refine check_of _ _ _ _ valid ?_
  cases root with
  | none => rfl
  | some id =>
    obtain ⟨decoded,read,family⟩ := node id rfl
    simp only [address,bind,Except.bind,read,Except.mapError,family,beq_self_eq_true,↓reduceIte]
    rfl

/-- What a lookup writes outside the peers' counts lies inside what the caller
keeps apart from the heap. -/
theorem lookup_writes_within (s : MachineState) (c : Context) (query : Pair.Span) :
    Within (Trie.callStack s false ++ Trie.callBuffers c ++ [(preemptCountAddress.toNat,4)])
      ([((s.data.regs.rsp.toBitVec-144).toNat,152),query] ++ Trie.callServices c ++ Trie.callBuffers c) := by
  intro span member
  rcases List.mem_append.mp member with rest | preempt
  · rcases List.mem_append.mp rest with stack | buffer
    · obtain rfl : span = ((s.data.regs.rsp.toBitVec-144).toNat,144) := by
        simpa [Trie.callStack] using stack
      exact ⟨_,List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)),
        Nat.le_refl _,by simp only; omega⟩
    · exact ⟨span,List.mem_append_right _ buffer,Nat.le_refl _,Nat.le_refl _⟩
  · obtain rfl := List.mem_singleton.mp preempt
    exact ⟨_,List.mem_append_left _ (List.mem_append_right _
      (by simp [Trie.callServices,Trie.readSpans])),Nat.le_refl _,Nat.le_refl _⟩

theorem lookup_boundary {L : Layout} {c : Context} {s : MachineState} {w : World}
    {d : Device} {family key : Nat} {ra : UInt64} {names : Allowedips.Names}
    (table : names.table = L.table) (peers : names.trie.peers = L.peers)
    (device : w.wg.dev = some d)
    (related : Allowedips.Corresponds names Root.nodeOffsets s.data.dmem d)
    (shape : heap names (target d) s.data.dmem = .ok ())
    (apart : spansApart ([(L.table,AllowedipsMutationLayout.tableSize)] ++
      L.peers.map fun (_,a) => (a,Layouts.peerSize)) L.arena = true)
    (arena : ∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2)
    (ready : lookupReady L c s family key ra = .ok ()) :
    lookupBoundary names lookupInput c s w family key ra = .ok () := by
  have facts := lookupReady_facts ready
  have frame := facts.frame
  have heapApart : spansApart L.heap
      ([((s.data.regs.rsp.toBitVec-144).toNat,152),(s.data.regs.rdx.toNat,(if family == 4 then 32 else 128)/8)] ++
        Trie.callServices c ++ Trie.callBuffers c) = true := frame.heap
  have serviceApart : spansApart (Trie.callServices c) [((s.data.regs.rsp.toBitVec-144).toNat,152)] = true :=
    frame.service
  have bufferApart : spansApart (Trie.callBuffers c)
      ([((s.data.regs.rsp.toBitVec-144).toNat,152),(s.data.regs.rdx.toNat,(if family == 4 then 32 else 128)/8)] ++
        Trie.callMetadata c ++ [(preemptCountAddress.toNat,4)]) = true := frame.buffer
  have preemptApart : spansApart ([((s.data.regs.rsp.toBitVec-144).toNat,152)] ++ Trie.callMetadata c ++
      Trie.callHeaders c) [(preemptCountAddress.toNat,4)] = true := frame.preempt
  have callerApart : spansApart [((s.data.regs.rsp.toBitVec-144).toNat,144)]
      [(s.data.regs.rdx.toNat,(if family == 4 then 32 else 128)/8)] = true := frame.caller
  have fields := Allowedips.reconstruct_fields related
  have writesWithin := lookup_writes_within s c (s.data.regs.rdx.toNat,(if family == 4 then 32 else 128)/8)
  -- lookupBoundary's own separation
  have metadataApart : spansApart (metadataSpans names lookupInput.offsets)
      (lookupWrites names lookupInput.offsets c s) = true := by
    apply spansApart_append_right
    · exact spansApart_within heapApart
        ((Within.of_subset (metadataSpans_subset names _)).trans (readSpans_within table peers arena))
        writesWithin
    · exact metadata_count_apart related
  -- the landed entry check
  have widths : (if family == 4 then 32 else 128) = 32 ∨ (if family == 4 then 32 else 128) = 128 := by
    split
    · exact .inl rfl
    · exact .inr rfl
  have keyBound := network_key_bound facts.address
  obtain ⟨raw,rootRead,rootAddress,rootNode⟩ : ∃ raw,
      readNat s (L.table + (if family == 4 then AllowedipsMutationLayout.root4
        else AllowedipsMutationLayout.root6)) 8 = .ok raw ∧
      Trie.address names.trie.nodes
        (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = .ok raw ∧
      ∀ id, (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some id →
        ∃ node, Trie.decodeNode names.trie Root.nodeOffsets s.data.dmem raw = .ok node ∧
          node.width = (if family == 4 then 32 else 128) := by
    have checks := ((heap_checks names (target d) s.data.dmem).mp shape).2
    by_cases v4 : (family == 4) = true
    · obtain ⟨raw,read,decoded⟩ := fields.root4
      obtain ⟨address,node⟩ := root_slot (width := 32) related decoded
        (fun id node atRoot listed => (root_family (checks id node listed).1).1 atRoot)
      simp only [v4,↓reduceIte]
      rw [← table]
      exact ⟨raw,readNat_of_word read,address,node⟩
    · obtain ⟨raw,read,decoded⟩ := fields.root6
      obtain ⟨address,node⟩ := root_slot (width := 128) related decoded
        (fun id node atRoot listed => (root_family (checks id node listed).1).2 atRoot)
      simp only [v4,Bool.false_eq_true,↓reduceIte]
      rw [← table]
      exact ⟨raw,readNat_of_word read,address,node⟩
  have rdi : s.data.regs.rdi.toNat = raw := Except.ok.inj (facts.root.symm.trans rootRead)
  have input : Trie.callInput names.trie Root.nodeOffsets s.data.dmem
      (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6)
      (if family == 4 then 32 else 128) key = .ok () :=
    callInput_of widths keyBound rootAddress rootNode
  have stackTrue : Trie.callStack s true = [((s.data.regs.rsp.toBitVec-144).toNat,152)] := rfl
  have stackFalse : Trie.callStack s false = [((s.data.regs.rsp.toBitVec-144).toNat,144)] := rfl
  have frameOk : Trie.callFrameCheck names.trie Root.nodeOffsets c s ra
      (if family == 4 then 32 else 128) key = .ok () := by
    unfold Trie.callFrameCheck
    refine check_of _ _ _ _ frame.abi ?_
    refine check_of _ _ _ _ ?_ ?_
    · apply List.all_eq_true.mpr
      intro i hi
      have small : i < 18 := List.mem_range.mp hi
      apply loadInt_mapped
      intro j hj
      have mapped := List.all_eq_true.mp frame.stack ((i+1)*8-j-1)
        (List.mem_range.mpr (by simp only [lookupWindow]; omega))
      have equal : s.data.regs.rsp.toBitVec - BitVec.ofNat 64 ((i+1)*8-j-1+1) =
          s.data.regs.rsp.toBitVec - BitVec.ofNat 64 ((i+1)*8) + BitVec.ofNat 64 j := by
        bv_omega
      rw [← equal]
      exact mapped
    refine check_of _ _ _ _ facts.address ?_
    refine check_of _ _ _ _ (by rw [frame.coverage,frame.coverageBh]; rfl) ?_
    refine check_of _ _ _ _ frame.hardirq ?_
    refine check_of _ _ _ _ frame.pending ?_
    refine check_of _ _ _ _ (spansApart_within heapApart (decoderSpans_within peers arena) writesWithin) ?_
    refine check_of _ _ _ _ ?_ ?_
    · have size : (if ((if family == 4 then 32 else 128) == 32) = true then 4 else 16) =
          (if family == 4 then 32 else 128)/8 := by
        by_cases v4 : (family == 4) = true <;> simp [v4]
      rw [size,stackFalse]
      apply spansApart_append_right
      · exact spansApart_symm callerApart
      · apply spansApart_symm
        refine spansApart_within bufferApart
          (Within.of_subset fun span member => List.mem_append_left _ member)
          (Within.of_subset fun span member => ?_)
        obtain rfl := List.mem_singleton.mp member
        simp
    refine check_of _ _ _ _ ?_ ?_
    · rw [stackFalse]
      refine spansApart_within serviceApart (Within.of_subset fun _ member => member) ?_
      intro span member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨_,List.mem_singleton.mpr rfl,Nat.le_refl _,by simp only; omega⟩
    refine check_of _ _ _ _ ?_ ?_
    · rw [stackTrue]
      refine spansApart_within bufferApart (Within.of_subset fun _ member => member)
        (Within.of_subset fun span member => ?_)
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      rcases member with (rfl | h) | h
      · exact .inl (.inl (.inl rfl))
      · exact .inl (.inr h)
      · exact .inr h
    refine check_of _ _ _ _ ?_ ?_
    · rw [stackTrue]
      apply spansApart_append_right
      · refine spansApart_within heapApart
          (Within.of_subset fun span member => List.mem_append_left _ (count_fixed peers span member))
          (Within.of_subset fun span member => ?_)
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
        rcases member with rfl | h
        · exact .inl (.inl (.inl rfl))
        · exact .inl (.inr h)
      · exact spansApart_within apart (count_objects peers) (trieSpans_within arena)
    rw [stackTrue,preemptApart]
    rfl
  have callOk : Trie.callBoundary names.trie lookupInput c s w
      (if family == 4 then d.peerAllowedips.root4 else d.peerAllowedips.root6)
      (if family == 4 then 32 else 128) key ra = .ok () := by
    unfold Trie.callBoundary
    rw [show lookupInput.offsets = Root.nodeOffsets from rfl]
    rw [trie_assertAt device related shape,input,rootAddress]
    refine check_of _ _ _ _ ?_ frameOk
    simp [facts.entry,rdi,facts.width]
  unfold lookupBoundary
  rw [show lookupInput.offsets = Root.nodeOffsets from rfl]
  rw [assertAt_of_related device related shape]
  simp only [device]
  refine check_of _ _ _ _ (by simpa using facts.families) ?_
  exact check_of _ _ _ _ metadataApart callOk

theorem address_bound {names : List (Nat×Nat)} {id : Option Nat} {raw : Nat}
    (ok : Trie.address names id = .ok raw) (bounded : ∀ id a, (id,a) ∈ names → a < 2^64) :
    raw < 2^64 := by
  cases id with
  | none => cases ok; decide
  | some id =>
    simp only [Trie.address] at ok
    cases found : names.find? (·.1 == id) with
    | none => rw [found] at ok; cases ok
    | some pair =>
      rw [found] at ok
      have equal : pair.2 = raw := Except.ok.inj ok
      exact equal ▸ bounded pair.1 pair.2 (List.mem_of_find?_eq_some found)

/-- `LookupStep` for `Inv`, from the landed `lookup_checked`. -/
theorem lookupHolds : LookupHolds := by
  intro fetch L A premises c s w w' d family key ra answer pointer related device ready accepted address
  obtain ⟨names,stream,table,peers,asserted,armedBefore,hidden,sites,apart,arena,idle⟩ := related
  obtain ⟨d',device',corresponds,shape⟩ := assertAt_ok asserted
  obtain rfl : d' = d := Option.some.inj (device'.symm.trans device)
  have boundary := lookup_boundary table peers device corresponds shape apart arena ready
  have run := lookup_checked fetch premises.lookup premises.peer premises.callbacks premises.cmp1
    premises.constCmp4 premises.callbacks.constCmp1 premises.bhEnable device boundary accepted
  have facts := lookupReady_facts ready
  have heapApart : spansApart L.heap
      ([((s.data.regs.rsp.toBitVec-144).toNat,152),(s.data.regs.rdx.toNat,(if family == 4 then 32 else 128)/8)] ++
        Trie.callServices c ++ Trie.callBuffers c) = true := facts.frame.heap
  have arenaWrites : spansApart L.arena
      (Trie.callStack s false ++ Trie.callBuffers c ++ [(preemptCountAddress.toNat,4)]) = true :=
    spansApart_within heapApart (Within.of_subset fun span member => List.mem_append_right _ member)
      (lookup_writes_within s c _)
  have countArena : spansApart (Trie.countSpans names.trie Root.nodeOffsets) L.arena = true :=
    spansApart_within apart (count_objects peers) (Within.of_subset fun _ member => member)
  obtain ⟨hiddenSame,armedSame⟩ := lookup_pending accepted
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨post,⟨dFinal,deviceFinal,correspondsFinal,shapeFinal⟩,frame⟩
  refine ⟨post.returned,?_,?_,?_⟩
  · have bound : pointer < 2^64 := address_bound address fun id a member =>
      Nat.lt_of_le_of_lt (Nat.le_add_right _ _)
        ((Trie.reconstruct_fields corresponds.trie).peerRange id a (peers ▸ member)).2
    rw [← peers] at address
    rw [post.result,Trie.address_value address]
    change (BitVec.ofNat 64 pointer).toNat = pointer
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound]
  · refine ⟨names,stream,table,peers,assertAt_of_related deviceFinal correspondsFinal shapeFinal,?_,
      hiddenSame.trans hidden,sites,apart,arena,
      premises.allocator.frame s.data.dmem t.data.dmem _ _ idle ?_⟩
    · unfold armed at armedBefore ⊢
      rw [armedSame]
      exact armedBefore
    · intro a inArena _
      obtain ⟨object,listed,inside⟩ := inArena
      apply frame a
      rintro (written | count)
      · obtain ⟨span,member,at_⟩ := Trie.callTotalWrites_cover s c a written
        exact spansApart_sound arenaWrites listed member inside at_
      · obtain ⟨span,member,at_⟩ := Trie.countSpans_cover names.trie _ a count
        exact spansApart_sound countArena member listed at_ inside
  · intro a outside
    apply frame a
    rintro (written | count)
    · exact outside (.inl written)
    · obtain ⟨span,member,at_⟩ := Trie.countSpans_cover names.trie _ a count
      exact outside (.inr ⟨span,List.mem_append_left _ (count_fixed peers span member),at_⟩)

#print axioms lookupHolds

/-! ## What `RunIsStep` takes from the invariant and the caller's conditions -/

/-! ## What `RunIsStep` takes from the invariant and the caller's conditions -/

/-- `heap.root-family`, read off the structural check of one node. -/
theorem ordered_root_family {s : State} {id : NodeId} {n : AipNode}
    (checked : structureCheck s id n = .ok ()) :
    (s.table.root4 = some id → n.bitlen = 32) ∧ (s.table.root6 = some id → n.bitlen = 128) := by
  rw [structureCheck_walk] at checked
  obtain ⟨incoming,first,_⟩ := bind_ok checked
  simp only [List.forIn_cons,List.forIn_nil,rootStep] at first
  constructor
  · intro root
    by_cases family : n.bitlen = 32
    · exact family
    · simp [root,family] at first
      cases first
  · intro root
    by_cases family : n.bitlen = 128
    · exact family
    · by_cases other : s.table.root4 = some id
      · by_cases family4 : n.bitlen = 32
        · simp [root,other,family4] at first
          cases first
        · simp [other,family4] at first
          cases first
      · simp [root,other,family] at first
        cases first

/-- A node of the mirror's store is the decoding of a named object. -/
theorem ordered_node_fields {names : Allowedips.Names} {m : Mem 64} {d : Device} {id : NodeId} {n : AipNode}
    (related : Allowedips.Corresponds names Root.nodeOffsets m d) (member : (id,n) ∈ d.nodes.toList) :
    (n.bitlen = 32 ∨ n.bitlen = 128) ∧ n.cidr ≤ n.bitlen ∧ n.bits < 2^n.bitlen ∧ n.bit.size = 2 := by
  have full := Trie.reconstruct_fields related.trie
  have inTarget : (id,Trie.targetNode n) ∈ (Trie.target d).nodes :=
    List.mem_map.mpr ⟨(id,n),member,rfl⟩
  obtain ⟨⟨id',base⟩,_,_,decoded⟩ := full.nodes.right _ inTarget
  have fields := Trie.decodeNode_fields decoded
  obtain ⟨left,right,_,_,shape,_⟩ := fields.children
  have family : n.bitlen = 32 ∨ n.bitlen = 128 := fields.family
  have bounded : n.cidr ≤ n.bitlen := fields.bounded
  have shape' : n.bit = #[left,right] := shape
  refine ⟨family,bounded,?_,by rw [shape']; rfl⟩
  have key := fields.key
  change (if n.bitlen = 32 then _ else _) at key
  by_cases width : n.bitlen = 32
  · simp only [width,↓reduceIte] at key
    have bound := word_bound key
    change n.bits < 256^4 at bound
    rw [width]
    omega
  · simp only [width,↓reduceIte] at key
    obtain ⟨hi,lo,high,low,sum⟩ := key
    have highBound := word_bound high
    have lowBound := word_bound low
    have sum' : n.bits = hi*2^64+lo := sum
    have wide : n.bitlen = 128 := by omega
    rw [wide,sum']
    omega

theorem ordered_of_related {L : Layout} {A : Allocator} {w : World} {m : Mem 64} {d : Device}
    (related : Related L A w m) (device : w.wg.dev = some d) : ordered d = true := by
  obtain ⟨names,stream,_,_,asserted,_⟩ := related
  obtain ⟨d',device',corresponds,shape⟩ := assertAt_ok asserted
  have same : d' = d := Option.some.inj (device'.symm.trans device)
  subst d'
  obtain ⟨tree,checks⟩ := (heap_checks names (Allowedips.target d) m).mp shape
  have present : ∀ id (node : Trie.Node), (id,node) ∈ (Allowedips.target d).nodes.map (fun (id,n) => (id,Trie.targetNode n)) →
      ∃ n, d.nodes.get? id = some n ∧ node = Trie.targetNode n := by
    intro id node member
    obtain ⟨⟨id',n⟩,inside,equal⟩ := List.mem_map.mp member
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
    exact ⟨n,Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp inside,rfl⟩
  simp only [ordered,Bool.and_eq_true,List.all_eq_true]
  constructor
  · rintro ⟨id,n⟩ member
    obtain ⟨family,bounded,key,size⟩ := ordered_node_fields corresponds member
    refine ⟨⟨⟨⟨?_,by simpa using bounded⟩,by simpa using key⟩,by simpa using size⟩,?_⟩
    · simpa using family
    rintro ⟨child,bit⟩ edge
    cases child with
    | none => rfl
    | some next =>
      have facts := Trie.heap_edge_facts tree id (Trie.targetNode n)
        (List.mem_map.mpr ⟨(id,n),member,rfl⟩) (some next,bit) edge next rfl
      obtain ⟨childNode,found,_,width,measure,prefixEq,side⟩ := facts
      obtain ⟨c,stored,rfl⟩ := present next childNode (List.mem_of_find?_eq_some found)
      simp only [stored,edgeOrdered,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
      exact ⟨⟨⟨width,measure⟩,prefixEq⟩,side⟩
  · have roots : ∀ id, (d.peerAllowedips.root4 = some id ∨ d.peerAllowedips.root6 = some id) →
        ∃ n, d.nodes.get? id = some n ∧ (d.peerAllowedips.root4 = some id → n.bitlen = 32) ∧
          (d.peerAllowedips.root6 = some id → n.bitlen = 128) := by
      intro id which
      have member : some id ∈ [(Allowedips.target d).table.root4,(Allowedips.target d).table.root6] := by
        rcases which with h | h
        · exact List.mem_cons.mpr (.inl h.symm)
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (.inl h.symm))
      obtain ⟨node,inside⟩ := Trie.heap_root tree member
      obtain ⟨n,stored,_⟩ := present id node inside
      have listed : (id,n) ∈ (Allowedips.target d).nodes := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr stored
      exact ⟨n,stored,ordered_root_family (checks id n listed).1⟩
    rintro ⟨root,width⟩ member
    simp only [List.mem_cons,Prod.mk.injEq,List.not_mem_nil,or_false] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · cases slot : d.peerAllowedips.root4 with
      | none => rfl
      | some id =>
        obtain ⟨n,stored,four,_⟩ := roots id (.inl slot)
        simp only [stored,beq_iff_eq]
        exact four slot
    · cases slot : d.peerAllowedips.root6 with
      | none => rfl
      | some id =>
        obtain ⟨n,stored,_,six⟩ := roots id (.inr slot)
        simp only [stored,beq_iff_eq]
        exact six slot

theorem ordered_peer_present {L : Layout} {A : Allocator} {w : World} {m : Mem 64} {d : Device} {pid peer : Nat}
    (related : Related L A w m) (device : w.wg.dev = some d)
    (address : Trie.address L.peers (some pid) = .ok peer) : ∃ p, d.peers.get? pid = some p := by
  obtain ⟨names,stream,_,peers,asserted,_⟩ := related
  obtain ⟨d',device',corresponds,_⟩ := assertAt_ok asserted
  have same : d' = d := Option.some.inj (device'.symm.trans device)
  subst d'
  simp only [Trie.address] at address
  cases found : L.peers.find? (·.1 == pid) with
  | none => simp [found] at address
  | some pair =>
    obtain ⟨id,a⟩ := pair
    have identity : id = pid := by simpa using List.find?_some found
    subst id
    have named : (pid,a) ∈ names.trie.peers := peers ▸ List.mem_of_find?_eq_some found
    obtain ⟨p,stored,_⟩ := named_peer_count corresponds.trie named "peer.refcount"
    exact ⟨p,stored⟩

theorem ordered_key_bound {m : Mem 64} {base : BitVec 64} {family key : Nat}
    (checked : Trie.networkKeyCheck m base (if family == 4 then 32 else 128) key = true) :
    key < 2^widthOf family := by
  unfold Trie.networkKeyCheck at checked
  unfold widthOf
  by_cases four : (family == 4) = true
  · simp only [four,↓reduceIte,beq_self_eq_true] at checked ⊢
    split at checked
    · cases checked
    · rename_i word _
      have equal := eq_of_beq checked
      have bound := (Binary.Allowedips.swap32 word).isLt
      omega
  · simp only [four,↓reduceIte,Bool.false_eq_true] at checked ⊢
    have wide : ((128 : Nat) == 32) = false := by decide
    simp only [wide,Bool.false_eq_true,↓reduceIte] at checked
    split at checked
    · rename_i high low _ _
      have equal := eq_of_beq checked
      have highBound := (Binary.Allowedips.swap64 high).isLt
      have lowBound := (Binary.Allowedips.swap64 low).isLt
      omega
    · cases checked

theorem ordered_ready_facts {L : Layout} {A : Allocator} {c : Binary.CommonBitsCoverage.Context}
    {s : MachineState} {family key cidr pid : Nat} {ra : UInt64}
    (ready : insertReady L A c s family key cidr pid ra = .ok ()) :
    (family = 4 ∨ family = 6) ∧ key < 2^widthOf family ∧
      ∃ peer, Trie.address L.peers (some pid) = .ok peer ∧ peer ≠ 0 := by
  unfold insertReady at ready
  obtain ⟨families,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨_,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨_,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨peer,address,ready⟩ := bind_ok ready
  obtain ⟨nonNull,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨_,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨keyChecked,ready⟩ := require_bind_ok _ _ _ _ ready
  refine ⟨by simpa using families,ordered_key_bound keyChecked,peer,address,?_⟩
  have parts : peer ≠ 0 ∧ s.data.regs.rcx.toNat = peer := by simpa using nonNull
  exact parts.1

theorem ordered_clean {L : Layout} {A : Allocator} {w : World} {m : Mem 64} (related : Related L A w m) :
    ∃ stream, w.ambient.hidden = some stream ∧ (∀ r ∈ stream, HiddenSite.passive r.site = false) ∧
      w.ambient.allocArmed.contains "allocNode190" = true ∧
      w.ambient.allocArmed.contains "allocNode205" = true ∧
      w.ambient.allocArmed.contains "allocNode234" = true := by
  obtain ⟨names,stream,_,_,_,isArmed,hidden,sites,_⟩ := related
  refine ⟨stream,hidden,?_,?_⟩
  · intro r member
    have site := sites r member
    have cases : r.site = 78 ∨ r.site = 79 ∨ r.site = 77 := by simpa [allocSites] using site
    obtain ⟨p77,p78,p79⟩ := passive_sites
    rcases cases with h | h | h <;> rw [h] <;> assumption
  · simpa [armed] using isArmed

#print axioms ordered_of_related
#print axioms ordered_peer_present
#print axioms ordered_ready_facts
#print axioms ordered_clean

/-! ## The two exclusions, from the headline -/

/-! ## The exclusions, from the headline with the invariant fixed -/

/-- An ambient primitive lifted into a state layer leaves that state alone
(adapted from the T4 trial's `lift_state`). -/
theorem excl_lift_acc {σ α : Type} {x : AmbientM α} {s s1 : σ} {a a1 : Ambient} {v : α}
    (h : ((monadLift x : StateT σ AmbientM α).run s).run a = .ok ((v,s1),a1)) :
    s1 = s ∧ x.run a = .ok (v,a1) := by
  have unfolded : ((monadLift x : StateT σ AmbientM α).run s).run a =
      (x.run a >>= fun p => pure ((p.1,s),p.2)) := rfl
  rw [unfolded] at h
  cases hx : x.run a with
  | error e => rw [hx] at h; cases h
  | ok p => rw [hx] at h; cases h; exact ⟨rfl,rfl⟩

theorem excl_branch_run (dcn : Decision) (b : Bool) (g : WGWorld) (a : Ambient) :
    ((branch dcn b : WG.M Bool).run g).run a = .ok ((b,g),Model.record a dcn b) := rfl

theorem excl_branchCmp_run (dcn : Decision) (b : Bool) (x y : Int) (g : WGWorld) (a : Ambient) :
    ((branchCmp dcn b x y : WG.M Bool).run g).run a = .ok ((b,g),Placement.recordCmp a dcn b x y) := rfl

theorem excl_slotGet_run (g : WGWorld) (a : Ambient) (d : Device) (device : g.dev = some d) (v4 : Bool) :
    ((liftM (slotGet (Model.rootSlot v4)) : WG.M (Option NodeId)).run g).run a =
      .ok ((Model.rootValue d v4,g),a) := by
  change ((WG.liftAip (slotGet (Model.rootSlot v4))).run g).run a = _
  rw [Model.liftAip_run, device]
  cases v4
  · change Except.ok ((d.peerAllowedips.root6,{g with dev := some d}),a) = _
    rw [← device]; rfl
  · change Except.ok ((d.peerAllowedips.root4,{g with dev := some d}),a) = _
    rw [← device]; rfl

theorem excl_connectNode_run (store : AipStore) (v4 : Bool) (id : NodeId) (n : AipNode)
    (hn : store.nodes[id]? = some n) (a : Ambient) :
    ((connectNode (Model.rootSlot v4) id).run store).run a =
      .ok (((),{store with
        nodes := store.nodes.insert id {n with parent := Model.rootSlot v4},
        trie := if v4 then {store.trie with root4 := some id} else {store.trie with root6 := some id}}),a) := by
  cases v4 <;> simp [connectNode,getNode,setNode,slotSet,hn,Model.rootSlot] <;> rfl

theorem excl_connect_lifted (g : WGWorld) (d2 : Device) (dev : g.dev = some d2) (v4 : Bool) (id : NodeId)
    (n : AipNode) (hn : d2.nodes[id]? = some n) (a : Ambient) :
    ((liftM (connectNode (Model.rootSlot v4) id) : WG.M Unit).run g).run a =
      .ok (((),{g with dev := some {d2 with
        nodes := d2.nodes.insert id {n with parent := Model.rootSlot v4},
        peerAllowedips := if v4 then {d2.peerAllowedips with root4 := some id}
          else {d2.peerAllowedips with root6 := some id}}}),a) := by
  change ((WG.liftAip (connectNode (Model.rootSlot v4) id)).run g).run a = _
  rw [Model.liftAip_run, dev]
  simp only [excl_connectNode_run ⟨d2.nodes,d2.nextNode,d2.peerAllowedips⟩ v4 id n hn a]
  rfl

/-- The allocation at :190 on an accepted run: the head record decides. -/
theorem excl_allocNode_acc {n : AipNode} {store s' : AipStore} {a a' : Ambient}
    {out : Option NodeId} {r : HiddenRecord} {rest : List HiddenRecord}
    (hid : a.hidden = some (r :: rest)) (arm : a.allocArmed.contains "allocNode190" = true)
    (clean : HiddenSite.passive r.site = false)
    (h : ((allocNode .allocNode190 n).run store).run a = .ok ((out,s'),a')) :
    (r.bytes.head? = some 0 ∧ out = none ∧ s' = store) ∨ (r.bytes.head? = some 1 ∧ out = some store.nextNode ∧
      s' = {store with nextNode := store.nextNode+1, nodes := store.nodes.insert store.nextNode n}) := by
  unfold allocNode at h
  obtain ⟨b,s1,a1,hb,h2⟩ := bind_ok_run h
  clear h
  obtain ⟨same,consumed⟩ := excl_lift_acc hb
  clear hb
  subst same
  obtain ⟨_,byte,rfl,_⟩ := hiddenAlloc_accepted (.inl rfl) hid arm clean consumed
  rcases byte with zero | one
  · simp only [zero] at h2
    obtain ⟨rfl,rfl,_⟩ := ok_inj h2 none s1 a1 rfl
    exact .inl ⟨zero,rfl,rfl⟩
  · simp only [one] at h2
    obtain ⟨rfl,rfl,_⟩ := ok_inj h2 (some s1.nextNode)
      {s1 with nextNode := s1.nextNode+1, nodes := s1.nodes.insert s1.nextNode n} a1 rfl
    exact .inr ⟨one,rfl,rfl⟩


/-- An accepted run of the mirror's `add` at an empty root with a prefix in
range (adapted from the T4 trial's `add_source_cases`): the head record's
outcome byte decides between `-ENOMEM` with the world unchanged and 0 with
the new root installed. -/
theorem excl_add_empty (g g' : WGWorld) (a a' : Ambient) (d : Device) (device : g.dev = some d)
    (v4 : Bool) (key cidr pid : Nat) (res : Int) (empty : Model.rootValue d v4 = none)
    {r : HiddenRecord} {rest : List HiddenRecord}
    (hid : a.hidden = some (r :: rest)) (arm : a.allocArmed.contains "allocNode190" = true)
    (clean : HiddenSite.passive r.site = false) (short : cidr ≤ Model.rootWidth v4)
    (run : ((WG.add (Model.rootSlot v4) (Model.rootWidth v4) key cidr (some pid)).run g).run a =
      .ok ((res,g'),a')) :
    (r.bytes.head? = some 0 ∧ res = -ENOMEM ∧ g' = g) ∨
    (r.bytes.head? = some 1 ∧ res = 0 ∧ ∃ owner, d.peers[pid]? = some owner ∧
      g'.dev = some (Model.emptyInstalled d v4 key cidr pid owner)) := by
  unfold WG.add at run
  obtain ⟨b1,g1,a1,h1,run1⟩ := bind_ok_run run
  clear run
  obtain ⟨rfl,rfl,rfl⟩ := ok_inj h1 _ _ _
    (excl_branchCmp_run .addCidrTooLong (decide (cidr > Model.rootWidth v4)) cidr (Model.rootWidth v4) g a)
  clear h1
  have notLong : ¬cidr > Model.rootWidth v4 := by omega
  simp only [notLong,decide_false,Bool.false_eq_true,↓reduceIte] at run1
  obtain ⟨b2,g2,a2,h2,run2⟩ := bind_ok_run run1
  clear run1
  obtain ⟨rfl,rfl,rfl⟩ := ok_inj h2 _ _ _ (excl_branch_run .addNoPeer (some pid).isNone g _)
  clear h2
  simp only [Option.isNone_some,Bool.false_eq_true,↓reduceIte] at run2
  obtain ⟨trie,g3,a3,h3,run3⟩ := bind_ok_run run2
  clear run2
  obtain ⟨rfl,rfl,rfl⟩ := ok_inj h3 _ _ _ (excl_slotGet_run g _ d device v4)
  clear h3
  obtain ⟨b4,g4,a4,h4,run4⟩ := bind_ok_run run3
  clear run3
  obtain ⟨rfl,rfl,rfl⟩ := ok_inj h4 _ _ _ (excl_branch_run .addEmptyTrie (Model.rootValue d v4).isNone g _)
  clear h4
  simp only [empty,Option.isNone_none,↓reduceIte] at run4
  obtain ⟨x,g5,a5,h5,run5⟩ := bind_ok_run run4
  clear run4
  obtain ⟨out,g6,a6,h6,h7⟩ := bind_ok_run h5
  clear h5
  obtain ⟨b7,g7,a7,h8,h9⟩ := bind_ok_run h7
  clear h7
  obtain ⟨rfl,rfl,rfl⟩ := ok_inj h8 _ _ _ (excl_branch_run .addRootNoMem out.isNone g6 a6)
  clear h8
  obtain ⟨s',inner,rfl⟩ := liftAip_acc device h6
  clear h6
  rcases excl_allocNode_acc (by exact hid) (by exact arm) clean inner with ⟨zero,rfl,rfl⟩ | ⟨one,rfl,rfl⟩
  · obtain ⟨rfl,rfl,rfl⟩ := ok_inj h9 none _ _ rfl
    obtain ⟨rfl,rfl,_⟩ := ok_inj run5 (-ENOMEM) _ _ rfl
    exact .inl ⟨zero,rfl,world_same device⟩
  · obtain ⟨rfl,rfl,rfl⟩ := ok_inj h9 (some d.nextNode) _ _ rfl
    clear h9 inner
    obtain ⟨u,g8,a8,h10,run8⟩ := bind_ok_run run5
    clear run5
    cases hp : d.peers[pid]? with
    | none =>
      simp [WG.listAddTail,WG.getPeer,WG.getDev,invariant,AmbientM.invariant,hp,asDev,Source.Aip.store] at h10
      cases h10
    | some owner =>
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj h10 _ _ _
        (Model.listAddTail_run _ _ _ rfl pid d.nextNode owner (by exact hp))
      clear h10
      obtain ⟨u2,g9,a9,h11,run9⟩ := bind_ok_run run8
      clear run8
      have hn : (d.nodes.insert d.nextNode (newNode key cidr (Model.rootWidth v4) (some pid)))[d.nextNode]? =
          some (newNode key cidr (Model.rootWidth v4) (some pid)) := by simp
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj h11 _ _ _
        (excl_connect_lifted _ _ rfl v4 d.nextNode _ (by exact hn) _)
      clear h11
      obtain ⟨rfl,rfl,_⟩ := ok_inj run9 0 _ _ rfl
      refine .inr ⟨one,rfl,owner,rfl,?_⟩
      cases v4 <;> rfl


/-- The accepted insertion at an empty table whose next record is an
allocation outcome: refused and both roots still empty, or 0 with the
family's root the new node. -/
theorem excl_insert {w w' : World} {d d' : Device} {family key cidr pid : Nat} {answer : Int}
    {r : HiddenRecord} {rest : List HiddenRecord}
    (device : w.wg.dev = some d) (r4 : d.peerAllowedips.root4 = none) (r6 : d.peerAllowedips.root6 = none)
    (hid : w.ambient.hidden = some (r :: rest)) (clean : HiddenSite.passive r.site = false)
    (armedW : armed w = true) (short : cidr ≤ Model.rootWidth (family == 4))
    (run : (liftWG (WG.insert family key cidr pid)).run w = .ok (answer,w'))
    (device' : w'.wg.dev = some d') :
    (r.bytes.head? = some 0 ∧ answer = -ENOMEM ∧ Model.rootValue d' (family == 4) = none) ∨
    (r.bytes.head? = some 1 ∧ answer = 0 ∧ Model.rootValue d' (family == 4) = some d.nextNode ∧
      d'.nodes.get? d.nextNode = some {newNode key cidr (Model.rootWidth (family == 4)) (some pid) with
        parent := Model.rootSlot (family == 4)}) := by
  have arm : w.ambient.allocArmed.contains "allocNode190" = true := by
    simp only [armed,List.all_cons,Bool.and_eq_true] at armedW
    exact armedW.1
  have unfolded : (liftWG (WG.insert family key cidr pid)).run w =
      (((WG.insert family key cidr pid).run w.wg).run w.ambient >>= fun p =>
        pure (p.1.1,{w with wg := p.1.2, ambient := p.2})) := rfl
  rw [unfolded] at run
  cases inner : ((WG.insert family key cidr pid).run w.wg).run w.ambient with
  | error e => rw [inner] at run; cases run
  | ok p =>
    obtain ⟨⟨res,g'⟩,a'⟩ := p
    rw [inner] at run
    cases run
    change g'.dev = some d' at device'
    unfold WG.insert at inner
    obtain ⟨u,g1,a1,h1,run1⟩ := bind_ok_run inner
    clear inner
    obtain ⟨_,rfl,rfl⟩ := ok_inj h1 () _ _ rfl
    clear h1
    have dev1 : ({w.wg with dev := w.wg.dev.map fun d =>
        {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}}} : WGWorld).dev =
        some {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}} := by
      simp only [device,Option.map_some]
    cases hf : (family == 4)
    all_goals
      rw [hf] at short
      simp only [hf,Bool.false_eq_true,↓reduceIte] at run1
      have empty : Model.rootValue {d with peerAllowedips :=
          {d.peerAllowedips with seq := d.peerAllowedips.seq + 1}} (family == 4) = none := by
        rw [hf]; simp [Model.rootValue,r4,r6]
      rw [hf] at empty
      rcases excl_add_empty _ _ _ _ _ dev1 _ key cidr pid res empty (by exact hid) (by exact arm) clean short
        (by exact run1) with ⟨zero,rfl,rfl⟩ | ⟨one,rfl,owner,_,installed⟩
      · have same := Option.some.inj (device'.symm.trans dev1)
        subst same
        exact .inl ⟨zero,rfl,empty⟩
      · have same := Option.some.inj (device'.symm.trans installed)
        subst same
        refine .inr ⟨one,rfl,?_,?_⟩ <;>
          simp [Model.emptyInstalled,Model.rootWrite,Model.rootValue,Model.rootSlot,Model.rootWidth]


theorem excl_select_none (nodes : AllowedipsSource.NodeView) (bits key : Nat) :
    AllowedipsSource.select nodes none bits key = some none := rfl

/-- The mirror's selection on a trie whose root is the node just inserted
for `key`: it selects that node. -/
theorem excl_select_root (nodes : AllowedipsSource.NodeView) (id bits key cidr pid : Nat) (slot : Slot)
    (present : nodes id = some {newNode key cidr bits (some pid) with parent := slot})
    (family : bits = 32 ∨ bits = 128) (short : cidr ≤ bits) :
    AllowedipsSource.select nodes (some id) bits key = some (some id) := by
  have loop : ∀ fuel, (AllowedipsSource.selectLoop nodes bits key (fuel+2) (none,some id,none)).bind Prod.fst =
      some (some id) := by
    intro fuel
    have common : ∀ n : AipNode, n.bits = key → AllowedipsSource.commonValue n key bits = bits := by
      intro n same
      rcases family with rfl | rfl <;> simp [AllowedipsSource.commonValue,same,fls]
    have notLess : ¬bits < cidr := by omega
    by_cases full : cidr = bits
    · simp [AllowedipsSource.selectLoop,AllowedipsSource.selectStep,present,common,full,newNode]
    · have notGe : ¬cidr ≥ bits := by omega
      have index : key / 2^(bits-1-cidr) % 2 = 0 ∨ key / 2^(bits-1-cidr) % 2 = 1 := by omega
      rcases index with index | index <;>
        simp [AllowedipsSource.selectLoop,AllowedipsSource.selectStep,present,common,full,newNode,notLess,
          notGe,index]
  exact loop 128

theorem excl_ready_peer {L : Layout} {A : Allocator} {c : Context} {s : MachineState}
    {family key cidr pid peer : Nat} {ra : UInt64}
    (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (address : Trie.address L.peers (some pid) = .ok peer) : peer ≠ 0 := by
  unfold insertReady at ready
  dsimp only at ready
  obtain ⟨_,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨_,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨_,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨found,read,ready⟩ := bind_ok ready
  obtain ⟨checked,_⟩ := require_bind_ok _ _ _ _ ready
  have same : found = peer := Except.ok.inj (read.symm.trans address)
  subst same
  simp only [Bool.and_eq_true,bne_iff_ne,ne_eq] at checked
  exact checked.1

theorem exclusionOne : ExclusionOne := by
  intro headline fetch L A premises w d c s family key cidr pid peer ra stream device armedW hidden sites
    empty idle ready short address accepts
  obtain ⟨initial,framed,insertStep,lookupStep⟩ := headline fetch L A premises
  have facts := emptyTable_facts empty
  have inv : Inv L A w s.data.dmem := initial w d s.data.dmem _ device armedW hidden (by
    intro record member
    rcases List.mem_cons.mp member with rfl | later
    · decide
    · exact sites record later) empty idle
  obtain ⟨answer,w',d',found,w'',insRun,device',lookRun⟩ := accepts
  have short' : cidr ≤ Model.rootWidth (family == 4) := by simpa [Model.rootWidth] using short
  rcases excl_insert device facts.mirror4 facts.mirror6 hidden passive_sites.1 armedW short' insRun device' with
    ⟨zero,_⟩ | ⟨_,rfl,root,node⟩
  · cases zero
  have width : Model.rootWidth (family == 4) = 32 ∨ Model.rootWidth (family == 4) = 128 := by
    cases family == 4 <;> simp [Model.rootWidth]
  have selected := excl_select_root (fun id => d'.nodes.get? id) d.nextNode _ key cidr pid _ node width short'
  have foundPid : found = some pid := by
    have lookRun' : (Source.lookup (Model.rootValue d' (family == 4)) (Model.rootWidth (family == 4)) key).run w' =
        .ok (found,w'') := lookRun
    rw [root] at lookRun'
    obtain ⟨_,_,chosen,_,_,select,effect⟩ := Trie.lookup_effect device' lookRun'
    have same : chosen = some d.nextNode := Option.some.inj (select.symm.trans selected)
    subst same
    obtain ⟨n,p,_,present,owner,_,answered,_⟩ := effect
    have equal := Option.some.inj (present.symm.trans node)
    subst equal
    cases owner
    exact answered
  subst foundPid
  refine eventually_weaken _ _ _ _ ?_ (insertStep c s w w' family key cidr pid ra 0 inv ready insRun)
  rintro t ⟨returned,eax,_,inv',_⟩
  refine ⟨returned,eax,?_⟩
  rintro s' c' ra' ⟨heapSame,lookupOk⟩
  have inv'' : Inv L A w' s'.data.dmem := framed w' t.data.dmem s'.data.dmem inv' heapSame
  refine eventually_weaken _ _ _ _ ?_
    (lookupStep c' s' w' w'' d' family key ra' (some pid) peer inv'' device' lookupOk lookRun address)
  rintro t' ⟨returned',rax,_,_⟩
  exact ⟨returned',rax,excl_ready_peer ready address⟩

theorem exclusionTwo : ExclusionTwo := by
  intro headline fetch L A premises w d c s family key cidr pid ra stream device armedW hidden sites
    empty idle ready short accepts
  obtain ⟨initial,framed,insertStep,lookupStep⟩ := headline fetch L A premises
  have facts := emptyTable_facts empty
  have inv : Inv L A w s.data.dmem := initial w d s.data.dmem _ device armedW hidden (by
    intro record member
    rcases List.mem_cons.mp member with rfl | later
    · decide
    · exact sites record later) empty idle
  obtain ⟨answer,w',d',found,w'',insRun,device',lookRun⟩ := accepts
  have short' : cidr ≤ Model.rootWidth (family == 4) := by simpa [Model.rootWidth] using short
  rcases excl_insert device facts.mirror4 facts.mirror6 hidden passive_sites.1 armedW short' insRun device' with
    ⟨_,rfl,root⟩ | ⟨one,_⟩
  case inr => cases one
  have foundNone : found = none := by
    have lookRun' : (Source.lookup (Model.rootValue d' (family == 4)) (Model.rootWidth (family == 4)) key).run w' =
        .ok (found,w'') := lookRun
    rw [root] at lookRun'
    obtain ⟨_,_,chosen,_,_,select,effect⟩ := Trie.lookup_effect device' lookRun'
    have same : chosen = none := Option.some.inj (select.symm.trans (excl_select_none _ _ _))
    subst same
    exact effect.1
  subst foundNone
  refine eventually_weaken _ _ _ _ ?_ (insertStep c s w w' family key cidr pid ra (-ENOMEM) inv ready insRun)
  rintro t ⟨returned,eax,_,inv',_⟩
  refine ⟨returned,eax,?_⟩
  rintro s' c' ra' ⟨heapSame,lookupOk⟩
  have inv'' : Inv L A w' s'.data.dmem := framed w' t.data.dmem s'.data.dmem inv' heapSame
  refine eventually_weaken _ _ _ _ ?_
    (lookupStep c' s' w' w'' d' family key ra' none 0 inv'' device' lookupOk lookRun rfl)
  rintro t' ⟨returned',rax,_,_⟩
  exact ⟨returned',rax⟩

#print axioms exclusionOne
#print axioms exclusionTwo

/-! ## The walk facts: the induction over `nodePlacement`'s loop -/

/-! ## The walk facts: `nodePlacement`'s accepted run on an ordered trie

The arithmetic lemmas `walk_fls_le_iff` to `walk_common_split` are re-proved
here from `Leanux/Proofs/WG/AllowedIps/Prefix.lean` (the proof tree is not
importable from `binary/`). -/

theorem walk_fls_le_iff (x k : Nat) : fls x ≤ k ↔ x < 2 ^ k := by
  by_cases hx : x = 0
  · subst x
    constructor
    · intro _
      exact Nat.two_pow_pos k
    · intro _
      simp [fls]
  · simpa [fls, hx, Nat.add_one_le_iff] using (Nat.log2_lt (k := k) hx)

theorem walk_lt_pow_fls (x : Nat) : x < 2 ^ fls x :=
  (walk_fls_le_iff x _).mp (Nat.le_refl _)

theorem walk_fls_div_pow (x k : Nat) (h : x / 2 ^ k ≠ 0) :
    fls x = fls (x / 2 ^ k) + k := by
  have hupper : fls x ≤ fls (x / 2 ^ k) + k := by
    apply (walk_fls_le_iff _ _).mpr
    rw [Nat.pow_add]
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mp (walk_lt_pow_fls _)
  have hxlo : 2 ^ k ≤ x := (Nat.div_ne_zero_iff.mp h).2
  have hn : ¬ fls x ≤ k := fun hf =>
    (Nat.not_lt_of_ge hxlo) ((walk_fls_le_iff x k).mp hf)
  have hk : k ≤ fls x := by omega
  have hp : 2 ^ (fls x - k) * 2 ^ k = 2 ^ fls x := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hk]
  have hquot : x / 2 ^ k < 2 ^ (fls x - k) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).mpr
    rw [hp]
    exact walk_lt_pow_fls x
  have hlower := (walk_fls_le_iff _ _).mpr hquot
  omega

/-- The landed `common` is the width-uniform `bits - fls (a ^^^ b)` in both families. -/
theorem walk_common_eq (bits a b : Nat) (fam : bits = 32 ∨ bits = 128) :
    AllowedipsRelation.common bits a b = bits - fls (a ^^^ b) := by
  rcases fam with rfl | rfl
  · rfl
  · simp only [AllowedipsRelation.common]
    by_cases h : (a ^^^ b) / 2 ^ 64 = 0
    · have hx : (a ^^^ b) < 2 ^ 64 := (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos 64)).mp h
      simp [h, Nat.mod_eq_of_lt hx]
    · simp [h, walk_fls_div_pow (a ^^^ b) 64 h]

theorem walk_xor_eq_zero_iff (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun z => z ^^^ b) h
    simpa [Nat.xor_assoc] using this
  · rintro rfl
    simp

/-- `cidr ≤ common` is equality of the leading `cidr` bits. -/
theorem walk_common_ge_iff {bits cidr a b : Nat} (fam : bits = 32 ∨ bits = 128)
    (ha : a < 2 ^ bits) (hb : b < 2 ^ bits) (hc : cidr ≤ bits) :
    cidr ≤ AllowedipsRelation.common bits a b ↔ a / 2 ^ (bits - cidr) = b / 2 ^ (bits - cidr) := by
  have hf : fls (a ^^^ b) ≤ bits :=
    (walk_fls_le_iff _ _).mpr (Nat.xor_lt_two_pow ha hb)
  rw [walk_common_eq bits a b fam]
  calc
    cidr ≤ bits - fls (a ^^^ b) ↔ fls (a ^^^ b) ≤ bits - cidr := by omega
    _ ↔ a ^^^ b < 2 ^ (bits - cidr) := walk_fls_le_iff _ _
    _ ↔ (a ^^^ b) / 2 ^ (bits - cidr) = 0 :=
      (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).symm
    _ ↔ a / 2 ^ (bits - cidr) = b / 2 ^ (bits - cidr) := by
      rw [Nat.xor_div_two_pow, walk_xor_eq_zero_iff]

theorem walk_common_le (bits a b : Nat) (fam : bits = 32 ∨ bits = 128) :
    AllowedipsRelation.common bits a b ≤ bits := by
  rw [walk_common_eq bits a b fam]
  omega

/-- One more matching prefix bit is a matching shorter prefix and a matching branch bit. -/
theorem walk_prefix_succ_eq_iff {bits c a b : Nat} (hc : c < bits) :
    a / 2 ^ (bits - (c + 1)) = b / 2 ^ (bits - (c + 1)) ↔
      a / 2 ^ (bits - c) = b / 2 ^ (bits - c) ∧ a / 2 ^ (bits - 1 - c) % 2 = b / 2 ^ (bits - 1 - c) % 2 := by
  have shape : bits - c = bits - (c + 1) + 1 := by omega
  have same : bits - 1 - c = bits - (c + 1) := by omega
  rw [shape, same, Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  constructor
  · intro h
    rw [h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hq, hr⟩
    have ha := Nat.div_add_mod (a / 2 ^ (bits - (c + 1))) 2
    have hb := Nat.div_add_mod (b / 2 ^ (bits - (c + 1))) 2
    omega

/-- What the stop of the walk above a node gives (PLAN.md section 1, rows 3 and 5). -/
theorem walk_stop_facts {bits key cidr nb nc : Nat} (fam : bits = 32 ∨ bits = 128)
    (hk : key < 2 ^ bits) (hn : nb < 2 ^ bits) (short : cidr ≤ bits)
    (stop : cidr < nc ∨ AllowedipsRelation.common bits nb key < nc) :
    min cidr (AllowedipsRelation.common bits nb key) < nc ∧
    nb / 2 ^ (bits - min cidr (AllowedipsRelation.common bits nb key)) =
      key / 2 ^ (bits - min cidr (AllowedipsRelation.common bits nb key)) ∧
    (cidr ≤ AllowedipsRelation.common bits nb key ∨
      (AllowedipsRelation.common bits nb key < bits ∧
        nb / 2 ^ (bits - 1 - AllowedipsRelation.common bits nb key) % 2 ≠
          key / 2 ^ (bits - 1 - AllowedipsRelation.common bits nb key) % 2)) := by
  have cle := walk_common_le bits nb key fam
  refine ⟨by omega, ?_, ?_⟩
  · exact (walk_common_ge_iff fam hn hk (by omega)).mp (Nat.min_le_right _ _)
  · by_cases enough : cidr ≤ AllowedipsRelation.common bits nb key
    · exact .inl enough
    · have below : AllowedipsRelation.common bits nb key < bits := by omega
      refine .inr ⟨below, ?_⟩
      intro sameBit
      have pre := (walk_common_ge_iff fam hn hk cle).mp (Nat.le_refl _)
      have more := (walk_prefix_succ_eq_iff below).mpr ⟨pre, sameBit⟩
      have := (walk_common_ge_iff fam hn hk (by omega)).mpr more
      omega

/-- The placed node's prefix is strictly shorter than `min cidr common` (row 4). -/
theorem walk_parent_lt {bits key cidr nb pb pc : Nat} (fam : bits = 32 ∨ bits = 128)
    (hk : key < 2 ^ bits) (hn : nb < 2 ^ bits) (short : cidr ≤ bits) (shorter : pc < cidr)
    (keyPrefix : key / 2 ^ (bits - pc) = pb / 2 ^ (bits - pc))
    (childPrefix : nb / 2 ^ (bits - pc) = pb / 2 ^ (bits - pc))
    (side : nb / 2 ^ (bits - 1 - pc) % 2 = key / 2 ^ (bits - 1 - pc) % 2) :
    pc < min cidr (AllowedipsRelation.common bits nb key) := by
  have more := (walk_prefix_succ_eq_iff (a := nb) (b := key) (show pc < bits by omega)).mpr
    ⟨childPrefix.trans keyPrefix.symm, side⟩
  have := (walk_common_ge_iff fam hn hk (by omega)).mpr more
  omega

/-- The node facts of `ordered`. -/
theorem walk_ordered_node {d : Device} {id : NodeId} {n : AipNode} (trie : ordered d = true)
    (present : d.nodes.get? id = some n) :
    (n.bitlen = 32 ∨ n.bitlen = 128) ∧ n.cidr ≤ n.bitlen ∧ n.bits < 2 ^ n.bitlen ∧
    ∀ i c, n.bit[i]? = some (some c) → ∃ cn, d.nodes.get? c = some cn ∧ cn.bitlen = n.bitlen ∧
      n.cidr < cn.cidr ∧ cn.bits / 2 ^ (n.bitlen - n.cidr) = n.bits / 2 ^ (n.bitlen - n.cidr) ∧
      cn.bits / 2 ^ (n.bitlen - 1 - n.cidr) % 2 = i := by
  unfold ordered at trie
  simp only [Bool.and_eq_true, List.all_eq_true] at trie
  have member : (id,n) ∈ d.nodes.toList := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present
  have checked := trie.1 (id,n) member
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨family, prefixLength⟩, bound⟩, _⟩, children⟩ := checked
  refine ⟨family, prefixLength, bound, ?_⟩
  intro i c childAt
  have listed : (some c, i) ∈ n.bit.toList.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa using childAt
  have edge := children (some c, i) listed
  simp only at edge
  cases childNode : d.nodes.get? c with
  | none => rw [childNode] at edge; cases edge
  | some cn =>
    rw [childNode] at edge
    simp only [edgeOrdered, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at edge
    obtain ⟨⟨⟨sameFamily, longer⟩, shared⟩, side⟩ := edge
    exact ⟨cn, rfl, sameFamily, longer, shared, side⟩

/-- The root clause of `ordered`. -/
theorem walk_ordered_root {d : Device} {family : Nat} {id : NodeId} (trie : ordered d = true)
    (root : rootOf d family = some id) : ∃ n, d.nodes.get? id = some n ∧ n.bitlen = widthOf family := by
  unfold ordered at trie
  simp only [Bool.and_eq_true, List.all_eq_true] at trie
  have roots := trie.2
  unfold rootOf at root
  unfold widthOf
  by_cases four : (family == 4) = true
  · simp only [four, ↓reduceIte] at root ⊢
    have checked := roots (d.peerAllowedips.root4,32) (by simp)
    simp only [root] at checked
    cases present : d.nodes.get? id with
    | none => rw [present] at checked; cases checked
    | some n => rw [present] at checked; exact ⟨n, rfl, by simpa using checked⟩
  · simp only [four, Bool.false_eq_true, ↓reduceIte] at root ⊢
    have checked := roots (d.peerAllowedips.root6,128) (by simp)
    simp only [root] at checked
    cases present : d.nodes.get? id with
    | none => rw [present] at checked; cases checked
    | some n => rw [present] at checked; exact ⟨n, rfl, by simpa using checked⟩


/-- The loop invariant: the current node is of the family's width; if a node
has been placed, the key shares its prefix, its prefix is strictly shorter than
`cidr`, and the current node is its child on the key's side. -/
def walk_Inv (d : Device) (root : Option NodeId) (key cidr bits : Nat)
    (current parent : Option NodeId) : Prop :=
  (∀ id, current = some id → ∃ n, d.nodes.get? id = some n ∧ n.bitlen = bits) ∧
  match parent with
  | none => current = root
  | some pid => ∃ p, d.nodes.get? pid = some p ∧ p.bitlen = bits ∧ p.cidr < cidr ∧
      key / 2 ^ (bits - p.cidr) = p.bits / 2 ^ (bits - p.cidr) ∧
      current = (p.bit[key / 2 ^ (p.bitlen - 1 - p.cidr) % 2]?).join

/-- The walk's answer when it stops with nothing below. -/
theorem walk_done_empty {d : Device} {root : Option NodeId} {key cidr bits : Nat} {parent : Option NodeId}
    (inv : walk_Inv d root key cidr bits none parent) :
    walk d root key cidr bits parent false = true := by
  obtain ⟨_, placed⟩ := inv
  cases parent with
  | none =>
    simp only at placed
    simp [walk, below, ← placed]
  | some pid =>
    obtain ⟨p, present, family, shorter, keyPrefix, child⟩ := placed
    have differs : (p.cidr == cidr) = false := by simpa using Nat.ne_of_lt shorter
    have present : d.nodes[pid]? = some p := present
    rw [family] at child
    simp [walk, below, present, family, Nat.le_of_lt shorter, differs, keyPrefix, ← child]

/-- The walk's answer when it stops above a node. -/
theorem walk_done_stop {d : Device} {root : Option NodeId} {key cidr bits : Nat}
    {id : NodeId} {n : AipNode} {parent : Option NodeId}
    (trie : ordered d = true) (fam : bits = 32 ∨ bits = 128) (keyBound : key < 2 ^ bits)
    (short : cidr ≤ bits) (inv : walk_Inv d root key cidr bits (some id) parent)
    (present : d.nodes.get? id = some n)
    (stop : cidr < n.cidr ∨ AllowedipsRelation.common bits n.bits key < n.cidr) :
    walk d root key cidr bits parent false = true := by
  obtain ⟨current, placed⟩ := inv
  obtain ⟨n', present', family⟩ := current id rfl
  have same : n' = n := Option.some.inj (present'.symm.trans present)
  rw [same] at family
  obtain ⟨_, _, bound, _⟩ := walk_ordered_node trie present
  rw [family] at bound
  obtain ⟨least, agree, split⟩ := walk_stop_facts fam keyBound bound short stop
  have splitBool : (decide (cidr ≤ AllowedipsRelation.common bits n.bits key) ||
      (decide (AllowedipsRelation.common bits n.bits key < bits) &&
        (n.bits / 2 ^ (bits - 1 - AllowedipsRelation.common bits n.bits key) % 2 !=
          key / 2 ^ (bits - 1 - AllowedipsRelation.common bits n.bits key) % 2))) = true := by
    rcases split with enough | ⟨inside, differ⟩
    · simp [enough]
    · simp [inside, differ]
  have present'' : d.nodes[id]? = some n := present
  cases parent with
  | none =>
    simp only at placed
    simp [walk, below, ← placed, present'', family, least, agree, splitBool]
  | some pid =>
    obtain ⟨p, parentPresent, parentFamily, shorter, keyPrefix, child⟩ := placed
    have differs : (p.cidr == cidr) = false := by simpa using Nat.ne_of_lt shorter
    obtain ⟨_, _, _, edges⟩ := walk_ordered_node trie parentPresent
    have childAt : p.bit[key / 2 ^ (p.bitlen - 1 - p.cidr) % 2]? = some (some id) := by
      cases at_ : p.bit[key / 2 ^ (p.bitlen - 1 - p.cidr) % 2]? with
      | none => rw [at_] at child; cases child
      | some value => rw [at_] at child; simp only [Option.join_some] at child; rw [← child]
    obtain ⟨cn, childPresent, _, _, shared, side⟩ := edges _ id childAt
    have sameChild : cn = n := Option.some.inj (childPresent.symm.trans present)
    rw [sameChild, parentFamily] at shared side
    rw [parentFamily] at childAt
    have parentShorter := walk_parent_lt fam keyBound bound short shorter keyPrefix shared side
    have parentPresent : d.nodes[pid]? = some p := parentPresent
    simp [walk, below, parentPresent, parentFamily, Nat.le_of_lt shorter, differs, keyPrefix, childAt,
      present'', family, least, agree, splitBool, parentShorter]


/-- The walk's answer at a node with exactly this prefix. -/
theorem walk_done_exact {d : Device} {root : Option NodeId} {key cidr bits : Nat}
    {id : NodeId} {n : AipNode} {parent : Option NodeId}
    (trie : ordered d = true) (fam : bits = 32 ∨ bits = 128) (keyBound : key < 2 ^ bits)
    (short : cidr ≤ bits) (inv : walk_Inv d root key cidr bits (some id) parent)
    (present : d.nodes.get? id = some n)
    (matching : ¬AllowedipsRelation.common bits n.bits key < n.cidr) (exactLength : n.cidr = cidr) :
    walk d root key cidr bits (some id) true = true := by
  obtain ⟨current, _⟩ := inv
  obtain ⟨n', present', family⟩ := current id rfl
  have same : n' = n := Option.some.inj (present'.symm.trans present)
  rw [same] at family
  obtain ⟨_, _, bound, _⟩ := walk_ordered_node trie present
  rw [family] at bound
  have agree := (walk_common_ge_iff fam bound keyBound (by omega)).mp (Nat.le_of_not_lt matching)
  rw [exactLength] at agree
  have present'' : d.nodes[id]? = some n := present
  simp [walk, present'', family, exactLength, agree]

/-- One more turn of the loop keeps the invariant. -/
theorem walk_yield {d : Device} {root : Option NodeId} {key cidr bits : Nat}
    {id : NodeId} {n : AipNode} {parent next : Option NodeId}
    (trie : ordered d = true) (fam : bits = 32 ∨ bits = 128) (keyBound : key < 2 ^ bits)
    (inv : walk_Inv d root key cidr bits (some id) parent)
    (present : d.nodes.get? id = some n) (notLong : ¬cidr < n.cidr)
    (matching : ¬AllowedipsRelation.common bits n.bits key < n.cidr) (notExact : ¬n.cidr = cidr)
    (child : n.bit[key / 2 ^ (n.bitlen - 1 - n.cidr) % 2]? = some next) :
    walk_Inv d root key cidr bits next (some id) := by
  obtain ⟨current, _⟩ := inv
  obtain ⟨n', present', family⟩ := current id rfl
  have same : n' = n := Option.some.inj (present'.symm.trans present)
  rw [same] at family
  obtain ⟨_, prefixLength, bound, edges⟩ := walk_ordered_node trie present
  rw [family] at bound prefixLength
  have agree := (walk_common_ge_iff fam bound keyBound prefixLength).mp (Nat.le_of_not_lt matching)
  refine ⟨?_, n, present, family, by omega, agree.symm, by rw [child]; rfl⟩
  intro nextId isNext
  rw [isNext] at child
  obtain ⟨cn, childPresent, childFamily, _⟩ := edges _ nextId child
  exact ⟨cn, childPresent, childFamily.trans family⟩

/-- One accepted turn: it keeps the invariant or ends with the walk facts. -/
theorem walk_step {d : Device} {root : Option NodeId} {key cidr bits : Nat}
    {acc : Placement.Acc} {step : ForInStep Placement.Acc}
    (trie : ordered d = true) (fam : bits = 32 ∨ bits = 128) (keyBound : key < 2 ^ bits)
    (short : cidr ≤ bits) (inv : walk_Inv d root key cidr bits acc.2.1 acc.2.2)
    (selected : Placement.selectStep (Source.Aip.store d) key cidr bits acc = some step) :
    match step with
    | .yield next => next.1 = none ∧ walk_Inv d root key cidr bits next.2.1 next.2.2
    | .done out => ∃ placed exact, out.1 = some (placed,exact) ∧ walk d root key cidr bits placed exact = true := by
  rcases acc with ⟨answer, current, parent⟩
  cases current with
  | none =>
    cases selected
    exact ⟨parent, false, rfl, walk_done_empty inv⟩
  | some id =>
    cases present : d.nodes.get? id with
    | none =>
      have absent : (Source.Aip.store d).nodes[id]? = none := present
      simp [Placement.selectStep, absent] at selected
    | some node =>
      have here : (Source.Aip.store d).nodes[id]? = some node := present
      by_cases long : cidr < node.cidr
      · simp [Placement.selectStep, here, long] at selected
        subst selected
        exact ⟨parent, false, rfl, walk_done_stop trie fam keyBound short inv present (.inl long)⟩
      by_cases matching : AllowedipsRelation.common bits node.bits key < node.cidr
      · simp [Placement.selectStep, here, long, matching] at selected
        subst selected
        exact ⟨parent, false, rfl, walk_done_stop trie fam keyBound short inv present (.inr matching)⟩
      by_cases exactLength : node.cidr = cidr
      · have matching' : ¬AllowedipsRelation.common bits node.bits key < cidr := exactLength ▸ matching
        simp [Placement.selectStep, here, matching', exactLength] at selected
        subst selected
        exact ⟨some id, true, rfl, walk_done_exact trie fam keyBound short inv present matching exactLength⟩
      by_cases invalid : node.cidr ≥ node.bitlen
      · simp [Placement.selectStep, here, long, matching, exactLength, invalid] at selected
      cases child : node.bit[key / 2 ^ (node.bitlen - 1 - node.cidr) % 2]? with
      | none => simp [Placement.selectStep, here, long, matching, exactLength, invalid, child] at selected
      | some next =>
        simp [Placement.selectStep, here, long, matching, exactLength, invalid, child] at selected
        subst selected
        exact ⟨rfl, walk_yield trie fam keyBound inv present long matching exactLength child⟩


theorem walk_commonRecords_kept (a : Ambient) (width x : Nat) :
    (Model.commonRecords a width x).hidden = a.hidden ∧
      (Model.commonRecords a width x).allocArmed = a.allocArmed := by
  unfold Model.commonRecords
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

/-- An accepted turn of the loop writes only decision records. -/
theorem walk_iteration_ambient {key cidr bits : Nat} {acc : Placement.Acc} {store st' : AipStore}
    {a a' : Ambient} {step : ForInStep Placement.Acc}
    (run : ((Placement.iteration key cidr bits acc).run store).run a = .ok ((step,st'),a')) :
    a'.hidden = a.hidden ∧ a'.allocArmed = a.allocArmed := by
  rcases acc with ⟨answer, current, parent⟩
  cases current with
  | none => cases run; exact ⟨rfl, rfl⟩
  | some id =>
    cases present : store.nodes[id]? with
    | none =>
      simp [Placement.iteration, getNode, StateT.run_bind, Placement.branch_run,
        Source.except_ok_bind, present, invariant] at run
      cases run
    | some node =>
      by_cases long : cidr < node.cidr <;>
        by_cases matching : AllowedipsRelation.common bits node.bits key < node.cidr <;>
        by_cases exactLength : node.cidr = cidr <;>
        by_cases invalid : node.cidr ≥ node.bitlen <;>
        cases child : node.bit[key / 2 ^ (node.bitlen - 1 - node.cidr) % 2]?
      all_goals try simp only [exactLength] at long matching invalid child
      all_goals simp [Placement.iteration, getNode, StateT.run_bind, StateT.run_pure, Placement.branch_run,
        Placement.branchCmp_run, Source.except_ok_bind, Source.except_pure, Placement.prefix_run, present,
        choose, AipNode.bitAt, invariant, long, matching, exactLength, invalid, child] at run
      all_goals
        rcases run with ⟨⟨-, -⟩, rfl⟩ <;>
        exact ⟨by simp [(walk_commonRecords_kept _ _ _).1, Placement.recordCmp, Model.record],
          by simp [(walk_commonRecords_kept _ _ _).2, Placement.recordCmp, Model.record]⟩

/-- The bounded loop: every accepted prefix of turns keeps the store, writes
only decision records, and either is still open under the invariant or has
ended with the walk facts. -/
theorem walk_loop {d : Device} {root : Option NodeId} {key cidr bits : Nat}
    (trie : ordered d = true) (fam : bits = 32 ∨ bits = 128) (keyBound : key < 2 ^ bits)
    (short : cidr ≤ bits) (items : List Nat) :
    ∀ (acc : Placement.Acc) (a : Ambient) (out : Placement.Acc) (st' : AipStore) (a' : Ambient),
      ((forIn items acc (fun (_ : Nat) => Placement.iteration key cidr bits)).run (Source.Aip.store d)).run a =
        .ok ((out,st'),a') →
      acc.1 = none → walk_Inv d root key cidr bits acc.2.1 acc.2.2 →
      st' = Source.Aip.store d ∧ a'.hidden = a.hidden ∧ a'.allocArmed = a.allocArmed ∧
        (out.1 = none ∨ ∃ placed exact, out.1 = some (placed,exact) ∧
          walk d root key cidr bits placed exact = true) := by
  induction items with
  | nil =>
    intro acc a out st' a' run opened _
    cases run
    exact ⟨rfl, rfl, rfl, .inl opened⟩
  | cons x xs ih =>
    intro acc a out st' a' run opened inv
    simp only [List.forIn_cons] at run
    obtain ⟨step, s1, a1, turn, rest⟩ := bind_ok_run run
    clear run
    obtain ⟨selected, rfl⟩ := Placement.iteration_accepted turn
    obtain ⟨hidden, armed⟩ := walk_iteration_ambient turn
    have facts := walk_step trie fam keyBound short inv selected
    cases step with
    | done value =>
      cases rest
      exact ⟨rfl, hidden, armed, .inr facts⟩
    | yield next =>
      obtain ⟨stillOpen, nextInv⟩ := facts
      obtain ⟨same, hidden', armed', result⟩ := ih next a1 out st' a' rest stillOpen nextInv
      exact ⟨same, hidden'.trans hidden, armed'.trans armed, result⟩

/-- THE WALK FACTS. An accepted `nodePlacement` from the family's root of an
ordered trie returns a placement with `C1Invariant.walk`'s facts, leaves the
component store alone, and keeps the pending records and the armed sites. -/
theorem walk_of_run {d : Device} {family key cidr : Nat} {placed : Option NodeId} {exact : Bool}
    {a a' : Ambient} {s' : AipStore} (trie : ordered d = true) (families : family = 4 ∨ family = 6)
    (keyBound : key < 2^widthOf family) (short : cidr ≤ widthOf family)
    (run : ((WG.nodePlacement (rootOf d family) key cidr (widthOf family)).run (Source.Aip.store d)).run a =
      .ok (((placed,exact),s'),a')) :
    walk d (rootOf d family) key cidr (widthOf family) placed exact = true ∧ s' = Source.Aip.store d ∧
      a'.hidden = a.hidden ∧ a'.allocArmed = a.allocArmed := by
  have fam : widthOf family = 32 ∨ widthOf family = 128 := by
    rcases families with rfl | rfl
    · exact .inl rfl
    · exact .inr rfl
  rw [← Placement.run_eq_source] at run
  unfold Placement.run at run
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at run
  obtain ⟨acc, s1, a1, looped, rest⟩ := bind_ok_run run
  clear run
  have initial : walk_Inv d (rootOf d family) key cidr (widthOf family) (rootOf d family) none :=
    ⟨fun id isRoot => walk_ordered_root trie isRoot, rfl⟩
  obtain ⟨rfl, hidden, armed, result⟩ := walk_loop trie fam keyBound short _ (none, rootOf d family, none)
    a acc s1 a1 looped rfl initial
  cases answer : acc.1 with
  | none =>
    rw [answer] at rest
    cases rest
  | some value =>
    rw [answer] at rest
    cases rest
    rcases result with stillOpen | ⟨placed', exact', found, facts⟩
    · rw [answer] at stillOpen
      cases stillOpen
    · rw [answer] at found
      cases found
      exact ⟨facts, rfl, hidden, armed⟩

#print axioms walk_of_run

/-! ## An accepted run of the mirror's insertion as `C1Step.step` -/

/-! ## An accepted `WG.insert` is `C1Step.step` -/

structure add_Ready (a : Ambient) (stream : List HiddenRecord) : Prop where
  hidden : a.hidden = some stream
  clean : ∀ r ∈ stream, HiddenSite.passive r.site = false
  armed190 : a.allocArmed.contains "allocNode190" = true
  armed205 : a.allocArmed.contains "allocNode205" = true
  armed234 : a.allocArmed.contains "allocNode234" = true

theorem add_Ready.keep {a a' : Ambient} {stream : List HiddenRecord} (ready : add_Ready a stream)
    (hidden : a'.hidden = a.hidden) (armed : a'.allocArmed = a.allocArmed) : add_Ready a' stream :=
  ⟨hidden.trans ready.hidden,ready.clean,armed ▸ ready.armed190,armed ▸ ready.armed205,armed ▸ ready.armed234⟩

theorem add_Ready.next {a : Ambient} {r : HiddenRecord} {rest : List HiddenRecord}
    (ready : add_Ready a (r :: rest)) : add_Ready {a with hidden := some rest} rest :=
  ⟨rfl,fun x member => ready.clean x (List.mem_cons_of_mem _ member),ready.armed190,ready.armed205,ready.armed234⟩

@[simp] theorem add_record_hidden (a : Ambient) (dcn : Decision) (b : Bool) :
    (Model.record a dcn b).hidden = a.hidden := rfl
@[simp] theorem add_record_armed (a : Ambient) (dcn : Decision) (b : Bool) :
    (Model.record a dcn b).allocArmed = a.allocArmed := rfl
@[simp] theorem add_recordCmp_hidden (a : Ambient) (dcn : Decision) (b : Bool) (x y : Int) :
    (Placement.recordCmp a dcn b x y).hidden = a.hidden := rfl
@[simp] theorem add_recordCmp_armed (a : Ambient) (dcn : Decision) (b : Bool) (x y : Int) :
    (Placement.recordCmp a dcn b x y).allocArmed = a.allocArmed := rfl
@[simp] theorem add_commonRecords_hidden (a : Ambient) (width x : Nat) :
    (Model.commonRecords a width x).hidden = a.hidden := by
  unfold Model.commonRecords
  dsimp only
  split
  · rfl
  · split <;> rfl
@[simp] theorem add_commonRecords_armed (a : Ambient) (width x : Nat) :
    (Model.commonRecords a width x).allocArmed = a.allocArmed := by
  unfold Model.commonRecords
  dsimp only
  split
  · rfl
  · split <;> rfl

/-- An ambient primitive lifted into a state layer (after the T4 trial's `lift_state`). -/
theorem add_lift_amb {σ α : Type} {x : AmbientM α} {s s1 : σ} {a a1 : Ambient} {v : α}
    (h : ((monadLift x : StateT σ AmbientM α).run s).run a = .ok ((v,s1),a1)) :
    s1 = s ∧ x.run a = .ok (v,a1) := by
  have unfolded : ((monadLift x : StateT σ AmbientM α).run s).run a =
      (x.run a >>= fun p => pure ((p.1,s),p.2)) := rfl
  rw [unfolded] at h
  cases hx : x.run a with
  | error e => rw [hx] at h; cases h
  | ok p => rw [hx] at h; cases h; exact ⟨rfl,rfl⟩

theorem add_iteration_kept (key cidr bits : Nat) (acc : Placement.Acc) (store : AipStore) (a : Ambient) :
    match ((Placement.iteration key cidr bits acc).run store).run a with
    | .ok r => r.2.hidden = a.hidden ∧ r.2.allocArmed = a.allocArmed
    | .error _ => True := by
  rcases acc with ⟨answer,current,parent⟩
  cases current with
  | none => exact ⟨rfl,rfl⟩
  | some id =>
    cases present : store.nodes[id]? with
    | none =>
      simp [Placement.iteration,getNode,StateT.run_bind,Placement.branch_run,
        Source.except_ok_bind,present,invariant]
      exact True.intro
    | some node =>
      by_cases long : cidr<node.cidr <;>
        by_cases matching : AllowedipsRelation.common bits node.bits key<node.cidr <;>
        by_cases exactLength : node.cidr=cidr <;>
        by_cases invalid : node.cidr≥node.bitlen <;>
        cases child : node.bit[key/2^(node.bitlen-1-node.cidr)%2]?
      all_goals try simp only [exactLength] at long matching invalid child
      all_goals simp [Placement.iteration,getNode,StateT.run_bind,StateT.run_pure,Placement.branch_run,
        Placement.branchCmp_run,Source.except_ok_bind,Source.except_pure,Placement.prefix_run,present,choose,
        AipNode.bitAt,invariant,long,matching,exactLength,invalid,child]
      all_goals first | exact True.intro | exact ⟨rfl,rfl⟩


/-- The walk's cursor is the node below its remembered parent. -/
def add_Link (d : Device) (root : Option NodeId) (key : Nat) (current parent : Option NodeId) : Prop :=
  match parent with
  | none => current = root
  | some p => ∃ pn, d.nodes.get? p = some pn ∧ current = (pn.bit[key / 2^(pn.bitlen-1-pn.cidr) % 2]?).join

/-- What the rest of `add` needs of a returned placement: the placed node is stored and, when the
walk was not exact, so is the node below it (the walk read it). -/
def add_Good (d : Device) (root : Option NodeId) (key : Nat) (placed : Option NodeId) (exact : Bool) : Prop :=
  (∀ p, placed = some p → ∃ pn, d.nodes.get? p = some pn) ∧
  (exact = false → ∀ id, below d root key placed = some id → ∃ n, d.nodes.get? id = some n)

theorem add_Link.below {d : Device} {root : Option NodeId} {key : Nat} {current parent : Option NodeId}
    (link : add_Link d root key current parent) : below d root key parent = current := by
  cases parent with
  | none => exact link.symm
  | some p =>
    obtain ⟨pn,present,rfl⟩ := link
    simp only [Proof.below,present]

theorem add_Link.placed {d : Device} {root : Option NodeId} {key : Nat} {current parent : Option NodeId}
    (link : add_Link d root key current parent) : ∀ p, parent = some p → ∃ pn, d.nodes.get? p = some pn := by
  rintro p rfl
  obtain ⟨pn,present,_⟩ := link
  exact ⟨pn,present⟩

theorem add_good_stop {d : Device} {root : Option NodeId} {key : Nat} {current parent : Option NodeId}
    (link : add_Link d root key current parent)
    (stored : ∀ id, current = some id → ∃ n, d.nodes.get? id = some n) :
    ∀ res : Option NodeId × Bool, some (parent,false) = some res → add_Good d root key res.1 res.2 := by
  intro res same
  cases same
  refine ⟨link.placed,fun _ id reached => ?_⟩
  rw [link.below] at reached
  exact stored id reached

theorem add_good_exact {d : Device} {root : Option NodeId} {key : Nat} {id : NodeId} {node : AipNode}
    (present : d.nodes.get? id = some node) :
    ∀ res : Option NodeId × Bool, some (some id,true) = some res → add_Good d root key res.1 res.2 := by
  intro res same
  cases same
  refine ⟨?_,fun wrong => by cases wrong⟩
  rintro p ⟨rfl⟩
  exact ⟨node,present⟩

theorem add_select {d : Device} {root : Option NodeId} {key cidr bits : Nat} {acc : Placement.Acc}
    {step : ForInStep Placement.Acc} (link : add_Link d root key acc.2.1 acc.2.2)
    (selected : Placement.selectStep (Source.Aip.store d) key cidr bits acc = some step) :
    match step with
    | .done b => ∀ res, b.1 = some res → add_Good d root key res.1 res.2
    | .yield b => b.1 = none ∧ add_Link d root key b.2.1 b.2.2 := by
  rcases acc with ⟨answer,current,parent⟩
  cases current with
  | none =>
    cases selected
    exact add_good_stop link (fun id wrong => by cases wrong)
  | some id =>
    cases present : (Source.Aip.store d).nodes[id]? with
    | none => simp [Placement.selectStep,present] at selected
    | some node =>
      have present' : d.nodes.get? id = some node := present
      have stop := add_good_stop (d := d) (root := root) (key := key) link
        (fun id' same => by cases same; exact ⟨node,present'⟩)
      by_cases long : cidr<node.cidr <;>
        by_cases matching : AllowedipsRelation.common bits node.bits key<node.cidr <;>
        by_cases exactLength : node.cidr=cidr <;>
        by_cases invalid : node.cidr≥node.bitlen <;>
        cases child : node.bit[key/2^(node.bitlen-1-node.cidr)%2]?
      all_goals try simp only [exactLength] at long matching invalid child
      all_goals simp [Placement.selectStep,present,long,matching,exactLength,invalid,child] at selected
      all_goals cases selected
      all_goals first
        | exact stop
        | exact add_good_exact present'
        | exact ⟨rfl,node,present',by rw [child]; rfl⟩


theorem add_loop {d : Device} {root : Option NodeId} {key cidr bits : Nat} (xs : List Nat) :
    ∀ (acc acc' : Placement.Acc) (a a' : Ambient) (s' : AipStore), acc.1 = none →
      add_Link d root key acc.2.1 acc.2.2 →
      ((forIn xs acc (fun _ => Placement.iteration key cidr bits)).run (Source.Aip.store d)).run a =
        .ok ((acc',s'),a') →
      s' = Source.Aip.store d ∧ a'.hidden = a.hidden ∧ a'.allocArmed = a.allocArmed ∧
        ∀ res, acc'.1 = some res → add_Good d root key res.1 res.2 := by
  induction xs with
  | nil =>
    intro acc acc' a a' s' opened link run
    obtain ⟨rfl,rfl,rfl⟩ := ok_inj run _ _ _ rfl
    exact ⟨rfl,rfl,rfl,fun res found => by rw [opened] at found; cases found⟩
  | cons x xs ih =>
    intro acc acc' a a' s' opened link run
    simp only [List.forIn_cons] at run
    obtain ⟨step,s1,a1,first,rest⟩ := bind_ok_run run
    clear run
    obtain ⟨selected,rfl⟩ := Placement.iteration_accepted first
    have kept := add_iteration_kept key cidr bits acc (Source.Aip.store d) a
    rw [first] at kept
    have next := add_select link selected
    cases step with
    | done b =>
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj rest _ _ _ rfl
      exact ⟨rfl,kept.1,kept.2,next⟩
    | yield b =>
      obtain ⟨same,hidden,armed,good⟩ := ih b acc' a1 a' s' next.1 next.2 rest
      exact ⟨same,hidden.trans kept.1,armed.trans kept.2,good⟩

theorem add_placement {d : Device} {root placed : Option NodeId} {key cidr bits : Nat} {exact : Bool}
    {s' : AipStore} {a a' : Ambient}
    (run : ((WG.nodePlacement root key cidr bits).run (Source.Aip.store d)).run a = .ok (((placed,exact),s'),a')) :
    s' = Source.Aip.store d ∧ a'.hidden = a.hidden ∧ a'.allocArmed = a.allocArmed ∧
      add_Good d root key placed exact := by
  rw [← Placement.run_eq_source] at run
  unfold Placement.run at run
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at run
  obtain ⟨acc,s1,a1,loop,rest⟩ := bind_ok_run run
  clear run
  obtain ⟨rfl,hidden,armed,good⟩ := add_loop (d := d) (root := root) (key := key) _ (none,root,none) acc a a1 s1 rfl
    (show add_Link d root key root none from rfl) loop
  cases found : acc.1 with
  | none => simp only [found] at rest; cases rest
  | some res =>
    simp only [found] at rest
    have g := good res found
    obtain ⟨same,rfl,rfl⟩ := ok_inj rest res _ _ rfl
    cases same
    exact ⟨rfl,hidden,armed,g⟩


theorem add_hiddenAlloc_nil {s : AllocSite} {a a' : Ambient} {b : Bool}
    (site : s = .allocNode190 ∨ s = .allocNode205 ∨ s = .allocNode234)
    (hid : a.hidden = some []) (arm : a.allocArmed.contains s.info.label = true)
    (run : (AmbientM.hiddenAlloc s).run a = .ok (b,a')) : False := by
  obtain ⟨P,copy⟩ := hiddenAlloc_copy
  obtain ⟨count,len,ident,notRx⟩ := alloc_site_facts site
  rw [copy,hiddenAllocCopy_once P s count] at run
  simp only [StateT.run_bind,StateT.run_get,hid,arm,Option.isNone_some,Bool.false_and,Bool.not_false,
    Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte,Source.except_ok_bind,Source.except_pure,
    allocRecordCopy] at run
  cases consumed : (AmbientM.hidden (.alloc s)).run a with
  | error e => rw [consumed] at run; cases run
  | ok out =>
    simp only [AmbientM.hidden,AmbientM.skipAmbient,AmbientM.noteNetRxStart,StateT.run_bind,StateT.run_get,
      StateT.run_set,hid,len,ident,notRx,List.dropWhile,Source.except_ok_bind,Source.except_pure,pure_bind,
      Bool.false_eq_true,↓reduceIte] at consumed
    cases consumed

theorem add_allocNode_acc {site : AllocSite} {n : AipNode} {d : Device} {s' : AipStore} {a a' : Ambient}
    {res : Option NodeId} {stream : List HiddenRecord}
    (which : site = .allocNode190 ∨ site = .allocNode205 ∨ site = .allocNode234)
    (hid : a.hidden = some stream) (clean : ∀ r ∈ stream, HiddenSite.passive r.site = false)
    (arm : a.allocArmed.contains site.info.label = true)
    (run : ((allocNode site n).run (Source.Aip.store d)).run a = .ok ((res,s'),a')) :
    ∃ r rest, stream = r :: rest ∧ r.site = site.hiddenId ∧ a' = {a with hidden := some rest} ∧
      ((r.bytes.head? = some 0 ∧ res = none ∧ asDev d s' = d) ∨
       (r.bytes.head? = some 1 ∧ res = some d.nextNode ∧ asDev d s' = alloc d n)) := by
  unfold allocNode at run
  obtain ⟨b,s1,a1,drawn,rest⟩ := bind_ok_run run
  clear run
  obtain ⟨rfl,consumed⟩ := add_lift_amb drawn
  clear drawn
  cases stream with
  | nil => exact (add_hiddenAlloc_nil which hid arm consumed).elim
  | cons r tail =>
    obtain ⟨siteEq,bytes,outcome,rfl⟩ := hiddenAlloc_accepted which hid arm (clean r (by simp)) consumed
    cases b with
    | false =>
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj rest none _ _ rfl
      refine ⟨r,tail,rfl,siteEq,rfl,?_⟩
      rcases bytes with zero | one
      · exact .inl ⟨zero,rfl,rfl⟩
      · rw [one] at outcome
        exact absurd outcome (by decide)
    | true =>
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj rest (some d.nextNode)
        (⟨d.nodes.insert d.nextNode n,d.nextNode+1,d.peerAllowedips⟩ : AipStore) _ rfl
      refine ⟨r,tail,rfl,siteEq,rfl,?_⟩
      rcases bytes with zero | one
      · rw [zero] at outcome
        exact absurd outcome (by decide)
      · exact .inr ⟨one,rfl,rfl⟩

theorem add_choose_acc {σ : Type} {n : AipNode} {key v : Nat} {s s' : σ} {a a' : Ambient}
    (run : ((choose n key : StateT σ AmbientM Nat).run s).run a = .ok ((v,s'),a')) :
    v = side n key ∧ s = s' ∧ a = a' := by
  unfold choose at run
  by_cases full : n.cidr ≥ n.bitlen
  · simp only [full,↓reduceIte] at run
    obtain ⟨_,_,_,thrown,_⟩ := bind_ok_run run
    cases thrown
  · simp only [full,↓reduceIte] at run
    obtain ⟨rfl,rfl,rfl⟩ := ok_inj run _ _ _ rfl
    exact ⟨rfl,rfl,rfl⟩

theorem add_bitAt_acc {σ : Type} {n : AipNode} {i : Nat} {v : Option NodeId} {s s' : σ} {a a' : Ambient}
    (run : ((n.bitAt i : StateT σ AmbientM (Option NodeId)).run s).run a = .ok ((v,s'),a')) :
    n.bit[i]? = some v ∧ s = s' ∧ a = a' := by
  unfold AipNode.bitAt at run
  cases child : n.bit[i]? with
  | none => simp only [child] at run; cases run
  | some c =>
    simp only [child] at run
    obtain ⟨rfl,rfl,rfl⟩ := ok_inj run _ _ _ rfl
    exact ⟨rfl,rfl,rfl⟩

theorem add_chooseConnect_acc {parent node : NodeId} {d : Device} {s' : AipStore} {a a' : Ambient}
    (run : ((chooseAndConnectNode parent node).run (Source.Aip.store d)).run a = .ok (((),s'),a')) :
    asDev d s' = chooseConnect d parent node ∧ a' = a := by
  unfold chooseAndConnectNode at run
  obtain ⟨p,s1,a1,readParent,r1⟩ := bind_ok_run run
  clear run
  obtain ⟨parentPresent,rfl,rfl⟩ := getNode_acc readParent
  clear readParent
  obtain ⟨n,s2,a2,readNode,r2⟩ := bind_ok_run r1
  clear r1
  obtain ⟨nodePresent,rfl,rfl⟩ := getNode_acc readNode
  clear readNode
  obtain ⟨bit,s3,a3,chosen,r3⟩ := bind_ok_run r2
  clear r2
  obtain ⟨rfl,rfl,rfl⟩ := add_choose_acc chosen
  clear chosen
  obtain ⟨connected,rfl⟩ := connectNode_acc r3
  have parentPresent' : d.nodes.get? parent = some p := parentPresent
  have nodePresent' : d.nodes.get? node = some n := nodePresent
  refine ⟨?_,rfl⟩
  rw [connected]
  simp only [chooseConnect,parentPresent',nodePresent']

theorem add_freeNode_acc {id : NodeId} {d : Device} {s' : AipStore} {a a' : Ambient}
    (run : ((freeNode id).run (Source.Aip.store d)).run a = .ok (((),s'),a')) :
    asDev d s' = {d with nodes := d.nodes.erase id} ∧ a' = a := by
  unfold freeNode at run
  obtain ⟨n,s1,a1,read,r1⟩ := bind_ok_run run
  clear run
  obtain ⟨_,rfl,rfl⟩ := getNode_acc read
  obtain ⟨_,rfl,rfl⟩ := ok_inj r1 () _ _ rfl
  exact ⟨rfl,rfl⟩


/-! ### The same primitives in `WG.M`, at a world whose device is `d` -/

theorem add_branch_run {σ : Type} (dcn : Decision) (b : Bool) (s : σ) (a : Ambient) :
    ((branch dcn b : StateT σ AmbientM Bool).run s).run a = .ok ((b,s),Model.record a dcn b) := rfl

theorem add_branchCmp_run {σ : Type} (dcn : Decision) (b : Bool) (x y : Int) (s : σ) (a : Ambient) :
    ((branchCmp dcn b x y : StateT σ AmbientM Bool).run s).run a =
      .ok ((b,s),Placement.recordCmp a dcn b x y) := rfl

theorem add_common_run {σ : Type} (node : AipNode) (key bits : Nat) (s : σ) (a : Ambient) :
    ((WG.commonBits node key bits : StateT σ AmbientM Nat).run s).run a =
      .ok ((AllowedipsRelation.common bits node.bits key,s),Model.commonRecords a bits (node.bits ^^^ key)) := by
  by_cases h32 : bits=32
  · subst bits; rfl
  · by_cases h128 : bits=128
    · subst bits
      by_cases high : (node.bits ^^^ key)/2^64=0
      all_goals simp [WG.commonBits,StateT.run_bind,StateT.run_pure,add_branch_run,
        Source.except_ok_bind,Source.except_pure,AllowedipsRelation.common,
        Model.commonRecords,high] <;> rfl
    · simp [WG.commonBits,StateT.run_bind,StateT.run_pure,add_branch_run,
        Source.except_ok_bind,Source.except_pure,AllowedipsRelation.common,
        Model.commonRecords,h32,h128] <;> rfl

theorem add_bump_run {k : WGWorld} {d : Device} (device : k.dev = some d) (f : Device → Device) (a : Ambient) :
    ((WG.modifyDev f).run k).run a = .ok (((),{k with dev := some (f d)}),a) := by
  show Except.ok (((),{k with dev := k.dev.map f}),a) = _
  rw [device]
  rfl

theorem add_getNode_wg {k k' : WGWorld} {d : Device} {a a' : Ambient} {id : NodeId} {n : AipNode}
    (device : k.dev = some d) (run : ((WG.liftAip (getNode id)).run k).run a = .ok ((n,k'),a')) :
    d.nodes.get? id = some n ∧ k' = {k with dev := some d} ∧ a = a' := by
  obtain ⟨s',inner,rfl⟩ := liftAip_acc device run
  obtain ⟨present,rfl,rfl⟩ := getNode_acc inner
  exact ⟨present,rfl,rfl⟩

theorem add_slotGet_wg {k k' : WGWorld} {d : Device} {a a' : Ambient} {root : Slot} {v : Option NodeId}
    (device : k.dev = some d) (rootSlot : root = .root4 ∨ root = .root6)
    (run : ((WG.liftAip (slotGet root)).run k).run a = .ok ((v,k'),a')) :
    v = slotOf d root ∧ k' = {k with dev := some d} ∧ a = a' := by
  obtain ⟨s',inner,rfl⟩ := liftAip_acc device run
  rcases rootSlot with rfl | rfl
  · obtain ⟨rfl,rfl,rfl⟩ := ok_inj inner _ _ _ rfl
    exact ⟨rfl,rfl,rfl⟩
  · obtain ⟨rfl,rfl,rfl⟩ := ok_inj inner _ _ _ rfl
    exact ⟨rfl,rfl,rfl⟩

theorem add_allocNode_wg {k k' : WGWorld} {d : Device} {a a' : Ambient} {site : AllocSite} {n : AipNode}
    {res : Option NodeId} {stream : List HiddenRecord} (device : k.dev = some d)
    (which : site = .allocNode190 ∨ site = .allocNode205 ∨ site = .allocNode234)
    (hid : a.hidden = some stream) (clean : ∀ r ∈ stream, HiddenSite.passive r.site = false)
    (arm : a.allocArmed.contains site.info.label = true)
    (run : ((WG.liftAip (allocNode site n)).run k).run a = .ok ((res,k'),a')) :
    ∃ r rest, stream = r :: rest ∧ r.site = site.hiddenId ∧ a' = {a with hidden := some rest} ∧
      ((r.bytes.head? = some 0 ∧ res = none ∧ k' = {k with dev := some d}) ∨
       (r.bytes.head? = some 1 ∧ res = some d.nextNode ∧ k' = {k with dev := some (alloc d n)})) := by
  obtain ⟨s',inner,rfl⟩ := liftAip_acc device run
  obtain ⟨r,rest,rfl,siteEq,rfl,outcome⟩ := add_allocNode_acc which hid clean arm inner
  refine ⟨r,rest,rfl,siteEq,rfl,?_⟩
  rcases outcome with ⟨zero,rfl,same⟩ | ⟨one,rfl,same⟩
  · exact .inl ⟨zero,rfl,by rw [same]⟩
  · exact .inr ⟨one,rfl,by rw [same]⟩

theorem add_connect_wg {k k' : WGWorld} {d : Device} {a a' : Ambient} {slot : Slot} {id : NodeId}
    (device : k.dev = some d) (run : ((WG.liftAip (connectNode slot id)).run k).run a = .ok (((),k'),a')) :
    k' = {k with dev := some (connect d slot id)} ∧ a = a' := by
  obtain ⟨s',inner,rfl⟩ := liftAip_acc device run
  obtain ⟨same,rfl⟩ := connectNode_acc inner
  exact ⟨by rw [same],rfl⟩

theorem add_chooseConnect_wg {k k' : WGWorld} {d : Device} {a a' : Ambient} {parent node : NodeId}
    (device : k.dev = some d)
    (run : ((WG.liftAip (chooseAndConnectNode parent node)).run k).run a = .ok (((),k'),a')) :
    k' = {k with dev := some (chooseConnect d parent node)} ∧ a = a' := by
  obtain ⟨s',inner,rfl⟩ := liftAip_acc device run
  obtain ⟨same,rfl⟩ := add_chooseConnect_acc inner
  exact ⟨by rw [same],rfl⟩

theorem add_freeNode_wg {k k' : WGWorld} {d : Device} {a a' : Ambient} {id : NodeId}
    (device : k.dev = some d) (run : ((WG.liftAip (freeNode id)).run k).run a = .ok (((),k'),a')) :
    k' = {k with dev := some {d with nodes := d.nodes.erase id}} ∧ a = a' := by
  obtain ⟨s',inner,rfl⟩ := liftAip_acc device run
  obtain ⟨same,rfl⟩ := add_freeNode_acc inner
  exact ⟨by rw [same],rfl⟩

theorem add_placement_wg {k k' : WGWorld} {d : Device} {a a' : Ambient} {root placed : Option NodeId}
    {key cidr bits : Nat} {exact : Bool} (device : k.dev = some d)
    (run : ((WG.liftAip (WG.nodePlacement root key cidr bits)).run k).run a = .ok (((placed,exact),k'),a')) :
    k' = {k with dev := some d} ∧ a'.hidden = a.hidden ∧ a'.allocArmed = a.allocArmed ∧
      add_Good d root key placed exact ∧
      ∃ finalStore, ((WG.nodePlacement root key cidr bits).run (Source.Aip.store d)).run a =
        .ok (((placed,exact),finalStore),a') := by
  obtain ⟨s',inner,rfl⟩ := liftAip_acc device run
  obtain ⟨rfl,hidden,armed,good⟩ := add_placement inner
  exact ⟨rfl,hidden,armed,good,_,inner⟩

theorem add_listAddTail_wg {k k' : WGWorld} {d : Device} {a a' : Ambient} {pid : PeerId} {id : NodeId}
    (device : k.dev = some d) (run : ((WG.listAddTail pid id).run k).run a = .ok (((),k'),a')) :
    k' = {k with dev := some (addTail d pid id)} ∧ a = a' := by
  cases present : d.peers[pid]? with
  | none =>
    simp [WG.listAddTail,WG.getPeer,WG.getDev,invariant,AmbientM.invariant,present,device] at run
    cases run
  | some owner =>
    obtain ⟨_,rfl,rfl⟩ := ok_inj run _ _ _ (Model.listAddTail_run k d a device pid id owner present)
    have present' : d.peers.get? pid = some owner := present
    have same : addTail d pid id =
        {d with peers := d.peers.insert pid {owner with allowedipsList := owner.allowedipsList ++ [id]}} := by
      simp only [addTail,present']
    exact ⟨by rw [same],rfl⟩

theorem add_delete_fold (id : NodeId) (xs : List (Nat × Peer)) (d : Device) :
    xs.foldl (fun d (pid,p) => if p.allowedipsList.contains id then
      {d with peers := d.peers.insert pid {p with allowedipsList := listRemove p.allowedipsList id}} else d) d =
      {d with peers := Model.delFold id xs d.peers} := by
  induction xs generalizing d with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨pid,p⟩
    simp only [List.foldl_cons,Model.delFold]
    rw [ih]
    by_cases member : p.allowedipsList.contains id = true
    · simp only [member,↓reduceIte,Model.delFold,Model.delStep,Model.unlist]
    · simp only [member,Bool.false_eq_true,↓reduceIte,Model.delFold,Model.delStep]

theorem add_listDel_wg {k k' : WGWorld} {d : Device} {a a' : Ambient} {id : NodeId}
    (device : k.dev = some d) (run : ((WG.listDel id).run k).run a = .ok (((),k'),a')) :
    k' = {k with dev := some (delete d id)} ∧ a = a' := by
  obtain ⟨_,rfl,rfl⟩ := ok_inj run _ _ _ (Model.listDel_run k d a device id)
  refine ⟨?_,rfl⟩
  rw [show delete d id = Model.unlisted d id from add_delete_fold id d.peers.toList d]


/-! ### `add` against `step` -/

/-- `C1Step.step` after the wrapper's increment, with the root slot and the width as `add` takes them. -/
def add_stepAt (d : Device) (root : Slot) (bits key cidr pid : Nat) (placed : Option NodeId) (exact : Bool)
    (outcomes : List Bool) : Step :=
  if cidr > bits then ⟨.tooLong,-EINVAL,d,0⟩ else
  match slotOf d root with
  | none => match outcomes with
    | true :: _ => ⟨.root,0,connect (addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode) root d.nextNode,1⟩
    | _ => ⟨.rootNoMem,-ENOMEM,d,1⟩
  | some rootId =>
    if exact then
      match placed.bind fun id => (d.nodes.get? id).map fun n => (id,n) with
      | some (id,n) => ⟨.exact,0,addTail (delete {d with nodes := d.nodes.insert id {n with peer := some pid}} id) pid id,0⟩
      | none => ⟨.exact,0,d,0⟩
    else match outcomes with
    | true :: rest =>
      let fresh := d.nextNode
      let d1 := addTail (alloc d (newNode key cidr bits (some pid))) pid fresh
      match (below d (some rootId) key placed).bind fun id => (d.nodes.get? id).map fun n => (id,n) with
      | none => match placed with
        | some p => ⟨.child,0,chooseConnect d1 p fresh,1⟩
        | none => ⟨.child,0,d1,1⟩
      | some (downId,down) =>
        let least := min cidr (AllowedipsRelation.common bits down.bits key)
        if cidr == least then
          let d2 := chooseConnect d1 fresh downId
          ⟨.cover,0,match placed with | none => connect d2 root fresh | some p => chooseConnect d2 p fresh,1⟩
        else match rest with
        | true :: _ =>
          let middle := d1.nextNode
          let d2 := chooseConnect (chooseConnect (alloc d1 (newNode key least bits none)) middle downId) middle fresh
          ⟨.split,0,match placed with | none => connect d2 root middle | some p => chooseConnect d2 p middle,2⟩
        | _ => ⟨.splitNoMem,-ENOMEM,{delete d1 fresh with nodes := (delete d1 fresh).nodes.erase fresh},2⟩
    | _ => ⟨.nodeNoMem,-ENOMEM,d,1⟩

theorem add_step_eq (d : Device) (family key cidr pid : Nat) (placed : Option NodeId) (exact : Bool)
    (outcomes : List Bool) :
    step d family key cidr pid placed exact outcomes =
      add_stepAt (bump d) (if family == 4 then .root4 else .root6) (if family == 4 then 32 else 128)
        key cidr pid placed exact outcomes := rfl

theorem add_out1 {r : HiddenRecord} (one : r.bytes.head? = some 1) : (r.bytes.head? == some 1) = true := by
  rw [one]; rfl
theorem add_out0 {r : HiddenRecord} (zero : r.bytes.head? = some 0) : (r.bytes.head? == some 1) = false := by
  rw [zero]; decide

/-- What one accepted `add` gives against a step. -/
abbrev add_Post (k k' : WGWorld) (a a' : Ambient) (stream : List HiddenRecord) (answer : Int) (st : Step) : Prop :=
  answer = st.answer ∧ k' = {k with dev := some st.device} ∧
  a'.hidden = some (stream.drop st.consumed) ∧ a'.allocArmed = a.allocArmed ∧
  (stream.take st.consumed).map (·.site) = st.case.sites ∧
  (∀ r ∈ stream.take st.consumed, r.bytes.head? = some 0 ∨ r.bytes.head? = some 1)

/-- The part of `add` below the node `downId` under the placement (allowedips.c:219-248), text unchanged. -/
def add_tail (root : Slot) (bits key cidr : Nat) (placed : Option NodeId) (newnode downId : NodeId) : WG.M Int := do
  let common ← commonBits (← getNode downId) key bits
  let cidr := min cidr common
  let parent := placed
  if ← branch .addNewnodeCoversDown ((← getNode newnode).cidr == cidr) then
    chooseAndConnectNode newnode downId
    if ← branch .addNewnodeAtRoot parent.isNone then connectNode root newnode
    else if let some p := parent then chooseAndConnectNode p newnode
    return 0
  let nodeAlloc ← allocNode .allocNode234 (newNode (← getNode newnode).bits cidr bits none)
  if ← branch .addIntermediateNoMem nodeAlloc.isNone then
    listDel newnode
    freeNode newnode
    return -ENOMEM
  let some node := nodeAlloc | invariant "unreachable"
  chooseAndConnectNode node downId
  chooseAndConnectNode node newnode
  if ← branch .addIntermediateAtRoot parent.isNone then connectNode root node
  else if let some p := parent then chooseAndConnectNode p node
  return 0

/-- The last connection of the cover and split cases: at the root, or below the placed node. -/
def add_attach (d : Device) (root : Slot) (placed : Option NodeId) (node : NodeId) : Device :=
  match placed with
  | none => connect d root node
  | some p => chooseConnect d p node

theorem add_tail_acc {k k' : WGWorld} {a a' : Ambient} {d1 : Device} {root : Slot} {bits key cidr pid : Nat}
    {placed : Option NodeId} {newnode downId : NodeId} {down : AipNode} {answer : Int}
    {stream : List HiddenRecord}
    (run : ((add_tail root bits key cidr placed newnode downId).run k).run a = .ok ((answer,k'),a'))
    (device : k.dev = some d1) (ready : add_Ready a stream)
    (hnew : d1.nodes.get? newnode = some (newNode key cidr bits (some pid)))
    (hdown : d1.nodes.get? downId = some down) :
    ((cidr == min cidr (AllowedipsRelation.common bits down.bits key)) = true ∧ answer = 0 ∧
      k' = {k with dev := some (add_attach (chooseConnect d1 newnode downId) root placed newnode)} ∧
      a'.hidden = some stream ∧ a'.allocArmed = a.allocArmed) ∨
    ((cidr == min cidr (AllowedipsRelation.common bits down.bits key)) = false ∧
      ∃ r rest, stream = r :: rest ∧ r.site = 79 ∧ a'.hidden = some rest ∧ a'.allocArmed = a.allocArmed ∧
        ((r.bytes.head? = some 0 ∧ answer = -ENOMEM ∧
          k' = {k with dev := some {delete d1 newnode with nodes := (delete d1 newnode).nodes.erase newnode}}) ∨
         (r.bytes.head? = some 1 ∧ answer = 0 ∧
          k' = {k with dev := some (add_attach (chooseConnect (chooseConnect (alloc d1 (newNode key
                (min cidr (AllowedipsRelation.common bits down.bits key)) bits none)) d1.nextNode downId)
                d1.nextNode newnode) root placed d1.nextNode)}))) := by
  unfold add_tail at run
  obtain ⟨n,k1,a1,h,r1⟩ := bind_ok_run run
  clear run
  obtain ⟨present,rfl,rfl⟩ := add_getNode_wg device h
  clear h
  obtain rfl : n = down := Option.some.inj (present.symm.trans hdown)
  obtain ⟨common,k2,a2,h,r2⟩ := bind_ok_run r1
  clear r1
  obtain ⟨rfl,rfl,rfl⟩ := ok_inj h _ _ _ (add_common_run n key bits _ _)
  clear h
  obtain ⟨nn,k3,a3,h,r3⟩ := bind_ok_run r2
  clear r2
  obtain ⟨presentNew,rfl,rfl⟩ := add_getNode_wg (d := d1) rfl h
  clear h
  obtain rfl : nn = newNode key cidr bits (some pid) := Option.some.inj (presentNew.symm.trans hnew)
  obtain ⟨b,k4,a4,h,r4⟩ := bind_ok_run r3
  clear r3
  obtain ⟨rfl,rfl,rfl⟩ := ok_inj h _ _ _ (add_branch_run _ _ _ _)
  clear h
  have ready4 : add_Ready (Model.record (Model.commonRecords a bits (n.bits ^^^ key)) .addNewnodeCoversDown
      ((newNode key cidr bits (some pid)).cidr == min cidr (AllowedipsRelation.common bits n.bits key))) stream :=
    ready.keep (by simp) (by simp)
  by_cases cover : (cidr == min cidr (AllowedipsRelation.common bits n.bits key)) = true
  · have cover' : ((newNode key cidr bits (some pid)).cidr ==
        min cidr (AllowedipsRelation.common bits n.bits key)) = true := cover
    simp only [cover',↓reduceIte] at r4
    obtain ⟨u,k5,a5,h,r5⟩ := bind_ok_run r4
    clear r4
    obtain ⟨rfl,rfl⟩ := add_chooseConnect_wg (d := d1) rfl h
    clear h
    obtain ⟨b,k6,a6,h,r6⟩ := bind_ok_run r5
    clear r5
    obtain ⟨rfl,rfl,rfl⟩ := ok_inj h _ _ _ (add_branch_run _ _ _ _)
    clear h
    dsimp only at r6
    cases placed with
    | none =>
      simp only [Option.isNone_none,↓reduceIte] at r6
      obtain ⟨u,k7,a7,h,r7⟩ := bind_ok_run r6
      clear r6
      obtain ⟨rfl,rfl⟩ := add_connect_wg (d := chooseConnect d1 newnode downId) rfl h
      clear h
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj r7 0 _ _ rfl
      exact .inl ⟨cover,rfl,rfl,ready4.hidden,by simp⟩
    | some p =>
      simp only [Option.isNone_some,Bool.false_eq_true,↓reduceIte] at r6
      obtain ⟨u,k7,a7,h,r7⟩ := bind_ok_run r6
      clear r6
      obtain ⟨rfl,rfl⟩ := add_chooseConnect_wg (d := chooseConnect d1 newnode downId) rfl h
      clear h
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj r7 0 _ _ rfl
      exact .inl ⟨cover,rfl,rfl,ready4.hidden,by simp⟩
  · have cover' : ((newNode key cidr bits (some pid)).cidr ==
        min cidr (AllowedipsRelation.common bits n.bits key)) = false := Bool.eq_false_iff.mpr cover
    simp only [cover',Bool.false_eq_true,↓reduceIte] at r4
    rw [cover'] at ready4
    obtain ⟨nn,k5,a5,h,r5⟩ := bind_ok_run r4
    clear r4
    obtain ⟨presentAgain,rfl,rfl⟩ := add_getNode_wg (d := d1) rfl h
    clear h
    obtain rfl : nn = newNode key cidr bits (some pid) := Option.some.inj (presentAgain.symm.trans hnew)
    obtain ⟨res,k6,a6,h,r6⟩ := bind_ok_run r5
    clear r5
    obtain ⟨r,rest,rfl,siteEq,rfl,outcome⟩ := add_allocNode_wg (d := d1) rfl (.inr (.inr rfl))
      ready4.hidden ready4.clean ready4.armed234 h
    clear h
    obtain ⟨b,k7,a7,h,r7⟩ := bind_ok_run r6
    clear r6
    obtain ⟨rfl,rfl,rfl⟩ := ok_inj h _ _ _ (add_branch_run _ _ _ _)
    clear h
    refine .inr ⟨Bool.eq_false_iff.mpr cover,r,rest,rfl,siteEq,?_⟩
    rcases outcome with ⟨zero,rfl,rfl⟩ | ⟨one,rfl,rfl⟩
    · simp only [Option.isNone_none,↓reduceIte] at r7
      obtain ⟨u,k8,a8,h,r8⟩ := bind_ok_run r7
      clear r7
      obtain ⟨rfl,rfl⟩ := add_listDel_wg (d := d1) rfl h
      clear h
      obtain ⟨u,k9,a9,h,r9⟩ := bind_ok_run r8
      clear r8
      obtain ⟨rfl,rfl⟩ := add_freeNode_wg (d := delete d1 newnode) rfl h
      clear h
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj r9 (-ENOMEM) _ _ rfl
      exact ⟨rfl,by simp,.inl ⟨zero,rfl,rfl⟩⟩
    · simp only [Option.isNone_some,Bool.false_eq_true,↓reduceIte] at r7
      obtain ⟨u,k8,a8,h,r8⟩ := bind_ok_run r7
      clear r7
      obtain ⟨rfl,rfl⟩ := add_chooseConnect_wg (d := alloc d1 (newNode key
        (min cidr (AllowedipsRelation.common bits n.bits key)) bits none)) rfl h
      clear h
      obtain ⟨u,k9,a9,h,r9⟩ := bind_ok_run r8
      clear r8
      obtain ⟨rfl,rfl⟩ := add_chooseConnect_wg (d := chooseConnect (alloc d1 (newNode key
        (min cidr (AllowedipsRelation.common bits n.bits key)) bits none)) d1.nextNode downId) rfl h
      clear h
      obtain ⟨b,k10,a10,h,r10⟩ := bind_ok_run r9
      clear r9
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj h _ _ _ (add_branch_run _ _ _ _)
      clear h
      dsimp only at r10
      cases placed with
      | none =>
        simp only [Option.isNone_none,↓reduceIte] at r10
        obtain ⟨u,k11,a11,h,r11⟩ := bind_ok_run r10
        clear r10
        obtain ⟨rfl,rfl⟩ := add_connect_wg (d := chooseConnect (chooseConnect (alloc d1 (newNode key
          (min cidr (AllowedipsRelation.common bits n.bits key)) bits none)) d1.nextNode downId)
          d1.nextNode newnode) rfl h
        clear h
        obtain ⟨rfl,rfl,rfl⟩ := ok_inj r11 0 _ _ rfl
        exact ⟨rfl,by simp,.inr ⟨one,rfl,rfl⟩⟩
      | some p =>
        simp only [Option.isNone_some,Bool.false_eq_true,↓reduceIte] at r10
        obtain ⟨u,k11,a11,h,r11⟩ := bind_ok_run r10
        clear r10
        obtain ⟨rfl,rfl⟩ := add_chooseConnect_wg (d := chooseConnect (chooseConnect (alloc d1 (newNode key
          (min cidr (AllowedipsRelation.common bits n.bits key)) bits none)) d1.nextNode downId)
          d1.nextNode newnode) rfl h
        clear h
        obtain ⟨rfl,rfl,rfl⟩ := ok_inj r11 0 _ _ rfl
        exact ⟨rfl,by simp,.inr ⟨one,rfl,rfl⟩⟩

theorem add_setNode_wg {k k' : WGWorld} {d : Device} {a a' : Ambient} {id : NodeId} {n : AipNode}
    (device : k.dev = some d) (run : ((WG.liftAip (setNode id n)).run k).run a = .ok (((),k'),a')) :
    k' = {k with dev := some {d with nodes := d.nodes.insert id n}} ∧ a = a' := by
  obtain ⟨s',inner,rfl⟩ := liftAip_acc device run
  obtain ⟨_,rfl,rfl⟩ := ok_inj inner () _ _ rfl
  exact ⟨rfl,rfl⟩

theorem add_addTail_nodes (d : Device) (pid : PeerId) (id : NodeId) : (addTail d pid id).nodes = d.nodes := by
  unfold addTail
  split <;> rfl

theorem add_addTail_next (d : Device) (pid : PeerId) (id : NodeId) : (addTail d pid id).nextNode = d.nextNode := by
  unfold addTail
  split <;> rfl

theorem add_addTail_slot (d : Device) (pid : PeerId) (id : NodeId) (n : AipNode) {root : Slot}
    (rootSlot : root = .root4 ∨ root = .root6) : slotOf (addTail (alloc d n) pid id) root = slotOf d root := by
  unfold addTail
  rcases rootSlot with rfl | rfl <;> split <;> rfl

theorem add_fresh_get {d : Device} {id : NodeId} {n m : AipNode} {pid : PeerId} {f : NodeId}
    (fresh : d.nodes.get? d.nextNode = none) (present : d.nodes.get? id = some n) :
    (addTail (alloc d m) pid f).nodes.get? id = some n := by
  have different : ¬d.nextNode = id := by
    rintro rfl
    rw [fresh] at present
    cases present
  rw [add_addTail_nodes]
  have stored : d.nodes[id]? = some n := present
  show (d.nodes.insert d.nextNode m)[id]? = some n
  simpa [Std.TreeMap.getElem?_insert,different] using stored

theorem add_new_get (d : Device) (m : AipNode) (pid : PeerId) (f : NodeId) :
    (addTail (alloc d m) pid f).nodes.get? d.nextNode = some m := by
  rw [add_addTail_nodes]
  show (d.nodes.insert d.nextNode m)[d.nextNode]? = some m
  simp

theorem add_one_site {r : HiddenRecord} {rest : List HiddenRecord} {n : Nat} (site : r.site = n) :
    List.map (fun x => x.site) (List.take 1 (r :: rest)) = [n] := by
  simp [site]

theorem add_one_outcome {r : HiddenRecord} {rest : List HiddenRecord}
    (outcome : r.bytes.head? = some 0 ∨ r.bytes.head? = some 1) :
    ∀ x ∈ List.take 1 (r :: rest), x.bytes.head? = some 0 ∨ x.bytes.head? = some 1 := by
  intro x member
  simp only [List.take_succ_cons,List.take_zero,List.mem_singleton] at member
  subst member
  exact outcome

/-- The cover and split cases against `add_stepAt`, from the tail's result. -/
theorem add_tail_post {k k' : WGWorld} {a a6 a' : Ambient} {d : Device} {root : Slot}
    {bits key cidr pid : Nat} {placed : Option NodeId} {rootId downId : NodeId} {down : AipNode}
    {answer : Int} {r : HiddenRecord} {rest : List HiddenRecord}
    (long : ¬cidr > bits) (empty : slotOf d root = some rootId)
    (reached : ((below d (some rootId) key placed).bind fun id => (d.nodes.get? id).map fun n => (id,n)) =
      some (downId,down))
    (one : r.bytes.head? = some 1) (site : r.site = 78) (armed6 : a6.allocArmed = a.allocArmed)
    (result :
      ((cidr == min cidr (AllowedipsRelation.common bits down.bits key)) = true ∧ answer = 0 ∧
        k' = {k with dev := some (add_attach (chooseConnect (addTail (alloc d (newNode key cidr bits (some pid)))
          pid d.nextNode) d.nextNode downId) root placed d.nextNode)} ∧
        a'.hidden = some rest ∧ a'.allocArmed = a6.allocArmed) ∨
      ((cidr == min cidr (AllowedipsRelation.common bits down.bits key)) = false ∧
        ∃ r2 rest2, rest = r2 :: rest2 ∧ r2.site = 79 ∧ a'.hidden = some rest2 ∧
          a'.allocArmed = a6.allocArmed ∧
          ((r2.bytes.head? = some 0 ∧ answer = -ENOMEM ∧
            k' = {k with dev := some {delete (addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode)
              d.nextNode with nodes := (delete (addTail (alloc d (newNode key cidr bits (some pid))) pid
                d.nextNode) d.nextNode).nodes.erase d.nextNode}}) ∨
           (r2.bytes.head? = some 1 ∧ answer = 0 ∧
            k' = {k with dev := some (add_attach (chooseConnect (chooseConnect (alloc (addTail (alloc d
              (newNode key cidr bits (some pid))) pid d.nextNode) (newNode key
                (min cidr (AllowedipsRelation.common bits down.bits key)) bits none))
                (addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode).nextNode downId)
                (addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode).nextNode d.nextNode)
                root placed (addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode).nextNode)})))) :
    ∀ st, st = add_stepAt d root bits key cidr pid placed false
        ((r :: rest).map fun x => x.bytes.head? == some 1) →
      add_Post k k' a a' (r :: rest) answer st ∧ st.case ≠ .tooLong := by
  rintro st rfl
  rcases result with ⟨cover,rfl,rfl,hid,arm⟩ |
    ⟨split,r2,rest2,rfl,site2,hid,arm,(⟨zero,rfl,rfl⟩ | ⟨one2,rfl,rfl⟩)⟩
  · simp only [add_stepAt,long,↓reduceIte,empty,Bool.false_eq_true,List.map_cons,add_out1 one,reached,cover]
    refine ⟨⟨rfl,?_,hid,arm.trans armed6,add_one_site site,add_one_outcome (.inr one)⟩,by simp⟩
    cases placed <;> rfl
  · simp only [add_stepAt,long,↓reduceIte,empty,Bool.false_eq_true,List.map_cons,add_out1 one,reached,split,
      add_out0 zero]
    refine ⟨⟨rfl,rfl,hid,arm.trans armed6,by simp [site,site2,Case.sites],?_⟩,by simp⟩
    intro x member
    simp only [List.take_succ_cons,List.take_zero,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact .inr one
    · exact .inl zero
  · simp only [add_stepAt,long,↓reduceIte,empty,Bool.false_eq_true,List.map_cons,add_out1 one,reached,split,
      add_out1 one2]
    refine ⟨⟨rfl,?_,hid,arm.trans armed6,by simp [site,site2,Case.sites],?_⟩,by simp⟩
    · cases placed <;> rfl
    · intro x member
      simp only [List.take_succ_cons,List.take_zero,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact .inr one
      · exact .inr one2

theorem add_ite_run {σ α : Type} {c : Prop} [Decidable c] {A B : StateT σ AmbientM α} {s : σ} {a : Ambient}
    {r : (α × σ) × Ambient} (h : ((if c then A else B).run s).run a = .ok r) :
    (c ∧ (A.run s).run a = .ok r) ∨ (¬c ∧ (B.run s).run a = .ok r) := by
  by_cases holds : c
  · rw [show (if c then A else B) = A from by simp only [holds,↓reduceIte]] at h
    exact .inl ⟨holds,h⟩
  · rw [show (if c then A else B) = B from by simp only [holds,↓reduceIte]] at h
    exact .inr ⟨holds,h⟩

theorem add_core {k k' : WGWorld} {a a' : Ambient} {d : Device} {root : Slot} {bits key cidr pid : Nat}
    {answer : Int} {stream : List HiddenRecord} (device : k.dev = some d) (ready : add_Ready a stream)
    (rootSlot : root = .root4 ∨ root = .root6) (fresh : d.nodes.get? d.nextNode = none)
    (run : ((WG.add root bits key cidr (some pid)).run k).run a = .ok ((answer,k'),a')) :
    ∃ placed exact, ∀ st,
      st = add_stepAt d root bits key cidr pid placed exact (stream.map fun r => r.bytes.head? == some 1) →
      add_Post k k' a a' stream answer st ∧
      (st.case ≠ .tooLong → st.case ≠ .rootNoMem → st.case ≠ .root →
        ∃ ambient finalAmbient finalStore,
          ((WG.nodePlacement (slotOf d root) key cidr bits).run (Source.Aip.store d)).run ambient =
            .ok (((placed,exact),finalStore),finalAmbient)) := by
  unfold WG.add at run
  obtain ⟨b1,k1,a1,h1,r1⟩ := bind_ok_run run
  clear run
  obtain ⟨rfl,rfl,rfl⟩ := ok_inj h1 _ _ _ (add_branchCmp_run .addCidrTooLong (decide (cidr > bits)) cidr bits k a)
  clear h1
  by_cases long : cidr > bits
  · simp only [long,decide_true,↓reduceIte] at r1
    obtain ⟨rfl,rfl,rfl⟩ := ok_inj r1 (-EINVAL) _ _ rfl
    refine ⟨none,false,?_⟩
    rintro st rfl
    simp only [add_stepAt,long,↓reduceIte]
    exact ⟨⟨rfl,(world_same device).symm,ready.hidden,rfl,rfl,fun r member => by cases member⟩,
      fun wrong => absurd rfl wrong⟩
  simp only [long,decide_false,Bool.false_eq_true,↓reduceIte] at r1
  obtain ⟨b2,k2,a2,h2,r2⟩ := bind_ok_run r1
  clear r1
  obtain ⟨rfl,rfl,rfl⟩ := ok_inj h2 _ _ _ (add_branch_run .addNoPeer (some pid).isNone k _)
  clear h2
  simp only [Option.isNone_some,Bool.false_eq_true,↓reduceIte] at r2
  obtain ⟨trie,k3,a3,h3,r3⟩ := bind_ok_run r2
  clear r2
  obtain ⟨rfl,rfl,rfl⟩ := add_slotGet_wg device rootSlot h3
  clear h3
  obtain ⟨b4,k4,a4,h4,r4⟩ := bind_ok_run r3
  clear r3
  obtain ⟨rfl,rfl,rfl⟩ := ok_inj h4 _ _ _ (add_branch_run .addEmptyTrie (slotOf d root).isNone _ _)
  clear h4
  have ready4 : add_Ready (Model.record (Model.record (Placement.recordCmp a .addCidrTooLong
      false cidr bits) .addNoPeer false) .addEmptyTrie (slotOf d root).isNone) stream :=
    ready.keep rfl rfl
  cases empty : slotOf d root with
  | none =>
    simp only [empty,Option.isNone_none,↓reduceIte] at r4 ready4
    obtain ⟨x,k5,a5,h5,r5⟩ := bind_ok_run r4
    clear r4
    obtain ⟨res,k6,a6,h6,h7⟩ := bind_ok_run h5
    clear h5
    obtain ⟨r,rest,rfl,siteEq,rfl,outcome⟩ := add_allocNode_wg (d := d) rfl (.inl rfl)
      ready4.hidden ready4.clean ready4.armed190 h6
    clear h6
    obtain ⟨b,k7,a7,h8,h9⟩ := bind_ok_run h7
    clear h7
    obtain ⟨rfl,rfl,rfl⟩ := ok_inj h8 _ _ _ (add_branch_run _ _ _ _)
    clear h8
    have site : r.site = 77 := siteEq
    refine ⟨none,false,?_⟩
    rintro st rfl
    rcases outcome with ⟨zero,rfl,rfl⟩ | ⟨one,rfl,rfl⟩
    · simp only [Option.isNone_none,↓reduceIte] at h9
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj h9 none _ _ rfl
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj r5 (-ENOMEM) _ _ rfl
      simp only [add_stepAt,long,↓reduceIte,empty,List.map_cons,add_out0 zero]
      exact ⟨⟨rfl,rfl,rfl,rfl,add_one_site site,add_one_outcome (.inl zero)⟩,fun _ wrong => absurd rfl wrong⟩
    · simp only [Option.isNone_some,Bool.false_eq_true,↓reduceIte] at h9
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj h9 (some d.nextNode) _ _ rfl
      dsimp only at r5
      obtain ⟨u,k8,a8,h,r6⟩ := bind_ok_run r5
      clear r5
      obtain ⟨rfl,rfl⟩ := add_listAddTail_wg (d := alloc d (newNode key cidr bits (some pid))) rfl h
      clear h
      obtain ⟨u,k9,a9,h,r7⟩ := bind_ok_run r6
      clear r6
      obtain ⟨rfl,rfl⟩ := add_connect_wg
        (d := addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode) rfl h
      clear h
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj r7 0 _ _ rfl
      simp only [add_stepAt,long,↓reduceIte,empty,List.map_cons,add_out1 one]
      exact ⟨⟨rfl,rfl,rfl,rfl,add_one_site site,add_one_outcome (.inr one)⟩,fun _ _ wrong => absurd rfl wrong⟩
  | some rootId =>
    simp only [empty,Option.isNone_some,Bool.false_eq_true,↓reduceIte] at r4 ready4
    obtain ⟨x,k5,a5,h,r5⟩ := bind_ok_run r4
    clear r4
    obtain ⟨placed,exact⟩ := x
    obtain ⟨rfl,hid5,arm5,good,finalStore,inner⟩ := add_placement_wg (d := d) rfl h
    clear h
    have ready5 : add_Ready a5 stream := ready4.keep hid5 arm5
    have armed5 : a5.allocArmed = a.allocArmed := arm5
    obtain ⟨b,k6,a6,h,r6⟩ := bind_ok_run r5
    clear r5
    obtain ⟨rfl,rfl,rfl⟩ := ok_inj h _ _ _ (add_branch_run _ _ _ _)
    clear h
    refine ⟨placed,exact,?_⟩
    rintro st rfl
    refine ⟨?_,fun _ _ _ => ⟨_,_,_,inner⟩⟩
    dsimp only at r6
    cases exact with
    | true =>
      simp only [↓reduceIte] at r6
      cases placed with
      | none =>
        obtain ⟨_,_,_,thrown,_⟩ := bind_ok_run r6
        cases thrown
      | some id =>
        dsimp only at r6
        obtain ⟨n,k7,a7,h,r7⟩ := bind_ok_run r6
        clear r6
        obtain ⟨present,rfl,rfl⟩ := add_getNode_wg (d := d) rfl h
        clear h
        obtain ⟨u,k8,a8,h,r8⟩ := bind_ok_run r7
        clear r7
        obtain ⟨rfl,rfl⟩ := add_setNode_wg (d := d) rfl h
        clear h
        obtain ⟨u,k9,a9,h,r9⟩ := bind_ok_run r8
        clear r8
        obtain ⟨rfl,rfl⟩ := add_listDel_wg (d := {d with nodes := d.nodes.insert id {n with peer := some pid}}) rfl h
        clear h
        obtain ⟨u,k10,a10,h,r10⟩ := bind_ok_run r9
        clear r9
        obtain ⟨rfl,rfl⟩ := add_listAddTail_wg
          (d := delete {d with nodes := d.nodes.insert id {n with peer := some pid}} id) rfl h
        clear h
        obtain ⟨rfl,rfl,rfl⟩ := ok_inj r10 0 _ _ rfl
        simp only [add_stepAt,long,↓reduceIte,empty,Option.bind_some,present,Option.map_some]
        exact ⟨rfl,rfl,ready5.hidden,armed5,rfl,fun r member => by cases member⟩
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte] at r6
      obtain ⟨res,k7,a7,h,r7⟩ := bind_ok_run r6
      clear r6
      have ready6 : add_Ready (Model.record a5 .addExact false) stream := ready5.keep rfl rfl
      obtain ⟨r,rest,rfl,siteEq,rfl,outcome⟩ := add_allocNode_wg (d := d) rfl (.inr (.inl rfl))
        ready6.hidden ready6.clean ready6.armed205 h
      clear h
      have site : r.site = 78 := siteEq
      obtain ⟨b,k8,a8,h,r8⟩ := bind_ok_run r7
      clear r7
      obtain ⟨rfl,rfl,rfl⟩ := ok_inj h _ _ _ (add_branch_run _ _ _ _)
      clear h
      rcases outcome with ⟨zero,rfl,rfl⟩ | ⟨one,rfl,rfl⟩
      · simp only [Option.isNone_none,↓reduceIte] at r8
        obtain ⟨rfl,rfl,rfl⟩ := ok_inj r8 (-ENOMEM) _ _ rfl
        simp only [add_stepAt,long,↓reduceIte,empty,Bool.false_eq_true,List.map_cons,add_out0 zero]
        exact ⟨rfl,rfl,rfl,armed5,add_one_site site,add_one_outcome (.inl zero)⟩
      · simp only [Option.isNone_some,Bool.false_eq_true,↓reduceIte] at r8
        obtain ⟨u,k9,a9,h,r9⟩ := bind_ok_run r8
        clear r8
        obtain ⟨rfl,rfl⟩ := add_listAddTail_wg (d := alloc d (newNode key cidr bits (some pid))) rfl h
        clear h
        obtain ⟨b,k10,a10,h,r10⟩ := bind_ok_run r9
        clear r9
        obtain ⟨rfl,rfl,rfl⟩ := ok_inj h _ _ _ (add_branch_run _ _ _ _)
        clear h
        have hnew := add_new_get d (newNode key cidr bits (some pid)) pid d.nextNode
        rcases add_ite_run r10 with ⟨atRoot,r10a⟩ | ⟨belowParent,r10b⟩
        · clear r10
          have nothing : placed = none := by
            cases placed with
            | none => rfl
            | some p => cases atRoot
          subst nothing
          obtain ⟨below,k11,a11,h,r11⟩ := bind_ok_run r10a
          clear r10a
          obtain ⟨rfl,rfl,rfl⟩ := add_slotGet_wg
            (d := addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode) rfl rootSlot h
          clear h
          rw [add_addTail_slot d pid d.nextNode (newNode key cidr bits (some pid)) rootSlot,empty] at r11
          dsimp only at r11
          obtain ⟨down,stored⟩ := good.2 rfl rootId rfl
          have hdown := add_fresh_get (m := newNode key cidr bits (some pid)) (pid := pid) (f := d.nextNode)
            fresh stored
          have result := add_tail_acc r11 rfl (ready6.next.keep rfl rfl) hnew hdown
          have reached : ((Proof.below d (some rootId) key none).bind fun id =>
              (d.nodes.get? id).map fun n => (id,n)) = some (rootId,down) := by
            simp only [Proof.below,Option.bind_some,stored,Option.map_some]
          exact (add_tail_post (k := k) long empty reached one site armed5 result _ rfl).1
        · clear r10
          obtain ⟨p,rfl⟩ : ∃ p, placed = some p := by
            cases placed with
            | none => exact absurd rfl belowParent
            | some p => exact ⟨p,rfl⟩
          dsimp only at r10b
          obtain ⟨pn,k11,a11,h,r11⟩ := bind_ok_run r10b
          clear r10b
          obtain ⟨presentP1,rfl,rfl⟩ := add_getNode_wg
            (d := addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode) rfl h
          clear h
          obtain ⟨pn0,presentP⟩ := good.1 p rfl
          obtain rfl : pn = pn0 := Option.some.inj (presentP1.symm.trans (add_fresh_get fresh presentP))
          obtain ⟨bit,k12,a12,h,r12⟩ := bind_ok_run r11
          clear r11
          obtain ⟨rfl,rfl,rfl⟩ := add_choose_acc h
          clear h
          obtain ⟨pn2,k13,a13,h,r13⟩ := bind_ok_run r12
          clear r12
          obtain ⟨presentP2,rfl,rfl⟩ := add_getNode_wg
            (d := addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode) rfl h
          clear h
          obtain rfl : pn = pn2 := Option.some.inj (presentP1.symm.trans presentP2)
          obtain ⟨downOpt,k14,a14,h,r14⟩ := bind_ok_run r13
          clear r13
          obtain ⟨child,rfl,rfl⟩ := add_bitAt_acc h
          clear h
          obtain ⟨b,k15,a15,h,r15⟩ := bind_ok_run r14
          clear r14
          obtain ⟨rfl,rfl,rfl⟩ := ok_inj h _ _ _ (add_branch_run _ _ _ _)
          clear h
          have child' : pn.bit[key / 2 ^ (pn.bitlen - 1 - pn.cidr) % 2]? = some downOpt := child
          have reachedBelow : Proof.below d (some rootId) key (some p) = downOpt := by
            simp only [Proof.below,presentP,child']
            rfl
          rcases add_ite_run r15 with ⟨noDown,r15a⟩ | ⟨someDown,r15b⟩
          · clear r15
            have nothing : downOpt = none := by
              cases downOpt with
              | none => rfl
              | some x => cases noDown
            subst nothing
            obtain ⟨u,k16,a16,h,r16⟩ := bind_ok_run r15a
            clear r15a
            obtain ⟨rfl,rfl⟩ := add_connect_wg
              (d := addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode) rfl h
            clear h
            obtain ⟨rfl,rfl,rfl⟩ := ok_inj r16 0 _ _ rfl
            have same : chooseConnect (addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode) p
                d.nextNode = connect (addTail (alloc d (newNode key cidr bits (some pid))) pid d.nextNode)
                  (.child p (side pn key)) d.nextNode := by
              simp only [chooseConnect,presentP1,hnew]
              rfl
            simp only [add_stepAt,long,↓reduceIte,empty,Bool.false_eq_true,List.map_cons,add_out1 one,
              reachedBelow,Option.bind_none,same]
            exact ⟨rfl,rfl,rfl,armed5,add_one_site site,add_one_outcome (.inr one)⟩
          · clear r15
            obtain ⟨downId,rfl⟩ : ∃ x, downOpt = some x := by
              cases downOpt with
              | none => exact absurd rfl someDown
              | some x => exact ⟨x,rfl⟩
            dsimp only at r15b
            obtain ⟨down,stored⟩ := good.2 rfl downId reachedBelow
            have hdown := add_fresh_get (m := newNode key cidr bits (some pid)) (pid := pid) (f := d.nextNode)
              fresh stored
            have result := add_tail_acc r15b rfl (ready6.next.keep rfl rfl) hnew hdown
            have reached : ((Proof.below d (some rootId) key (some p)).bind fun id =>
                (d.nodes.get? id).map fun n => (id,n)) = some (downId,down) := by
              rw [reachedBelow]
              simp only [Option.bind_some,stored,Option.map_some]
            exact (add_tail_post (k := k) long empty reached one site armed5 result _ rfl).1

/-- An accepted `WG.insert` is `C1Step.step`, on a device whose next node identity is unused.
The hypothesis `fresh` is not in the statement first asked for (`add_insert_accepted`): without it the
mirror's reads after the allocation (the placed node, the node below) can return the new node where
`step` reads the old one. `Inv` supplies it (every stored identity is below `nextNode`). -/
theorem add_insert_accepted_partial {g g' : WGWorld} {a a' : Ambient} {d : Device} {family key cidr pid : Nat}
    {answer : Int} {stream : List HiddenRecord} (device : g.dev = some d) (ready : add_Ready a stream)
    (families : family = 4 ∨ family = 6) (fresh : d.nodes.get? d.nextNode = none)
    (run : ((WG.insert family key cidr pid).run g).run a = .ok ((answer,g'),a')) :
    ∃ placed exact, ∀ st, st = step d family key cidr pid placed exact (stream.map fun r => r.bytes.head? == some 1) →
      answer = st.answer ∧ g' = {g with dev := some st.device} ∧
      a'.hidden = some (stream.drop st.consumed) ∧ a'.allocArmed = a.allocArmed ∧
      (stream.take st.consumed).map (·.site) = st.case.sites ∧
      (∀ r ∈ stream.take st.consumed, r.bytes.head? = some 0 ∨ r.bytes.head? = some 1) ∧
      (st.case ≠ .tooLong → st.case ≠ .rootNoMem → st.case ≠ .root →
        ∃ ambient finalAmbient finalStore,
          ((WG.nodePlacement (rootOf d family) key cidr (widthOf family)).run (Source.Aip.store (bump d))).run ambient =
            .ok (((placed,exact),finalStore),finalAmbient)) := by
  unfold WG.insert at run
  obtain ⟨u,k1,a1,h,r1⟩ := bind_ok_run run
  clear run
  obtain ⟨_,rfl,rfl⟩ := ok_inj h _ _ _ (add_bump_run device _ a)
  clear h
  rcases families with rfl | rfl
  · rcases add_ite_run r1 with ⟨_,r2⟩ | ⟨wrong,_⟩
    · obtain ⟨placed,exact,facts⟩ := add_core (d := bump d) rfl ready (.inl rfl) fresh r2
      refine ⟨placed,exact,?_⟩
      rintro st rfl
      obtain ⟨post,walked⟩ := facts (step d 4 key cidr pid placed exact _) rfl
      exact ⟨post.1,post.2.1,post.2.2.1,post.2.2.2.1,post.2.2.2.2.1,post.2.2.2.2.2,walked⟩
    · exact absurd rfl wrong
  · rcases add_ite_run r1 with ⟨wrong,_⟩ | ⟨_,r2⟩
    · exact absurd wrong (by decide)
    · obtain ⟨placed,exact,facts⟩ := add_core (d := bump d) rfl ready (.inr rfl) fresh r2
      refine ⟨placed,exact,?_⟩
      rintro st rfl
      obtain ⟨post,walked⟩ := facts (step d 6 key cidr pid placed exact _) rfl
      exact ⟨post.1,post.2.1,post.2.2.1,post.2.2.2.1,post.2.2.2.2.1,post.2.2.2.2.2,walked⟩

#print axioms add_insert_accepted_partial

/-! ## `RunIsStep` -/

/-- An accepted lifted run is an accepted run of the WireGuard computation. -/
theorem run_liftWG_acc {α : Type} {x : WG.M α} {w w' : World} {v : α}
    (run : (liftWG x).run w = .ok (v,w')) :
    ∃ g' a', (x.run w.wg).run w.ambient = .ok ((v,g'),a') ∧ w' = {w with wg := g', ambient := a'} := by
  have unfolded : (liftWG x).run w =
      ((x.run w.wg).run w.ambient >>= fun p => pure (p.1.1,{w with wg := p.1.2, ambient := p.2})) := rfl
  rw [unfolded] at run
  cases inner : (x.run w.wg).run w.ambient with
  | error e => rw [inner] at run; cases run
  | ok p =>
    rw [inner] at run
    cases run
    exact ⟨p.1.2,p.2,rfl,rfl⟩

theorem run_short {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool}
    (notLong : (Proof.step d family key cidr pid placed exact outcomes).case ≠ .tooLong) :
    cidr ≤ widthOf family := by
  by_cases long : cidr > widthOf family
  · exfalso
    apply notLong
    unfold widthOf at long
    simp only [Proof.step,long,↓reduceIte]
  · omega


theorem run_fresh {L : Layout} {A : Allocator} {w : World} {m : Mem 64} {d : Device}
    (related : Related L A w m) (device : w.wg.dev = some d) : d.nodes.get? d.nextNode = none := by
  obtain ⟨names,stream,_,_,asserted,_⟩ := related
  obtain ⟨d',device',corresponds,_⟩ := assertAt_ok asserted
  cases Option.some.inj (device'.symm.trans device)
  cases present : d.nodes.get? d.nextNode with
  | none => rfl
  | some n =>
    have member : (d.nextNode,n) ∈ (Allowedips.target d).nodes :=
      Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present
    exact absurd (target_nodes_below corresponds _ member) (Nat.lt_irrefl _)

theorem runIsStep : RunIsStep := by
  intro L A c s w w' family key cidr pid ra answer inv ready run
  obtain ⟨d,device⟩ : ∃ d, w.wg.dev = some d := by
    obtain ⟨names,stream,_,_,asserted,_⟩ := inv
    obtain ⟨d,device,_⟩ := assertAt_ok asserted
    exact ⟨d,device⟩
  obtain ⟨stream,hidden,clean,armed190,armed205,armed234⟩ := ordered_clean inv
  obtain ⟨families,keyBound,_⟩ := ordered_ready_facts ready
  obtain ⟨g',a',accepted,rfl⟩ := run_liftWG_acc run
  obtain ⟨placed,exact,spec⟩ := add_insert_accepted_partial device
    ⟨hidden,clean,armed190,armed205,armed234⟩ families (run_fresh inv device) accepted
  obtain ⟨result,world,recordsAfter,armedSame,sites,outcomes,walked⟩ := spec _ rfl
  refine ⟨d,stream,placed,exact,_,{
    device := device, records := hidden, trie := ordered_of_related inv device,
    families := families, keyBound := keyBound, model := rfl, result := result,
    after := ⟨_,by rw [world],rfl⟩, recordsAfter := recordsAfter, sites := sites, outcomes := outcomes,
    armedAfter := ?_, walked := ?_ }⟩
  · simp only [Statements.C1.armed,List.all_cons,List.all_nil,armedSame,armed190,armed205,armed234,
      Bool.and_self]
  · intro notLong notNoMem notRoot
    have trieOrdered : ordered d = true := ordered_of_related inv device
    obtain ⟨ambient,finalAmbient,finalStore,placement⟩ := walked notLong notNoMem notRoot
    exact ⟨⟨ambient,finalAmbient,finalStore,placement⟩,
      (walk_of_run (d := bump d) (show ordered (bump d) = true from trieOrdered) families keyBound (run_short notLong) placement).1⟩

#print axioms runIsStep
end Binary.Statements.C1.Proof
