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
end Binary.Statements.C1.Proof
