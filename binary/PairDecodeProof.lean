import PairTrie
import PairNextProof
import CanonicalLoads
import PairExcept

namespace Binary.Pair
set_option maxRecDepth 2048

theorem word_bound {m : DataMem} {path : String} {base bytes value : Nat}
    (read : word m path base bytes = .ok value) : value < 256^bytes := by
  have bound := (loadInt_range m (.ofNat 64 base) bytes value
    (word_loadInt m path base bytes value read)).2
  exact_mod_cast bound

namespace Trie

/-- Inversion of the executable decoder: these facts are conclusions of a
successful decode, not another premise or an independently checked relation. -/
structure DecodedFields (names : Names) (o : AllowedipsProbe.Offsets)
    (m : DataMem) (a : Nat) (node : Node) : Prop where
  peer : ∃ raw, word m "node.peer" (a+o.peer) 8 = .ok raw ∧
    pointer names.peers "node.peer" raw = .ok node.peer
  children : ∃ left right lp rp,
    node.children = #[left,right] ∧
    word m ("node.child[" ++ toString (0 : Nat) ++ "]") (a+o.children) 8 = .ok lp ∧
    pointer names.nodes ("node.child[" ++ toString (0 : Nat) ++ "]") lp = .ok left ∧
    word m ("node.child[" ++ toString (1 : Nat) ++ "]") (a+o.children+8) 8 = .ok rp ∧
    pointer names.nodes ("node.child[" ++ toString (1 : Nat) ++ "]") rp = .ok right
  cidr : word m "node.cidr" (a+o.cidr) 1 = .ok node.cidr
  width : word m "node.width" (a+o.bitlen) 1 = .ok node.width
  family : node.width = 32 ∨ node.width = 128
  bounded : node.cidr ≤ node.width
  byteSelector : word m "node.byte-selector" (a+o.bitAtA) 1 =
    .ok (node.cidr/8 ^^^ ((node.width/8-1)%8))
  bitSelector : word m "node.bit-selector" (a+o.bitAtB) 1 = .ok (7-node.cidr%8)
  key : if node.width = 32 then word m "node.key32" (a+o.bits) 4 = .ok node.key else
    ∃ hi lo, word m "node.key128.high" (a+o.bits) 8 = .ok hi ∧
      word m "node.key128.low" (a+o.bits+8) 8 = .ok lo ∧ node.key = hi*2^64+lo

theorem decodeNode_fields {names : Names} {o : AllowedipsProbe.Offsets}
    {m : DataMem} {a : Nat} {node : Node} (ok : decodeNode names o m a = .ok node) :
    DecodedFields names o m a node := by
  simp only [decodeNode, Std.Legacy.Range.forIn_eq_forIn_range',
    show ([:2] : Std.Legacy.Range).size = 2 from rfl,
    List.range'_succ,List.range'_zero,List.forIn_cons,List.forIn_nil,
    Nat.reduceAdd,Nat.reduceMul,Nat.add_zero,bind_assoc,pure_bind] at ok
  obtain ⟨peerRaw,peerRead,ok⟩ := bind_ok ok
  obtain ⟨peer,peerPointer,ok⟩ := bind_ok ok
  obtain ⟨lp,leftRead,ok⟩ := bind_ok ok
  obtain ⟨left,leftPointer,ok⟩ := bind_ok ok
  obtain ⟨rp,rightRead,ok⟩ := bind_ok ok
  obtain ⟨right,rightPointer,ok⟩ := bind_ok ok
  obtain ⟨cidr,cidrRead,ok⟩ := bind_ok ok
  obtain ⟨width,widthRead,ok⟩ := bind_ok ok
  obtain ⟨valid,ok⟩ := check_ok _ _ _ _ ok
  have valid' : (width = 32 ∨ width = 128) ∧ cidr ≤ width := by simpa using valid
  obtain ⟨byte,byteRead,ok⟩ := bind_ok ok
  obtain ⟨bit,bitRead,ok⟩ := bind_ok ok
  obtain ⟨selectors,ok⟩ := check_ok _ _ _ _ ok
  have selectors' : byte = (cidr/8 ^^^ ((width/8-1)%8)) ∧ bit = 7-cidr%8 := by simpa using selectors
  rw [selectors'.1] at byteRead
  rw [selectors'.2] at bitRead
  by_cases family : width = 32
  · simp only [family,beq_self_eq_true,↓reduceIte] at ok
    obtain ⟨key,keyRead,ok⟩ := bind_ok ok
    have equal : ({peer,children := #[left,right],cidr,width,key} : Node) = node := by
      have children : (#[].push left).push right = #[left,right] := by rfl
      simpa only [family,children] using Except.ok.inj ok
    subst node
    refine ⟨⟨peerRaw,peerRead,peerPointer⟩,⟨left,right,lp,rp,rfl,leftRead,leftPointer,rightRead,rightPointer⟩,
      cidrRead,widthRead,valid'.1,valid'.2,byteRead,bitRead,?_⟩
    simpa only [family,↓reduceIte] using keyRead
  · simp only [beq_iff_eq,family,↓reduceIte] at ok
    obtain ⟨hi,hiRead,ok⟩ := bind_ok ok
    obtain ⟨lo,loRead,ok⟩ := bind_ok ok
    have equal : ({peer,children := #[left,right],cidr,width,key := hi*2^64+lo} : Node) = node := Except.ok.inj ok
    subst node
    refine ⟨⟨peerRaw,peerRead,peerPointer⟩,⟨left,right,lp,rp,rfl,leftRead,leftPointer,rightRead,rightPointer⟩,
      cidrRead,widthRead,valid'.1,valid'.2,byteRead,bitRead,?_⟩
    simp only [family,↓reduceIte]
    exact ⟨hi,lo,hiRead,loRead,rfl⟩

structure Reconstructed (names : Names) (o : AllowedipsProbe.Offsets)
    (m : DataMem) (s : State) : Prop where
  layout : o.nodeSize = AllowedipsLayout.nodeSize ∧ o.peer = AllowedipsLayout.peer ∧
    o.children = AllowedipsLayout.bit ∧ o.cidr = AllowedipsLayout.cidr ∧
    o.bitAtA = AllowedipsLayout.bit_at_a ∧ o.bitAtB = AllowedipsLayout.bit_at_b ∧
    o.bitlen = AllowedipsLayout.bitlen ∧ o.bits = AllowedipsLayout.bits ∧
    o.peerRefcount = Layouts.peer_refcount
  nodeIds : (names.nodes.map Prod.fst).Nodup
  peerIds : (names.peers.map Prod.fst).Nodup
  nodeRange : ∀ id a, (id,a) ∈ names.nodes → 0 < a ∧ a+o.nodeSize < 2^64
  peerRange : ∀ id a, (id,a) ∈ names.peers → 0 < a ∧ a+Layouts.peerSize < 2^64
  nodes : Mapped (fun (id,a) (id',n) => id = id' ∧ decodeNode names o m a = .ok n) names.nodes s.nodes
  peers : Mapped (fun (id,a) (id',count) => id = id' ∧
    word m s!"peer[{id}].refcount" (a+o.peerRefcount) 4 = .ok count) names.peers s.counts

theorem reconstruct_fields {names : Names} {o : AllowedipsProbe.Offsets}
    {m : DataMem} {s : State} (ok : reconstruct names o m = .ok s) :
    Reconstructed names o m s := by
  unfold reconstruct at ok
  obtain ⟨_,validated,ok⟩ := bind_ok ok
  unfold validate at validated
  obtain ⟨layout,validated⟩ := check_ok _ _ _ _ validated
  obtain ⟨unique,uniqueOk,validated⟩ := bind_ok validated
  obtain ⟨ranges,rangesOk,_⟩ := bind_ok validated
  obtain ⟨nodes,nodesOk,ok⟩ := bind_ok ok
  obtain ⟨peers,peersOk,ok⟩ := bind_ok ok
  have equal : ({nodes,counts := peers} : State) = s := Except.ok.inj ok
  subst s
  have uniqueness := forIn_ok (P := fun pairs : List (Nat×Nat) => (pairs.map Prod.fst).Nodup)
    (fun pairs _ before after run => by
      obtain ⟨valid,run⟩ := check_ok _ _ _ _ run
      have lengths : (pairs.map Prod.fst).eraseDups.length = pairs.length ∧
          (pairs.map Prod.snd).eraseDups.length = pairs.length := by simpa using valid
      exact ⟨(),(Except.ok.inj run).symm,
        nodup_of_eraseDups_length _ (by simpa using lengths.1)⟩) uniqueOk
  have bounded := forIn_ok (P := fun x : (Nat×Nat)×Nat => 0 < x.1.1 ∧ x.1.1+x.1.2 < 2^64)
    (fun x _ before after run => by
      obtain ⟨valid,run⟩ := check_ok _ _ _ _ run
      obtain ⟨rest,checked,run⟩ := bind_ok run
      exact ⟨(),(Except.ok.inj run).symm,by simpa using valid⟩) rangesOk
  refine ⟨by simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using layout,
    uniqueness _ (by simp),uniqueness _ (by simp),?_,?_,?_,?_⟩
  · intro id a member
    have present : (a,o.nodeSize) ∈ names.nodes.map (fun x => (x.2,o.nodeSize)) ++
        names.peers.map (fun x => (x.2,Layouts.peerSize)) := by
      exact List.mem_append_left _ (List.mem_map.mpr ⟨(id,a),member,rfl⟩)
    obtain ⟨i,atIndex⟩ := List.mem_iff_getElem?.mp present
    exact bounded ((a,o.nodeSize),i) (List.mk_mem_zipIdx_iff_getElem?.mpr atIndex)
  · intro id a member
    have present : (a,Layouts.peerSize) ∈ names.nodes.map (fun x => (x.2,o.nodeSize)) ++
        names.peers.map (fun x => (x.2,Layouts.peerSize)) := by
      exact List.mem_append_right _ (List.mem_map.mpr ⟨(id,a),member,rfl⟩)
    obtain ⟨i,atIndex⟩ := List.mem_iff_getElem?.mp present
    exact bounded ((a,Layouts.peerSize),i) (List.mk_mem_zipIdx_iff_getElem?.mpr atIndex)
  · apply (mapM_ok nodesOk).imp
    rintro ⟨id,a⟩ ⟨id',n⟩ run
    obtain ⟨decoded,read,run⟩ := bind_ok run
    have eq : (id,decoded) = (id',n) := Except.ok.inj run
    cases eq
    exact ⟨rfl,read⟩
  · apply (mapM_ok peersOk).imp
    rintro ⟨id,a⟩ ⟨id',count⟩ run
    obtain ⟨decoded,read,run⟩ := bind_ok run
    have eq : (id,decoded) = (id',count) := Except.ok.inj run
    cases eq
    exact ⟨rfl,read⟩

#print axioms decodeNode_fields
#print axioms reconstruct_fields
end Trie
end Binary.Pair
