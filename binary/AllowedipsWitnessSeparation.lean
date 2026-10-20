import AllowedipsWitnessRelation
namespace Binary.AllowedipsWitness
open TrustBase AllowedipsRelation
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem range_nat (base : BitVec 64) (size : Nat) (a : BitVec 64)
    (bounded : base.toNat + size ≤ 2^64) (inside : InRange base size a) :
    base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + size := by
  obtain ⟨i, hi, rfl⟩ := inside
  have ilt : i < 2^64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ilt,
    Nat.mod_eq_of_lt (show base.toNat+i < 2^64 by omega)]
  omega

private theorem node_reads_location (id : Nat) (bits key : Nat) (n : Leanux.WG.AipNode)
    (small : id < 10) (index : childIndex n key < 2)
    (a : BitVec 64) (read : NodeReads nodeAddress bits key id n a) :
    0xa00000 ≤ a.toNat ∧ a.toNat < 0xa0a000 := by
  have loc (offset size : Nat) (bounded : offset+size ≤ 72)
      (inside : InRange (nodeAddress id + .ofNat 64 offset) size a) :
      0xa00000 ≤ a.toNat ∧ a.toNat < 0xa0a000 := by
    obtain ⟨i,hi,eq⟩ := inside
    have nums := congrArg BitVec.toNat eq
    simp [nodeAddress, BitVec.toNat_add] at nums
    omega
  rcases read with keyRead | cidrRead | ⟨_, peerRead | ⟨_, selA | selB | childRead⟩⟩
  · unfold KeyReads at keyRead
    split at keyRead
    · exact loc 32 4 (by decide) keyRead
    · rcases keyRead with high | ⟨_,low⟩
      · exact loc 32 8 (by decide) high
      · apply loc 40 8 (by decide)
        simpa only [AllowedipsLayout.bits, BitVec.add_assoc, show (32#64) + 8 = 40#64 from rfl] using low
  · exact loc 24 1 (by decide) cidrRead
  · exact loc 0 8 (by decide) peerRead
  · exact loc 25 1 (by decide) selA
  · exact loc 26 1 (by decide) selB
  · exact loc (8+8*childIndex n key) 8 (by omega) childRead

private theorem node_index (id : Fin 10) (key : Nat) : childIndex (row id).node key < 2 := by
  unfold childIndex
  exact Nat.mod_lt _ (by decide)

theorem trie4_location (a : BitVec 64)
    (read : TrieReads nodeAddress nodes (some 7) 32 key4 a) :
    0xa00000 ≤ a.toNat ∧ a.toNat < 0xa0a000 := by
  obtain ⟨id,n,reached,present,read⟩ := read
  have small : id < 10 := by
    rcases reached4 id reached with h | h | h | h | h <;> subst id <;> decide
  have found : nodes id = some (row ⟨id,small⟩).node := node_present ⟨id,small⟩
  rw [found] at present
  cases Option.some.inj present
  exact node_reads_location id 32 key4 _ small (node_index _ _) a read

theorem trie6_location (a : BitVec 64)
    (read : TrieReads nodeAddress nodes (some 1) 128 key6 a) :
    0xa00000 ≤ a.toNat ∧ a.toNat < 0xa0a000 := by
  obtain ⟨id,n,reached,present,read⟩ := read
  have small : id < 10 := by
    rcases reached6 id reached with h | h | h <;> subst id <;> decide
  have found : nodes id = some (row ⟨id,small⟩).node := node_present ⟨id,small⟩
  rw [found] at present
  cases Option.some.inj present
  exact node_reads_location id 128 key6 _ small (node_index _ _) a read

def config (wide : Bool) : Config := if wide then config6 else config4
def start (wide : Bool) : MachineState := if wide then initial6 else initial4

theorem reads_location (wide : Bool) (a : BitVec 64)
    (read : Reads (config wide) view a) :
    (0xa00000 ≤ a.toNat ∧ a.toNat < 0xa0a000) ∨
    (0x600000 ≤ a.toNat ∧ a.toNat < 0x605000) := by
  cases wide
  all_goals rcases read with trie | ⟨pid,focus,i,hi,eq⟩
  · exact .inl (trie4_location a trie)
  · change some 3 = some pid at focus
    cases Option.some.inj focus
    have nums := congrArg BitVec.toNat eq
    simp [config, config4, peerAddress, Layouts.peer_refcount, BitVec.toNat_add] at nums
    right; omega
  · exact .inl (trie6_location a trie)
  · change some 4 = some pid at focus
    cases Option.some.inj focus
    have nums := congrArg BitVec.toNat eq
    simp [config, config6, peerAddress, Layouts.peer_refcount, BitVec.toNat_add] at nums
    right; omega

theorem trie_location (wide : Bool) (a : BitVec 64)
    (read : TrieReads (config wide).nodes view.nodes (config wide).root (config wide).bits (config wide).key a) :
    0xa00000 ≤ a.toNat ∧ a.toNat < 0xa0a000 := by
  cases wide
  · exact trie4_location a read
  · exact trie6_location a read

theorem count_location (wide : Bool) (a : BitVec 64)
    (write : AllowedipsCountWrites (config wide) view a) :
    0x600000 ≤ a.toNat ∧ a.toNat < 0x605000 := by
  obtain ⟨pid,count,focus,eqCount,nonzero,field⟩ := write
  cases wide
  · change some 3 = some pid at focus
    cases Option.some.inj focus
    have loc := range_nat _ _ a (by decide) field
    change 0x603420 ≤ a.toNat ∧ a.toNat < 0x603424 at loc
    omega
  · change some 4 = some pid at focus
    cases Option.some.inj focus
    have loc := range_nat _ _ a (by decide) field
    change 0x604420 ≤ a.toNat ∧ a.toNat < 0x604424 at loc
    omega

theorem input_location (wide : Bool) (a : BitVec 64)
    (read : Allowedips.NetworkReads (start wide).data.regs.rdx.toBitVec (config wide).bits a) :
    0xb00000 ≤ a.toNat ∧ a.toNat < 0xb00010 := by
  cases wide
  all_goals
    have loc := range_nat _ _ a (by decide) read
    simp [start, initial4, initial6, initial, keyAddress, config, config4, config6] at loc
    omega

theorem stack_location (wide : Bool) (a : BitVec 64)
    (write : AllowedipsStackWrites (start wide) a) :
    0x400770 ≤ a.toNat ∧ a.toNat < 0x400800 := by
  have range : InRange (0x400770#64) 144 a := by cases wide <;> exact write
  exact range_nat _ _ a (by decide) range

theorem live_stack_location (wide : Bool) (a : BitVec 64)
    (write : AllowedipsLiveStack (start wide) a) :
    0x400770 ≤ a.toNat ∧ a.toNat < 0x400808 := by
  have range : InRange (0x400770#64) 152 a := by cases wide <;> exact write
  exact range_nat _ _ a (by decide) range

theorem buffer_location (a : BitVec 64) (write : KcovBufferBytes coverage a) :
    0x900000 ≤ a.toNat ∧ a.toNat < 0x902000 := range_nat _ _ a (by decide) write

theorem preempt_location (a : BitVec 64) (read : InRange preemptCountAddress 4 a) :
    0xffffffff81cc85c8 ≤ a.toNat ∧ a.toNat < 0xffffffff81cc85cc := range_nat _ _ a (by decide) read

def ServiceLocation (a : BitVec 64) : Prop :=
  (0xffffffff81cc85c0 ≤ a.toNat ∧ a.toNat < 0xffffffff81cc85c8) ∨
  (0xffffffff81cc85e0 ≤ a.toNat ∧ a.toNat < 0xffffffff81cc85e2) ∨
  (0x8006e0 ≤ a.toNat ∧ a.toNat < 0x800708) ∨
  (0x900000 ≤ a.toNat ∧ a.toNat < 0x902000)

def MetadataLocation (a : BitVec 64) : Prop :=
  (0xffffffff81cc85c0 ≤ a.toNat ∧ a.toNat < 0xffffffff81cc85c8) ∨
  (0xffffffff81cc85e0 ≤ a.toNat ∧ a.toNat < 0xffffffff81cc85e2) ∨
  (0x8006e0 ≤ a.toNat ∧ a.toNat < 0x800708)

theorem metadata_location (a : BitVec 64) (read : AllowedipsMetadata coverage 512 a) :
    MetadataLocation a := by
  rcases read with h | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h | h⟩ | ⟨_,h⟩
  all_goals
    have loc := range_nat _ _ a (by decide) h
    simp [coverage, currentTaskAddress, softirqPendingAddress] at loc
    unfold MetadataLocation
    omega

theorem service_location (a : BitVec 64) (read : AllowedipsServiceBytes coverage 512 a) :
    ServiceLocation a := by
  rcases read with metadata | ⟨_,header | buffer⟩
  · have loc := metadata_location a metadata
    unfold MetadataLocation at loc
    unfold ServiceLocation
    omega
  · have loc := range_nat _ _ a (by decide) header
    change 0x900000 ≤ a.toNat ∧ a.toNat < 0x900008 at loc
    unfold ServiceLocation
    omega
  · have loc := buffer_location a buffer
    exact .inr (.inr (.inr loc))

#print axioms reads_location
#print axioms service_location
end Binary.AllowedipsWitness
