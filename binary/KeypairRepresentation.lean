import Layouts
import Memory

namespace Binary.Layouts

private theorem unchanged (before after : Mem 64) (writes : BitVec 64 → Prop)
    (same : EqualOutside writes before after) (base : BitVec 64) (size : Nat)
    (disjoint : ∀ i < size, ¬writes (base + .ofNat 64 i))
    (off n : Nat) (bound : off + n ≤ size) :
    before.loadInt (base + .ofNat 64 off) n = after.loadInt (base + .ofNat 64 off) n := by
  apply same.loadInt
  intro i hi
  have h := disjoint (off + i) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h

/-- Exact counter and bitmap preservation through physical byte framing. -/
theorem ReplayFields.frame {before after : Mem 64} {writes : BitVec 64 → Prop}
    (same : EqualOutside writes before after) (base : BitVec 64)
    (counter : Leanux.WG.ReplayCounter)
    (disjoint : ∀ i < replaySize, ¬writes (base + .ofNat 64 i))
    (represented : ReplayFields before base counter) : ReplayFields after base counter := by
  rcases represented with ⟨count, length, words⟩
  refine ⟨(unchanged _ _ _ same base replaySize disjoint replay_counter 8 (by decide)).symm.trans count,
    length, ?_⟩
  intro i hi
  have small : i < 128 := by simpa only [length, replayWords] using hi
  exact (unchanged _ _ _ same base replaySize disjoint
    (replay_backtrack + i * replayWordBytes) replayWordBytes
    (by simp only [replaySize, replay_backtrack, replayWordBytes]; omega)).symm.trans (words i hi)

/-- The snapshot does not read the keypair's embedded index entry. Lookup
    may clear that entry's peer pointer even while all snapshot fields remain
    exactly unchanged; requiring the entire keypair block to be read-only
    would be unnecessarily strong for that path. -/
def KeypairSnapshotFootprint (base address : BitVec 64) : Prop :=
  InRange (base + .ofNat 64 keypair_internal_id) 8 address ∨
  InRange (base + .ofNat 64 keypair_receiving_counter) replaySize address

theorem KeypairSnapshotFields.frame_reads {before after : Mem 64} {writes : BitVec 64 → Prop}
    (same : EqualOutside writes before after) (base : BitVec 64) (keypair : Leanux.WG.Keypair)
    (disjoint : ∀ address, KeypairSnapshotFootprint base address → ¬writes address)
    (represented : KeypairSnapshotFields before base keypair) :
    KeypairSnapshotFields after base keypair := by
  constructor
  · exact (same.loadInt _ 8 (fun i hi => disjoint _ (.inl ⟨i, hi, rfl⟩))).symm.trans represented.1
  · apply ReplayFields.frame same _ _ _ represented.2
    intro i hi
    exact disjoint _ (.inr ⟨i, hi, rfl⟩)

private theorem after_entry (base : BitVec 64) (off n : Nat)
    (low : 8 ≤ off) (high : off + n ≤ 2^64) (address : BitVec 64)
    (read : InRange (base + .ofNat 64 off) n address) : ¬InRange base 8 address := by
  rintro ⟨j, hj, written⟩
  rcases read with ⟨i, hi, read⟩
  have equal : base + .ofNat 64 (off + i) = base + .ofNat 64 j := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using read.symm.trans written
  have values := congrArg (fun x : BitVec 64 => (x - base).toNat) equal
  simp only [BitVec.add_comm base, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at values
  omega

/-- The dead-peer write is inside a keypair object when the found entry is a
    keypair entry. Its NULL store still preserves the exact lifetime/replay
    snapshot, with no positive-peer or whole-object read-only premise. -/
theorem entry_peer_store_preserves_snapshot (memory : Mem 64) (base : BitVec 64)
    (peerWord : Int) (keypair : Leanux.WG.Keypair)
    (represented : KeypairSnapshotFields memory base keypair) :
    KeypairSnapshotFields (memory.storeInt base 8 peerWord) base keypair := by
  apply KeypairSnapshotFields.frame_reads (storeInt_frame memory base 8 peerWord) base keypair _ represented
  intro address read
  cases read with
  | inl identity => exact after_entry base keypair_internal_id 8 (by decide) (by decide) address identity
  | inr replay => exact after_entry base keypair_receiving_counter replaySize (by decide) (by decide) address replay

#print axioms entry_peer_store_preserves_snapshot

theorem KeypairSnapshotFields.frame {before after : Mem 64} {writes : BitVec 64 → Prop}
    (same : EqualOutside writes before after) (base : BitVec 64) (keypair : Leanux.WG.Keypair)
    (disjoint : ∀ i < keypairSize, ¬writes (base + .ofNat 64 i))
    (represented : KeypairSnapshotFields before base keypair) :
    KeypairSnapshotFields after base keypair := by
  refine ⟨(unchanged _ _ _ same base keypairSize disjoint keypair_internal_id 8
    (by decide)).symm.trans represented.1, ?_⟩
  apply ReplayFields.frame same _ _ _ represented.2
  intro i hi
  have h := disjoint (keypair_receiving_counter + i)
    (by simp only [keypair_receiving_counter, keypairSize, replaySize] at *; omega)
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h

theorem KeypairCounterField.frame {before after : Mem 64} {writes : BitVec 64 → Prop}
    (same : EqualOutside writes before after) (counter : Nat)
    (disjoint : ∀ i < 8, ¬writes (keypairCounterAddress + .ofNat 64 i))
    (represented : KeypairCounterField before counter) : KeypairCounterField after counter :=
  (same.loadInt keypairCounterAddress 8 disjoint).symm.trans represented

/-- Pointer-shaped slots are hand-written. Names are supplied by the live
    object relation; this local field predicate does not establish membership
    or injectivity of that relation. -/
def keypairPointer (addresses : Leanux.WG.KeypairId → BitVec 64) :
    Option Leanux.WG.KeypairId → BitVec 64
  | none => 0
  | some id => addresses id

def Slots (addresses : Leanux.WG.KeypairId → BitVec 64) (memory : Mem 64)
    (base : BitVec 64) (peer : Leanux.WG.Peer) : Prop :=
  memory.loadInt (base + .ofNat 64 slots_current_keypair) 8 =
    some (keypairPointer addresses peer.keypairCurrent).toNat ∧
  memory.loadInt (base + .ofNat 64 slots_previous_keypair) 8 =
    some (keypairPointer addresses peer.keypairPrevious).toNat ∧
  memory.loadInt (base + .ofNat 64 slots_next_keypair) 8 =
    some (keypairPointer addresses peer.keypairNext).toNat

theorem Slots.frame (addresses : Leanux.WG.KeypairId → BitVec 64)
    {before after : Mem 64} {writes : BitVec 64 → Prop}
    (same : EqualOutside writes before after) (base : BitVec 64) (peer : Leanux.WG.Peer)
    (disjoint : ∀ i < slotsSize, ¬writes (base + .ofNat 64 i))
    (represented : Slots addresses before base peer) : Slots addresses after base peer :=
  ⟨(unchanged _ _ _ same base slotsSize disjoint slots_current_keypair 8 (by decide)).symm.trans represented.1,
    (unchanged _ _ _ same base slotsSize disjoint slots_previous_keypair 8 (by decide)).symm.trans represented.2.1,
    (unchanged _ _ _ same base slotsSize disjoint slots_next_keypair 8 (by decide)).symm.trans represented.2.2⟩

/-- The physical replay bytes determine the entire mirrored replay value;
    this relation cannot silently weaken a counter or bitmap property. -/
theorem ReplayFields.functional (memory : Mem 64) (base : BitVec 64)
    (first second : Leanux.WG.ReplayCounter)
    (hfirst : ReplayFields memory base first) (hsecond : ReplayFields memory base second) :
    first = second := by
  have counter : first.counter = second.counter := by
    have h := Option.some.inj (hfirst.1.symm.trans hsecond.1)
    omega
  have bitmap : first.backtrack = second.backtrack := by
    apply Array.ext (hfirst.2.1.trans hsecond.2.1.symm)
    intro i hi hj
    have h := Option.some.inj ((hfirst.2.2 i hi).symm.trans (hsecond.2.2 i hj))
    omega
  cases first
  cases second
  cases counter
  cases bitmap
  rfl

theorem KeypairSnapshotFields.functional (memory : Mem 64) (base : BitVec 64)
    (first second : Leanux.WG.Keypair)
    (hfirst : KeypairSnapshotFields memory base first)
    (hsecond : KeypairSnapshotFields memory base second) :
    first.internalId = second.internalId ∧ first.receivingCounter = second.receivingCounter := by
  constructor
  · have h := Option.some.inj (hfirst.1.symm.trans hsecond.1)
    omega
  · exact ReplayFields.functional memory _ _ _ hfirst.2 hsecond.2

#print axioms ReplayFields.functional
#print axioms KeypairSnapshotFields.functional

#print axioms KeypairSnapshotFields.frame_reads
#print axioms ReplayFields.frame
#print axioms KeypairSnapshotFields.frame
#print axioms KeypairCounterField.frame
#print axioms Slots.frame

theorem SymmetricFields.functional (memory : Mem 64) (base : BitVec 64)
    (first second : Leanux.WG.SymmetricKey)
    (hfirst : SymmetricFields memory base first) (hsecond : SymmetricFields memory base second) :
    first = second := by
  have key := Option.some.inj (hfirst.1.symm.trans hsecond.1)
  have birthBits : first.birthdate.toBitVec = second.birthdate.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    have h := Option.some.inj (hfirst.2.1.symm.trans hsecond.2.1)
    omega
  have birth := Int64.toBitVec_inj.mp birthBits
  have valid : first.isValid = second.isValid := by
    have h := Option.some.inj (hfirst.2.2.symm.trans hsecond.2.2)
    cases hf : first.isValid <;> cases hs : second.isValid <;> simp_all
  cases first
  cases second
  cases key
  cases birth
  cases valid
  rfl

/-- At an embedded keypair entry the two physical views necessarily read
    the same pointer. A stale mirror alias cannot be hidden by this relation. -/
theorem KeypairFields.entry_peer_coherent (memory : Mem 64) (base kpWord entryWord : BitVec 64)
    (keypair : Leanux.WG.Keypair) (kind index : BitVec 32)
    (keypairFields : KeypairFields memory base kpWord keypair)
    (entryFields : EntryFields memory (base + .ofNat 64 keypair_entry) entryWord kind index) :
    kpWord = entryWord := by
  apply BitVec.eq_of_toNat_eq
  have entry : memory.loadInt ((base + .ofNat 64 keypair_entry) + .ofNat 64 entry_peer) 8 =
      some (entryWord.toNat : Int) := entryFields.1
  have h := Option.some.inj
    (keypairFields.2.2.2.2.2.2.2.symm.trans (by
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using entry))
  omega

/-- All scalar/array fields are determined by physical bytes. The peer ID
    is interpreted through the separately checked live pointer naming map. -/
theorem KeypairFields.functional (memory : Mem 64) (base firstWord secondWord : BitVec 64)
    (first second : Leanux.WG.Keypair)
    (hfirst : KeypairFields memory base firstWord first)
    (hsecond : KeypairFields memory base secondWord second) :
    { first with peer := second.peer } = second ∧ firstWord = secondWord := by
  obtain ⟨identity, replay⟩ := KeypairSnapshotFields.functional memory base first second hfirst.1 hsecond.1
  have sending := SymmetricFields.functional memory _ _ _ hfirst.2.1 hsecond.2.1
  have receiving := SymmetricFields.functional memory _ _ _ hfirst.2.2.1 hsecond.2.2.1
  have sendingCounter : first.sendingCounter = second.sendingCounter := by
    have h := Option.some.inj (hfirst.2.2.2.1.symm.trans hsecond.2.2.2.1)
    omega
  have remoteIndex : first.remoteIndex = second.remoteIndex := by
    have h := Option.some.inj (hfirst.2.2.2.2.1.symm.trans hsecond.2.2.2.2.1)
    omega
  have initiator : first.iAmTheInitiator = second.iAmTheInitiator := by
    have h := Option.some.inj (hfirst.2.2.2.2.2.1.symm.trans hsecond.2.2.2.2.2.1)
    cases hf : first.iAmTheInitiator <;> cases hs : second.iAmTheInitiator <;> simp_all
  have refcount : first.refcount = second.refcount := by
    have h := Option.some.inj (hfirst.2.2.2.2.2.2.1.symm.trans hsecond.2.2.2.2.2.2.1)
    omega
  constructor
  · cases first
    cases second
    cases identity
    cases replay
    cases sending
    cases receiving
    cases sendingCounter
    cases remoteIndex
    cases initiator
    cases refcount
    rfl
  · apply BitVec.eq_of_toNat_eq
    have h := Option.some.inj (hfirst.2.2.2.2.2.2.2.symm.trans hsecond.2.2.2.2.2.2.2)
    omega

#print axioms SymmetricFields.functional
#print axioms KeypairFields.entry_peer_coherent
#print axioms KeypairFields.functional

theorem SymmetricFields.frame {before after : Mem 64} {writes : BitVec 64 → Prop}
    (same : EqualOutside writes before after) (base : BitVec 64)
    (key : Leanux.WG.SymmetricKey)
    (disjoint : ∀ i < symmetricSize, ¬writes (base + .ofNat 64 i))
    (represented : SymmetricFields before base key) : SymmetricFields after base key := by
  refine ⟨?_, ?_, ?_⟩
  · have bytes := same.loadBytes (base + .ofNat 64 symmetric_key) 32 (by
      intro i hi
      simpa [symmetric_key] using disjoint i (by simp only [symmetricSize]; omega))
    exact bytes.symm.trans represented.1
  · exact (unchanged _ _ _ same base symmetricSize disjoint symmetric_birthdate 8
      (by decide)).symm.trans represented.2.1
  · exact (unchanged _ _ _ same base symmetricSize disjoint symmetric_is_valid 1
      (by decide)).symm.trans represented.2.2

theorem KeypairFields.frame {before after : Mem 64} {writes : BitVec 64 → Prop}
    (same : EqualOutside writes before after) (base peerWord : BitVec 64)
    (keypair : Leanux.WG.Keypair)
    (disjoint : ∀ i < keypairSize, ¬writes (base + .ofNat 64 i))
    (represented : KeypairFields before base peerWord keypair) :
    KeypairFields after base peerWord keypair := by
  have part (off size : Nat) (bound : off + size ≤ keypairSize) :
      ∀ i < size, ¬writes ((base + .ofNat 64 off) + .ofNat 64 i) := by
    intro i hi
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using disjoint (off + i) (by omega)
  exact ⟨KeypairSnapshotFields.frame same base keypair disjoint represented.1,
    SymmetricFields.frame same _ _ (part keypair_sending symmetricSize (by decide)) represented.2.1,
    SymmetricFields.frame same _ _ (part keypair_receiving symmetricSize (by decide)) represented.2.2.1,
    (unchanged _ _ _ same base keypairSize disjoint keypair_sending_counter 8 (by decide)).symm.trans represented.2.2.2.1,
    (unchanged _ _ _ same base keypairSize disjoint keypair_remote_index 4 (by decide)).symm.trans represented.2.2.2.2.1,
    (unchanged _ _ _ same base keypairSize disjoint keypair_i_am_the_initiator 1 (by decide)).symm.trans represented.2.2.2.2.2.1,
    (unchanged _ _ _ same base keypairSize disjoint keypair_refcount 4 (by decide)).symm.trans represented.2.2.2.2.2.2.1,
    (unchanged _ _ _ same base keypairSize disjoint (keypair_entry + entry_peer) 8 (by decide)).symm.trans represented.2.2.2.2.2.2.2⟩

#print axioms SymmetricFields.frame
#print axioms KeypairFields.frame

/-- Local pointer-name validity. A complete object relation must separately
    justify the live domain from allocation/ownership history; neither
    readable bytes nor the three peer slots determine that domain. -/
structure LiveKeypairNames (live : Leanux.WG.KeypairId → Prop) where
  address : Leanux.WG.KeypairId → BitVec 64
  nonnull : ∀ id, live id → address id ≠ 0
  unique : ∀ i j, live i → live j → address i = address j → i = j

def LiveOption (live : Leanux.WG.KeypairId → Prop) : Option Leanux.WG.KeypairId → Prop
  | none => True
  | some id => live id

theorem LiveKeypairNames.pointer_injective {live} (names : LiveKeypairNames live)
    (first second : Option Leanux.WG.KeypairId)
    (hf : LiveOption live first) (hs : LiveOption live second)
    (equal : keypairPointer names.address first = keypairPointer names.address second) :
    first = second := by
  cases first with
  | none =>
    cases second with
    | none => rfl
    | some id => exact False.elim (names.nonnull id hs equal.symm)
  | some id =>
    cases second with
    | none => exact False.elim (names.nonnull id hf equal)
    | some other => exact congrArg some (names.unique id other hf hs equal)

/-- Exact physical slot words plus valid names determine all three mirror
    identities; `some id` can neither denote NULL nor alias another live ID. -/
theorem Slots.functional {live} (names : LiveKeypairNames live)
    (memory : Mem 64) (base : BitVec 64) (first second : Leanux.WG.Peer)
    (hf : Slots names.address memory base first) (hs : Slots names.address memory base second)
    (firstLive : LiveOption live first.keypairCurrent ∧
      LiveOption live first.keypairPrevious ∧ LiveOption live first.keypairNext)
    (secondLive : LiveOption live second.keypairCurrent ∧
      LiveOption live second.keypairPrevious ∧ LiveOption live second.keypairNext) :
    first.keypairCurrent = second.keypairCurrent ∧
      first.keypairPrevious = second.keypairPrevious ∧ first.keypairNext = second.keypairNext := by
  have pointer (a b : Option Leanux.WG.KeypairId) (ha : LiveOption live a) (hb : LiveOption live b)
      (h : (keypairPointer names.address a).toNat = (keypairPointer names.address b).toNat) : a = b :=
    names.pointer_injective a b ha hb (BitVec.eq_of_toNat_eq h)
  refine ⟨pointer _ _ firstLive.1 secondLive.1 ?_,
    pointer _ _ firstLive.2.1 secondLive.2.1 ?_, pointer _ _ firstLive.2.2 secondLive.2.2 ?_⟩
  · have h := Option.some.inj (hf.1.symm.trans hs.1); omega
  · have h := Option.some.inj (hf.2.1.symm.trans hs.2.1); omega
  · have h := Option.some.inj (hf.2.2.symm.trans hs.2.2); omega

#print axioms LiveKeypairNames.pointer_injective
#print axioms Slots.functional
end Binary.Layouts
