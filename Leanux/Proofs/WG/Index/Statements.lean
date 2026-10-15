import Leanux.Proofs.WG.Index.DrawRecords
import Leanux.Proofs.WG.Index.Allocation
import Leanux.Proofs.WG.Index.CorpusDraws

/-! H2's original-operation table contracts. Reachable owner/peer-word
coherence remains a separate obligation. -/
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config

/-- Original removal deletes all rows for the embedded owner, changes no
other device field, and preserves numeric-index and owner uniqueness. -/
theorem original_index_remove (owner : IndexOwner) (d : Device)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable) :
    Returns (indexRemove owner) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some { d with indexTable := removeOwner owner d.indexTable } ∧
        UniqueIndices (removeOwner owner d.indexTable) ∧
        UniqueOwners (removeOwner owner d.indexTable)) := by
  intro w pre
  obtain ⟨result, final, run, device⟩ := indexRemove_exact owner d w pre
  exact ⟨result, final, run, device, remove_indices owner _ indices, remove_owners owner _ owners⟩

/-- The landed keypair-removal operation is owner-specialized indexRemove;
it removes the entry even when its separately stored peer word is NULL. -/
theorem original_keypair_index_remove (id : KeypairId) (d : Device)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable) :
    Returns (indexRemove (.keypair id)) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some { d with indexTable := removeOwner (.keypair id) d.indexTable } ∧
        UniqueIndices (removeOwner (.keypair id) d.indexTable) ∧
        UniqueOwners (removeOwner (.keypair id) d.indexTable)) :=
  original_index_remove (.keypair id) d indices owners

/-- Original replacement relabels the handshake row in place, preserves
numeric uniqueness, and preserves owner uniqueness when the destination
keypair is not already hashed. Every stored peer word is unchanged. -/
theorem original_index_replace (pid : PeerId) (kp : KeypairId) (d : Device)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable)
    (fresh : ∀ e ∈ d.indexTable, e.owner ≠ .keypair kp) :
    Returns (indexReplaceHandshake pid kp) (fun w => w.k.wg = some d)
      (fun hashed w =>
        let updated := if hashed then { d with indexTable := replaceOwner pid kp d.indexTable } else d
        hashed = d.indexTable.any (·.owner == .handshake pid) ∧
        w.k.wg = some updated ∧ UniqueIndices updated.indexTable ∧ UniqueOwners updated.indexTable) := by
  intro w pre
  obtain ⟨hashed, final, run, value, device⟩ := indexReplace_exact pid kp d w pre
  refine ⟨hashed, final, run, value, device, ?_, ?_⟩
  · cases hashed <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact indices
    · exact replace_indices pid kp _ indices
  · cases hashed <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact owners
    · exact replace_owners pid kp _ owners fresh

/-- Every normally returning original insertion removes its old owner row
first, then chooses an index absent from the remaining table. It preserves
both uniqueness properties; this does not promise success on missing draws. -/
theorem original_index_insert (owner : IndexOwner) (d : Device)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable) :
    Ensures (indexInsert owner) (fun w => w.k.wg = some d)
      (fun index w =>
        let table := { index, owner } :: removeOwner owner d.indexTable
        w.k.wg = some { d with indexTable := table } ∧
          UniqueIndices table ∧ UniqueOwners table) := by
  intro w index final pre run
  obtain ⟨device, fresh⟩ := indexInsert_exact owner d w index final pre run
  refine ⟨device, insert_indices owner index _ indices ?_, insert_owners owner index _ owners⟩
  intro e member
  have absent := List.any_eq_false.mp fresh e member
  have different : e.index ≠ index := by simpa using absent
  exact Ne.symm different

/-- Original lookup leaves the numeric-index/owner table unchanged. Any
returned owner belongs to an initial row with the requested index and an
allowed kind. -/
theorem original_index_lookup (kinds : List IndexKind) (index : Nat) (d : Device) :
    Ensures (indexLookup kinds index) (fun w => w.k.wg = some d)
      (fun result w => tableAt w = some d.indexTable ∧
        ∀ owner pid, result = some (owner, pid) →
          ∃ e ∈ d.indexTable, e.index = index ∧ e.owner = owner ∧ kinds.contains e.kind = true) :=
  indexLookup_owner kinds index d

/-- A matching permitted entry with a NULL stored peer word returns nothing
and performs the original NULL store, with all device effects specified. -/
theorem original_index_lookup_null (kinds : List IndexKind) (index : Nat)
    (owner : IndexOwner) (d : Device)
    (table : d.indexTable.find? (·.index == index) = some { index, owner })
    (permitted : kinds.contains (IndexEntry.kind { index, owner }) = true)
    (word : ownerWord d owner = some none) :
    Returns (indexLookup kinds index) (fun w => w.k.wg = some d)
      (fun result w => result = none ∧ w.k.wg = some (writeOwnerWord d owner none)) :=
  indexLookup_null kinds index owner d table permitted word

/-- A matching permitted entry referencing a zero-reference peer returns
nothing and stores NULL in that entry's owner, as the landed mirror does. -/
theorem original_index_lookup_zero_reference (kinds : List IndexKind) (index : Nat)
    (owner : IndexOwner) (d : Device)
    (table : d.indexTable.find? (·.index == index) = some { index, owner })
    (permitted : kinds.contains (IndexEntry.kind { index, owner }) = true)
    (pid : PeerId) (p : Peer) (word : ownerWord d owner = some (some pid))
    (resident : d.peers[pid]? = some p) (zero : p.refcount = 0) :
    Returns (indexLookup kinds index) (fun w => w.k.wg = some d)
      (fun result w => result = none ∧ w.k.wg = some (writeOwnerWord d owner none)) :=
  indexLookup_dead kinds index owner d table permitted pid p word resident zero

/-- A matching permitted entry with a resident, positively referenced peer
returns that owner and its stored peer identity, acquiring one reference.
The exact subsequent owner store retains that increment even for aliasing
handshake-owner and referenced-peer identities. -/
theorem original_index_lookup_live (kinds : List IndexKind) (index : Nat)
    (owner : IndexOwner) (d : Device)
    (table : d.indexTable.find? (·.index == index) = some { index, owner })
    (permitted : kinds.contains (IndexEntry.kind { index, owner }) = true)
    (pid : PeerId) (p : Peer) (word : ownerWord d owner = some (some pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) :
    Returns (indexLookup kinds index) (fun w => w.k.wg = some d)
      (fun result w => result = some (owner, pid) ∧
        w.k.wg = some (writeOwnerWord (acquirePeer d pid p) owner (some pid))) :=
  indexLookup_live kinds index owner d table permitted pid p word resident live bounded

/-- A finite contiguous recorded collision prefix followed by a fresh draw makes the
original insertion return that fresh index. Its record-derived budget suffices,
the unused suffix stays untouched, and both table uniqueness properties hold.
Collision and freshness are measured after removing this owner's old row. -/
theorem original_index_insert_recorded (owner : IndexOwner) (d : Device)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable)
    (collisions : List Draw) (fresh : Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (removeOwner owner d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (removeOwner owner d.indexTable).any (·.index == fresh.value) = false) :
    Returns (indexInsert owner)
      (fun w => w.k.wg = some d ∧ w.hidden = some (drawStream collisions fresh rest))
      (fun result w =>
        let table := { index := fresh.value, owner } :: removeOwner owner d.indexTable
        result = fresh.value ∧ w.k.wg = some { d with indexTable := table } ∧
          w.hidden = some rest ∧ UniqueIndices table ∧ UniqueOwners table) := by
  intro w pre
  obtain ⟨result, final, run, value, device, records⟩ :=
    indexInsert_records owner d collisions fresh rest allCollide isFresh w pre
  refine ⟨result, final, run, value, device, records,
    insert_indices owner fresh.value _ indices ?_, insert_owners owner fresh.value _ owners⟩
  intro e member
  have absent := List.any_eq_false.mp isFresh e member
  have different : e.index ≠ fresh.value := by simpa using absent
  exact Ne.symm different

/-- Two original insertions from an empty table consume the three index
values steered by s2_index_collision: the second retries the first value and
returns the third. This is a local composition, not an accepted runner trace. -/
theorem original_index_insert_corpus_draws (first second : PeerId)
    (different : first ≠ second) (d : Device) (empty : d.indexTable = [])
    (rest : List HiddenRecord) :
    Returns (corpusInsertPair first second)
      (fun w => w.k.wg = some d ∧ w.hidden = some
        (corpusCollisionDraw.record :: corpusCollisionDraw.record :: corpusFreshDraw.record :: rest))
      (fun result w => result = (0x0a0b0c0d, 0x11223344) ∧
        w.k.wg = some { d with indexTable :=
          [{ index := 0x11223344, owner := .handshake second },
           { index := 0x0a0b0c0d, owner := .handshake first }] } ∧
        w.hidden = some rest) :=
  corpusInsertPair_returns first second different d empty rest

/-- Bounds on resident and hashed keypair identities make a successful
original allocation fresh in both stores. It copies the supplied peer word,
leaves the index table untouched, and preserves those bounds. Allocation
failure returns no keypair and preserves the device and allocation counter. -/
theorem original_keypair_create_index_fresh (peer : Option PeerId) (d : Device)
    (counter : Nat) (owners : KeypairOwnersBounded d) (store : KeypairStoreBounded d) :
    Ensures (keypairCreate peer) (fun w => w.k.wg = some d ∧ w.k.keypairCounter = counter)
      (fun result w => match result with
        | none => w.k.wg = some d ∧ w.k.keypairCounter = counter
        | some id => id = d.nextKeypairId ∧
          w.k.wg = some (createdDevice d counter peer) ∧ w.k.keypairCounter = counter + 1 ∧
          d.keypairs[id]? = none ∧ (∀ e ∈ d.indexTable, e.owner ≠ .keypair id) ∧
          ownerWord (createdDevice d counter peer) (.keypair id) = some peer ∧
          KeypairOwnersBounded (createdDevice d counter peer) ∧
          KeypairStoreBounded (createdDevice d counter peer)) := by
  intro w result final pre run
  have effect := keypairCreate_exact peer d counter w result final pre run
  cases result with
  | none => exact effect
  | some id =>
    obtain ⟨rfl, hd, hc⟩ := effect
    exact ⟨rfl, hd, hc, store_bound_absent d store, bounded_fresh d owners,
      created_peer_word d counter peer, created_bounded d counter peer owners,
      created_store_bounded d counter peer store⟩

end Leanux.Proofs.WG.Index
