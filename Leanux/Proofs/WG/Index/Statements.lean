import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Index.View
import Leanux.Proofs.WG.Index.PeerRelease
import Leanux.Proofs.WG.Index.DrawExhaustion
import Leanux.Proofs.WG.Index.DrawRecords
import Leanux.Proofs.WG.Index.ReleaseBounds
import Leanux.Proofs.WG.Index.CorpusDraws
import Leanux.Proofs.WG.Index.OwnerCreation
import Leanux.Proofs.WG.Index.LookupMiss
import Leanux.Proofs.WG.Index.LifecycleSource

/-! H2's original-operation table contracts. Reachable owner/peer-word
coherence remains a separate obligation. -/
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config

/-- Original removal deletes all rows for the embedded owner, changes no
other device field, and preserves numeric-index and owner uniqueness. -/
theorem original_index_remove (owner : IndexOwner) (d : Device)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable) :
    Campaign2.Returns (indexRemove owner) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some { d with indexTable := removeOwner owner d.indexTable } ∧
        UniqueIndices (removeOwner owner d.indexTable) ∧
        UniqueOwners (removeOwner owner d.indexTable)) := by
  intro w pre
  obtain ⟨result, final, run, device⟩ := indexRemove_exact owner d w pre
  exact ⟨result, final, run, device, remove_indices owner _ indices, remove_owners owner _ owners⟩

/-- The landed keypair-removal operation is owner-specialized indexRemove;
it removes the entry even when its separately stored peer word is NULL. -/
theorem original_keypair_index_remove (id : KeypairId) (d : Device)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable) :
    Campaign2.Returns (indexRemove (.keypair id)) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some { d with indexTable := removeOwner (.keypair id) d.indexTable } ∧
        UniqueIndices (removeOwner (.keypair id) d.indexTable) ∧
        UniqueOwners (removeOwner (.keypair id) d.indexTable)) :=
  original_index_remove (.keypair id) d indices owners

/-- Original replacement relabels the handshake row in place, preserves
numeric uniqueness, and preserves owner uniqueness when the destination
keypair is not already hashed. Every stored peer word is unchanged. -/
theorem original_index_replace (pid : PeerId) (kp : KeypairId) (d : Device)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable)
    (fresh : ∀ e ∈ d.indexTable, e.owner ≠ .keypair kp) :
    Campaign2.Returns (indexReplaceHandshake pid kp) (fun w => w.wg.device = some d)
      (fun hashed w =>
        let updated := if hashed then { d with indexTable := replaceOwner pid kp d.indexTable } else d
        hashed = d.indexTable.any (·.owner == .handshake pid) ∧
        w.wg.device = some updated ∧ UniqueIndices updated.indexTable ∧ UniqueOwners updated.indexTable) := by
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
    Campaign2.Ensures (indexInsert owner) (fun w => w.wg.device = some d)
      (fun index w =>
        let table := { index, owner } :: removeOwner owner d.indexTable
        w.wg.device = some { d with indexTable := table } ∧
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
    Campaign2.Ensures (indexLookup kinds index) (fun w => w.wg.device = some d)
      (fun result w => View.tableAt w = some d.indexTable ∧
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
    Campaign2.Returns (indexLookup kinds index) (fun w => w.wg.device = some d)
      (fun result w => result = none ∧ w.wg.device = some (writeOwnerWord d owner none)) :=
  indexLookup_null kinds index owner d table permitted word

/-- A matching permitted entry referencing a zero-reference peer returns
nothing and stores NULL in that entry's owner, as the landed mirror does. -/
theorem original_index_lookup_zero_reference (kinds : List IndexKind) (index : Nat)
    (owner : IndexOwner) (d : Device)
    (table : d.indexTable.find? (·.index == index) = some { index, owner })
    (permitted : kinds.contains (IndexEntry.kind { index, owner }) = true)
    (pid : PeerId) (p : Peer) (word : ownerWord d owner = some (some pid))
    (resident : d.peers[pid]? = some p) (zero : p.refcount = 0) :
    Campaign2.Returns (indexLookup kinds index) (fun w => w.wg.device = some d)
      (fun result w => result = none ∧ w.wg.device = some (writeOwnerWord d owner none)) :=
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
    Campaign2.Returns (indexLookup kinds index) (fun w => w.wg.device = some d)
      (fun result w => result = some (owner, pid) ∧
        w.wg.device = some (writeOwnerWord (acquirePeer d pid p) owner (some pid))) :=
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
    Campaign2.Returns (indexInsert owner)
      (fun w => w.wg.device = some d ∧ w.ambient.hidden = some (drawStream collisions fresh rest))
      (fun result w =>
        let table := { index := fresh.value, owner } :: removeOwner owner d.indexTable
        result = fresh.value ∧ w.wg.device = some { d with indexTable := table } ∧
          w.ambient.hidden = some rest ∧ UniqueIndices table ∧ UniqueOwners table) := by
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
    Campaign2.Returns (corpusInsertPair first second)
      (fun w => w.wg.device = some d ∧ w.ambient.hidden = some
        (corpusCollisionDraw.record :: corpusCollisionDraw.record :: corpusFreshDraw.record :: rest))
      (fun result w => result = (0x0a0b0c0d, 0x11223344) ∧
        w.wg.device = some { d with indexTable :=
          [{ index := 0x11223344, owner := .handshake second },
           { index := 0x0a0b0c0d, owner := .handshake first }] } ∧
        w.ambient.hidden = some rest) :=
  corpusInsertPair_returns first second different d empty rest

/-- Bounds on resident and hashed keypair identities make a successful
original allocation fresh in both stores. It copies the supplied peer word,
leaves the index table untouched, and preserves those bounds. Allocation
failure returns no keypair and preserves the device and allocation counter. -/
theorem original_keypair_create_index_fresh (peer : Option PeerId) (d : Device)
    (counter : Nat) (owners : KeypairOwnersBounded d) (store : KeypairStoreBounded d) :
    Campaign2.Ensures (keypairCreate peer) (fun w => w.wg.device = some d ∧ w.wg.keypairCounter = counter)
      (fun result w => match result with
        | none => w.wg.device = some d ∧ w.wg.keypairCounter = counter
        | some id => id = d.nextKeypairId ∧
          w.wg.device = some (createdDevice d counter peer) ∧ w.wg.keypairCounter = counter + 1 ∧
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

/-- Every normal completion of original initiation creation preserves
numeric index uniqueness, including its recorded insertion path. -/
theorem original_create_initiation_indices (pid : PeerId) :
    Campaign2.Ensures (createInitiation pid) View.IndicesSafe (fun _ w => View.IndicesSafe w) :=
  (ensures_iff _ _ _).mpr (createInitiation_indices_spec pid)

/-- Every normal completion of original response creation preserves
numeric index uniqueness, including its recorded insertion path. -/
theorem original_create_response_indices (pid : PeerId) :
    Campaign2.Ensures (createResponse pid) View.IndicesSafe (fun _ w => View.IndicesSafe w) :=
  (ensures_iff _ _ _).mpr (createResponse_indices_spec pid)

/-- Every normal completion of original session installation preserves
numeric index uniqueness through allocation, slot rotation, displaced-key
removal and handshake-to-keypair replacement. -/
theorem original_begin_session_indices (pid : PeerId) :
    Campaign2.Ensures (beginSession pid) View.IndicesSafe (fun _ w => View.IndicesSafe w) :=
  (ensures_iff _ _ _).mpr (beginSession_indices_spec pid)

/-- If the first equal-index entry is absent or has a disallowed kind,
original lookup returns nothing and leaves the whole device unchanged. It
does not skip a disallowed equal-index row in search of a later row. -/
theorem original_index_lookup_miss (kinds : List IndexKind) (index : Nat) (d : Device)
    (noMatch : ∀ e, d.indexTable.find? (·.index == index) = some e →
      kinds.contains e.kind = false) :
    Campaign2.Returns (indexLookup kinds index) (fun w => w.wg.device = some d)
      (fun result w => result = none ∧ w.wg.device = some d) :=
  indexLookup_miss kinds index d noMatch

/-- Original keypair release removes every row for that owner when requested
immediately or when the last reference is released; only the last release erases
the keypair. Other stored keypairs are unchanged and both table uniqueness
properties survive. The non-NULL peer word permits the mirror's dereference;
this says nothing about peer residency or references held in slots and packets. -/
theorem original_keypair_release (id : KeypairId) (now : Bool) (d : Device) (k : Keypair)
    (resident : d.keypairs[id]? = some k) (live : 0 < k.refcount) (word : k.peer ≠ none)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable) :
    Campaign2.Returns (keypairPut (some id) now) (fun w => w.wg.device = some d)
      (fun _ w =>
        let final := releasedDevice d id k now
        w.wg.device = some final ∧
        final.indexTable = (if now || k.refcount == 1 then
          removeOwner (.keypair id) d.indexTable else d.indexTable) ∧
        final.keypairs[id]? = (if k.refcount = 1 then none else some { k with refcount := k.refcount - 1 }) ∧
        (∀ other : KeypairId, id ≠ other → final.keypairs[other]? = d.keypairs[other]?) ∧
        UniqueIndices final.indexTable ∧ UniqueOwners final.indexTable) := by
  intro w pre
  obtain ⟨ret, final, run, device⟩ := keypairPut_exact id now d k resident live word w pre
  exact ⟨ret, final, run, device, released_table d id k now, released_keypair d id k now,
    fun other different => released_other_keypair d id other k now different,
    released_indices d id k now indices, released_owners d id k now owners⟩

/-- Original release preserves both bounds used to make future keypair
allocations fresh. The allocation identity does not change. This local closure
result does not initialize the bounds or prove them through every driver caller. -/
theorem original_keypair_release_allocation_bounds (id : KeypairId) (now : Bool)
    (d : Device) (k : Keypair) (resident : d.keypairs[id]? = some k)
    (live : 0 < k.refcount) (word : k.peer ≠ none)
    (owners : KeypairOwnersBounded d) (store : KeypairStoreBounded d) :
    Campaign2.Returns (keypairPut (some id) now) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some (releasedDevice d id k now) ∧
        (releasedDevice d id k now).nextKeypairId = d.nextKeypairId ∧
        KeypairOwnersBounded (releasedDevice d id k now) ∧
        KeypairStoreBounded (releasedDevice d id k now)) := by
  intro w pre
  obtain ⟨ret, final, run, device⟩ := keypairPut_exact id now d k resident live word w pre
  exact ⟨ret, final, run, device, released_next d id k now,
    released_owners_bounded d id k now owners, released_store_bounded d id k now resident store⟩

/-- Original initiation creation preserves uniqueness of embedded table owners
and the hashed-keypair allocation bound on normal completion, including removal
of the owner's previous row before insertion. Numeric uniqueness is separate. -/
theorem original_create_initiation_owners (pid : PeerId) :
    Campaign2.Ensures (createInitiation pid) View.OwnersBoundedSafe (fun _ w => View.OwnersBoundedSafe w) :=
  (ensures_iff _ _ _).mpr (createInitiation_owners_spec pid)

/-- Original response creation preserves embedded-owner uniqueness on every
normal completion, retaining the hashed-keypair allocation bound. Missing record
inputs are not promised to succeed. -/
theorem original_create_response_owners (pid : PeerId) :
    Campaign2.Ensures (createResponse pid) View.OwnersBoundedSafe (fun _ w => View.OwnersBoundedSafe w) :=
  (ensures_iff _ _ _).mpr (createResponse_owners_spec pid)

/-- Original session installation preserves embedded-owner uniqueness when all
initial hashed keypair identities precede the allocation cursor. Allocation
establishes a fresh destination; key derivation, clearing and slot rotation keep
it unhashed until replacement. This covers normal completion and early returns,
and retains the allocation bound for composition; it does not cover stopped
prefixes, store/slot safety or full reachable owner-word coherence. -/
theorem original_begin_session_owners (pid : PeerId) :
    Campaign2.Ensures (beginSession pid) View.OwnersBoundedSafe (fun _ w => View.OwnersBoundedSafe w) :=
  (ensures_iff _ _ _).mpr (beginSession_owners_spec pid)

/-- A finite contiguous stream consisting only of colliding draws is rejected
by the original insertion with the exact missing-index-record error. Collision
is tested after removing this owner's old row. The record-derived budget has
one extra turn, so rejection occurs at the next hidden read, before budget
exhaustion. This includes an empty stream and does not constrain the hiddenPlaceholders
flag. Recordless placeholder execution is outside its scope. It does not claim
an accepted runner trace or expose a final state on error. -/
theorem original_index_insert_exhausted (owner : IndexOwner) (d : Device) (draws : List Draw)
    (allCollide : ∀ draw ∈ draws,
      (removeOwner owner d.indexTable).any (·.index == draw.value) = true) :
    Campaign2.Observes (indexInsert owner)
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some (draws.map Draw.record))
      (fun _ out => out = .error (.hidden "no record left for index_draw")) := by
  intro w pre
  rw [indexInsert_exhausted owner d draws allCollide w pre.1 pre.2]
  rfl

/-- Original peer release decrements the count. The last release removes all
handshake-owner rows, erases the peer and charges its staged packets to txDropped;
other peers are unchanged. Numeric-index and embedded-owner uniqueness survive.
This executes the original identity-retirement operation but exports only device
effects; it does not establish safety of references in other objects. -/
theorem original_peer_release (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable) :
    Campaign2.Returns (peerPut (some pid)) (fun w => w.wg.device = some d)
      (fun _ w =>
        let final := releasedPeerDevice d pid p
        w.wg.device = some final ∧
        final.indexTable = (if p.refcount = 1 then removeOwner (.handshake pid) d.indexTable else d.indexTable) ∧
        final.peers[pid]? = (if p.refcount = 1 then none else some { p with refcount := p.refcount - 1 }) ∧
        (∀ other : PeerId, pid ≠ other → final.peers[other]? = d.peers[other]?) ∧
        final.txDropped = d.txDropped + (if p.refcount = 1 then p.staged.length else 0) ∧
        UniqueIndices final.indexTable ∧ UniqueOwners final.indexTable) := by
  intro w pre
  obtain ⟨ret, final, run, device⟩ := peerPut_exact pid d p resident live w pre
  exact ⟨ret, final, run, device, releasedPeer_table pid d p, releasedPeer_peer pid d p,
    fun other different => releasedPeer_other pid other d p different, releasedPeer_dropped pid d p,
    releasedPeer_indices pid d p indices, releasedPeer_owners pid d p owners⟩

/-- Original peer release preserves the keypair store and allocation cursor,
and both freshness bounds for later allocation. Removing handshake rows cannot
introduce a keypair owner beyond the cursor; whole-driver initialization and
preservation of these bounds are not claimed. -/
theorem original_peer_release_allocation_bounds (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (owners : KeypairOwnersBounded d) (store : KeypairStoreBounded d) :
    Campaign2.Returns (peerPut (some pid)) (fun w => w.wg.device = some d)
      (fun _ w =>
        let final := releasedPeerDevice d pid p
        w.wg.device = some final ∧ final.keypairs = d.keypairs ∧ final.nextKeypairId = d.nextKeypairId ∧
        KeypairOwnersBounded final ∧ KeypairStoreBounded final) := by
  intro w pre
  obtain ⟨ret, final, run, device⟩ := peerPut_exact pid d p resident live w pre
  exact ⟨ret, final, run, device, releasedPeer_keypairs pid d p, releasedPeer_next pid d p,
    releasedPeer_owners_bounded pid d p owners, releasedPeer_store_bounded pid d p store⟩

/-- The original runner initializer establishes the optional-device table
invariant for every fixture-flag combination. Only its core projection is
installed here; the remaining observed context is arbitrary. This is an
initial-state theorem, not preservation through a runner trace. -/
theorem original_initial_kernel_tables (rlimit : Nat)
    (net bare foreign stepped seccompChild : Bool) (s : Campaign2.Snapshot) :
    View.TablesSafe (initialSnapshot rlimit net bare foreign stepped seccompChild s) :=
  initialSnapshot_safe rlimit net bare foreign stepped seccompChild s

/-- Original setup always installs its empty device table and establishes
numeric uniqueness, owner uniqueness and the hashed-keypair allocation bound.
No pre-existing device or invariant is required. -/
theorem original_setup_tables : Campaign2.Returns wgSetup (fun _ => True)
    (fun _ s => s.wg.device = some setupDevice ∧ View.TablesSafe s) := by
  intro w pre
  obtain ⟨result, final, run, device⟩ := wgSetup_device w pre
  refine ⟨result, final, run, device, ?_⟩
  intro d present
  change final.k.wg = some d at present
  rw [device] at present
  cases present
  exact setupDevice_safe

/-- Every normal completion of original destruction leaves no device, hence
the optional-device table invariant holds. This does not promise destruction
completes, preserve intermediate states, or establish whole-driver coverage. -/
theorem original_destruct_tables : Campaign2.Ensures wgDestruct (fun _ => True)
    (fun _ s => s.wg.device = none ∧ View.TablesSafe s) := by
  intro w result final pre run
  have absent := wgDestruct_absent w result final pre run
  exact ⟨absent, absent_tables_safe _ absent⟩

end Leanux.Proofs.WG.Index
