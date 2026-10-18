import Leanux.Proofs.WG.Index.StagingIndexClaims
import Leanux.Proofs.WG.Index.ResponseIndexClaims
import Leanux.Proofs.WG.Index.LookupCoreSource
import Leanux.Proofs.WG.Index.IncomingIndexClaims
import Leanux.Proofs.WG.Index.ExpiryIndexClaims
import Leanux.Proofs.WG.Index.ReachedRunnerSource
import Leanux.Proofs.WG.Index.ReachedIndexSource
import Leanux.Proofs.WG.Index.CreationIndexClaims
import Leanux.Proofs.WG.Index.RetirementSessionClaims
import Leanux.Proofs.WG.Index.RetirementSinglePeerSource
import Leanux.Proofs.WG.Index.InitiationIndexSource
import Leanux.Proofs.WG.Index.CreatorCompatibleClaims
import Leanux.Proofs.WG.Index.CreatorIndexClaims
import Leanux.Proofs.WG.Index.RetirementDischargeClaims
import Leanux.Proofs.WG.Index.RetirementFirstPassSource
import Leanux.Proofs.WG.Index.BoundedSessionClaims
import Leanux.Proofs.WG.Index.RetirementPaymentSource
import Leanux.Proofs.WG.Index.HashSlotClearWorkerClaims
import Leanux.Proofs.WG.Index.RetirementClearWorkerClaims
import Leanux.Proofs.WG.Index.RetirementReleaseClaims
import Leanux.Proofs.WG.Index.RetirementBulkSource
import Leanux.Proofs.WG.Index.HashSlotReleaseClaims
import Leanux.Proofs.WG.Index.SelectedDrainClaims
import Leanux.Proofs.WG.Index.InitializedFundingClaims
import Leanux.Proofs.WG.Index.InitializedBoundsClaims
import Leanux.Proofs.WG.Index.HashSlotLookupClaims
import Leanux.Proofs.WG.Index.HashSlotClearClaims
import Leanux.Proofs.WG.Index.HashSlotRotationClaims
import Leanux.Proofs.WG.Index.HashSlotSessionClaims
import Leanux.Proofs.WG.Index.SessionInvariantClaims
import Leanux.Proofs.WG.Index.BulkRemovalClaims
import Leanux.Proofs.WG.Index.SessionLookupClaims
import Leanux.Proofs.WG.Index.SessionAliasClaims
import Leanux.Proofs.WG.Index.OwnerCoherencePersistentFindingClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceRetransmitClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceCallbackClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceQueuedClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceClearWorkerClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceZeroWorkerClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceAipRemovalClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceQuietRemovalClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceRemovalFindings
import Leanux.Proofs.WG.Index.OwnerCoherencePeerCreateClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceCreatorClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceInitiationClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceResponseClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceCookieClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceExpiryClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceReceiveClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceKeypairCallerClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceSessionClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceKeypairReleaseClaims
import Leanux.Proofs.WG.Index.PeerRemovalClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceReleaseClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceReleaseFindings
import Leanux.Proofs.WG.Index.OwnerCoherenceReleaseFrames
import Leanux.Proofs.WG.Index.ReceiveDataClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceAllocationClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceTableSource
import Leanux.Proofs.WG.Index.OwnerCoherenceClaims
import Leanux.Proofs.WG.Index.ConfirmationClaims
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Index.TableClaims
import Leanux.Proofs.WG.Index.View
import Leanux.Proofs.WG.Index.PeerReleaseClaims
import Leanux.Proofs.WG.Index.DrawExhaustion
import Leanux.Proofs.WG.Index.DrawRecords
import Leanux.Proofs.WG.Index.ReleaseBounds
import Leanux.Proofs.WG.Index.CorpusDraws
import Leanux.Proofs.WG.Index.OwnerCreation
import Leanux.Proofs.WG.Index.LookupMiss
import Leanux.Proofs.WG.Index.LifecycleSource
import Leanux.Proofs.WG.Index.LinkSource
import Leanux.Proofs.WG.Index.SendSource
import Leanux.Proofs.WG.Index.DispatchSource
import Leanux.Proofs.WG.Index.ResponseSource
import Leanux.Proofs.WG.Index.ConsumeSource
import Leanux.Proofs.WG.Index.StagedSource
import Leanux.Proofs.WG.Index.ReceiveSource
import Leanux.Proofs.WG.Index.TimerSource
import Leanux.Proofs.WG.Index.FlushSource
import Leanux.Proofs.WG.Index.SessionCoherenceSource
import Leanux.Proofs.WG.Index.SessionAllocationSource
import Leanux.Proofs.WG.Index.SessionSequenceSource
import Leanux.Proofs.WG.Index.LookupProvenanceSource
import Leanux.Proofs.WG.Index.LookupNoneSource

/-! H2's original-operation table contracts. Reachable owner/peer-word
coherence remains a separate obligation. -/
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config

/-- Original removal deletes all rows for the embedded owner, changes no
other device field, and preserves numeric-index and owner uniqueness. -/
theorem original_index_remove (owner : IndexOwner) (d : Device)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable) :
    Campaign2.Returns (liftIndex (indexRemove owner)) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some { d with indexTable := removeOwner owner d.indexTable } ∧
        UniqueIndices (removeOwner owner d.indexTable) ∧
        UniqueOwners (removeOwner owner d.indexTable)) :=
  TableClaims.original_index_remove owner d indices owners

/-- The landed keypair-removal operation is owner-specialized indexRemove;
it removes the entry even when its separately stored peer word is NULL. -/
theorem original_keypair_index_remove (id : KeypairId) (d : Device)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable) :
    Campaign2.Returns (liftIndex (indexRemove (.keypair id))) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some { d with indexTable := removeOwner (.keypair id) d.indexTable } ∧
        UniqueIndices (removeOwner (.keypair id) d.indexTable) ∧
        UniqueOwners (removeOwner (.keypair id) d.indexTable)) :=
  TableClaims.original_keypair_index_remove id d indices owners

/-- Original replacement relabels the handshake row in place, preserves
numeric uniqueness, and preserves owner uniqueness when the destination
keypair is not already hashed. Every stored peer word is unchanged. -/
theorem original_index_replace (pid : PeerId) (kp : KeypairId) (d : Device)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable)
    (fresh : ∀ e ∈ d.indexTable, e.owner ≠ .keypair kp) :
    Campaign2.Returns (liftIndex (indexReplaceHandshake pid kp)) (fun w => w.wg.device = some d)
      (fun hashed w =>
        let updated := if hashed then { d with indexTable := replaceOwner pid kp d.indexTable } else d
        hashed = d.indexTable.any (·.owner == .handshake pid) ∧
        w.wg.device = some updated ∧ UniqueIndices updated.indexTable ∧ UniqueOwners updated.indexTable) :=
  TableClaims.original_index_replace pid kp d indices owners fresh

/-- Every normally returning original insertion removes its old owner row
first, then chooses an index absent from the remaining table. It preserves
both uniqueness properties; this does not promise success on missing draws. -/
theorem original_index_insert (owner : IndexOwner) (d : Device)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable) :
    Campaign2.Ensures (liftIndex (indexInsert owner)) (fun w => w.wg.device = some d)
      (fun index w =>
        let table := { index, owner } :: removeOwner owner d.indexTable
        w.wg.device = some { d with indexTable := table } ∧
          UniqueIndices table ∧ UniqueOwners table) :=
  TableClaims.original_index_insert owner d indices owners

/-- Original lookup leaves the numeric-index/owner table unchanged. Any
returned owner belongs to an initial row with the requested index and an
allowed kind. -/
theorem original_index_lookup (kinds : List IndexKind) (index : Nat) (d : Device) :
    Campaign2.Ensures (indexLookup kinds index) (fun w => w.wg.device = some d)
      (fun result w => View.tableAt w = some d.indexTable ∧
        ∀ owner pid, result = some (owner, pid) →
          ∃ e ∈ d.indexTable, e.index = index ∧ e.owner = owner ∧ kinds.contains e.kind = true) :=
  TableClaims.original_index_lookup kinds index d

/-- A matching permitted entry with a NULL stored peer word returns nothing
and performs the original NULL store, with all device effects specified. -/
theorem original_index_lookup_null (kinds : List IndexKind) (index : Nat)
    (owner : IndexOwner) (d : Device)
    (table : d.indexTable.find? (·.index == index) = some { index, owner })
    (permitted : kinds.contains (IndexEntry.kind { index, owner }) = true)
    (word : ownerWord d owner = some none) :
    Campaign2.Returns (indexLookup kinds index) (fun w => w.wg.device = some d)
      (fun result w => result = none ∧ w.wg.device = some (writeOwnerWord d owner none)) :=
  TableClaims.original_index_lookup_null kinds index owner d table permitted word

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
  TableClaims.original_index_lookup_zero_reference kinds index owner d table permitted pid p word resident zero

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
  TableClaims.original_index_lookup_live kinds index owner d table permitted pid p word resident live bounded

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
    Campaign2.Returns (liftIndex (indexInsert owner))
      (fun w => w.wg.device = some d ∧ w.ambient.hidden = some (drawStream collisions fresh rest))
      (fun result w =>
        let table := { index := fresh.value, owner } :: removeOwner owner d.indexTable
        result = fresh.value ∧ w.wg.device = some { d with indexTable := table } ∧
          w.ambient.hidden = some rest ∧ UniqueIndices table ∧ UniqueOwners table) :=
  TableClaims.original_index_insert_recorded owner d indices owners collisions fresh rest allCollide isFresh

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
  TableClaims.original_index_insert_corpus_draws first second different d empty rest

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
  intro w ambient result final after pre run
  have effect := keypairCreate_exact peer d counter w ambient result final after pre run
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
  intro w ambient pre
  obtain ⟨ret, final, after, run, device⟩ := keypairPut_exact id now d k resident live word w ambient pre
  exact ⟨ret, final, after, run, device, released_table d id k now, released_keypair d id k now,
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
  intro w ambient pre
  obtain ⟨ret, final, after, run, device⟩ := keypairPut_exact id now d k resident live word w ambient pre
  exact ⟨ret, final, after, run, device, released_next d id k now,
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
    Campaign2.Observes (liftIndex (indexInsert owner))
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some (draws.map Draw.record))
      (fun _ out => out = .error (.hidden "no record left for index_draw")) := by
  intro w ambient pre
  rw [indexInsert_exhausted owner d draws allCollide w ambient pre.1 pre.2]
  rfl

/-- The original resident/live domain has an exact refusal or normal return.
On return, all original table, peer, drop-accounting and uniqueness effects
hold. Refusal exposes no post-state; reference safety elsewhere is not claimed. -/
theorem original_peer_release (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (indices : UniqueIndices d.indexTable) (owners : UniqueOwners d.indexTable) :
    Campaign2.Observes (peerPut (some pid)) (fun w => w.wg.device = some d)
      (fun _ out =>
        match peerReleaseRefusal pid p with
        | some stop => out = .error stop
        | none => ∃ w, out = .ok ((), w) ∧
        let final := releasedPeerDevice d pid p
        w.wg.device = some final ∧
        final.indexTable = (if p.refcount = 1 then removeOwner (.handshake pid) d.indexTable else d.indexTable) ∧
        final.peers[pid]? = (if p.refcount = 1 then none else some { p with refcount := p.refcount - 1 }) ∧
        (∀ other : PeerId, pid ≠ other → final.peers[other]? = d.peers[other]?) ∧
        final.txDropped = d.txDropped + (if p.refcount = 1 then p.staged.length else 0) ∧
        UniqueIndices final.indexTable ∧ UniqueOwners final.indexTable) :=
  ReleaseClaims.original_peer_release pid d p resident live indices owners

/-- Exact refusal or normal preservation of the original keypair store, cursor
and allocation bounds. No whole-driver initialization or preservation is claimed. -/
theorem original_peer_release_allocation_bounds (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (owners : KeypairOwnersBounded d) (store : KeypairStoreBounded d) :
    Campaign2.Observes (peerPut (some pid)) (fun w => w.wg.device = some d)
      (fun _ out =>
        match peerReleaseRefusal pid p with
        | some stop => out = .error stop
        | none => ∃ w, out = .ok ((), w) ∧
        let final := releasedPeerDevice d pid p
        w.wg.device = some final ∧ final.keypairs = d.keypairs ∧ final.nextKeypairId = d.nextKeypairId ∧
        KeypairOwnersBounded final ∧ KeypairStoreBounded final) :=
  ReleaseClaims.original_peer_release_allocation_bounds pid d p resident live owners store

/-- The original runner initializer establishes the optional-device table
invariant for every fixture-flag combination. Only its core projection is
installed here; the remaining observed context is arbitrary. This is an
initial-state theorem, not preservation through a runner trace. The legacy
fixture arguments remain universally quantified; the native WireGuard initializer
reads only net and bare. -/
theorem original_initial_kernel_tables (_rlimit : Nat)
    (net bare _foreign _stepped _seccompChild : Bool) (s : Campaign2.Snapshot) :
    View.TablesSafe (initialSnapshot net bare s) :=
  initialSnapshot_safe net bare s

/-- Original setup always installs its empty device table and establishes
numeric uniqueness, owner uniqueness and the hashed-keypair allocation bound.
No pre-existing device or invariant is required. -/
theorem original_setup_tables : Campaign2.Returns wgSetup (fun _ => True)
    (fun _ s => s.wg.device = some setupDevice ∧ View.TablesSafe s) := by
  intro w ambient pre
  obtain ⟨result, final, after, run, device⟩ := wgSetup_device w ambient pre
  refine ⟨result, final, after, run, device, ?_⟩
  intro d present
  change final.dev = some d at present
  rw [device] at present
  cases present
  exact setupDevice_safe

/-- Every normal completion of original destruction leaves no device, hence
the optional-device table invariant holds. This does not promise destruction
completes, preserve intermediate states, or establish whole-driver coverage. -/
theorem original_destruct_tables : Campaign2.Ensures wgDestruct (fun _ => True)
    (fun _ s => s.wg.device = none ∧ View.TablesSafe s) := by
  intro w ambient result final after pre run
  have absent := wgDestruct_absent w ambient result final after pre run
  exact ⟨absent, absent_tables_safe _ absent⟩

/-- Original newlink preserves the optional-device table invariant on every
normal return. Allocation refusals and missing records may still stop; this
does not assert newlink initializes an arbitrary existing table. -/
theorem original_newlink_tables : Campaign2.Ensures wgNewlink View.TablesSafe
    (fun _ s => View.TablesSafe s) :=
  wgNewlink_tables

/-- Original creation preserves the optional-device table invariant: an
existing device is retained, while an absent device is initialized by setup
and either retained after newlink or removed on its negative return. Only
normal completion is claimed, not success for arbitrary input records. -/
theorem original_create_tables : Campaign2.Ensures wgCreate View.TablesSafe
    (fun _ s => View.TablesSafe s) :=
  wgCreate_tables

/-- Every normal completion of original deletion leaves no device, including
the already-absent ENODEV return, hence establishes the table invariant. The
down/destruction prefix may stop; its intermediate states are not covered. -/
theorem original_delete_tables : Campaign2.Ensures wgDelete (fun _ => True)
    (fun _ s => s.wg.device = none ∧ View.TablesSafe s) := by
  intro w ambient result final after pre run
  have absent := wgDelete_absent w ambient result final after pre run
  exact ⟨absent, absent_tables_safe _ absent⟩

/-- Every normal return of original handshake-initiation sending preserves
numeric index uniqueness, embedded-owner uniqueness and the hashed-keypair
allocation bound. This includes early returns and socket-send failure; it
asserts neither successful transmission nor completion on arbitrary records. -/
theorem original_send_handshake_initiation_tables (pid : PeerId) :
    Campaign2.Ensures (sendHandshakeInitiation pid) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  sendHandshakeInitiation_tables pid

/-- Every normal return of the original handshake-send worker preserves the
optional-device table invariant, including a final peer-reference release that
removes its handshake row and peer. No resident-peer or retained-reference
premise is added. Environment dispatch and stopped prefixes are not covered. -/
theorem original_handshake_send_worker_tables (pid : PeerId) :
    Campaign2.Ensures (handshakeSendWorker pid) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  handshakeSendWorker_tables pid

/-- Every normal return of original environment send-worker dispatch preserves
optional-device table uniqueness and its hashed-keypair allocation bound.
The actual selection, dequeue, pending check and section reads execute around
the worker body. No resident-peer or reference-count premise is required;
completion on arbitrary records and stopped prefixes are not asserted. -/
theorem original_send_dispatch_tables :
    Campaign2.Product.Ensures Env.runOneSendWorker (fun s => View.TablesSafe s.toSnapshot)
      (fun _ s => View.TablesSafe s.toSnapshot) :=
  runOneSendWorker_tables

/-- Every normal return of original handshake-response sending preserves
optional-device index/owner uniqueness and the hashed-keypair allocation bound.
This composes response creation, session installation and the send/timer suffix,
including their normal early returns. It adds no residency or reference-count
premise and asserts neither successful transmission nor arbitrary-record completion. -/
theorem original_send_handshake_response_tables (pid : PeerId) :
    Campaign2.Ensures (sendHandshakeResponse pid) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  sendHandshakeResponse_tables pid

/-- Every normal return of original initiation consumption preserves optional-device
numeric-index uniqueness, owner uniqueness and the hashed-keypair allocation bound.
This includes rejected messages and failure-side peer release. It asserts neither
successful authentication nor completion on arbitrary records. -/
theorem original_consume_initiation_tables (msg : List UInt8) :
    Campaign2.Ensures (consumeInitiation msg) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  consumeInitiation_tables msg

/-- Every normal return of original response consumption preserves the table
invariant, including lookup's NULL/dead-peer storeback and failure-side release.
No owner/peer-word identity, residency or reference-count premise is added. -/
theorem original_consume_response_tables (msg : List UInt8) :
    Campaign2.Ensures (consumeResponse msg) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  consumeResponse_tables msg

/-- Every normal return of original cookie-message consumption preserves the
optional-device table invariant through lookup, cookie updates and peer release.
This is a table-safety contract, not successful authentication or a promise that
arbitrary records allow completion. -/
theorem original_cookie_message_consume_tables (msg : List UInt8) :
    Campaign2.Ensures (cookieMessageConsume msg) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  cookieMessageConsume_tables msg

/-- Every normal return of original staged-packet sending preserves optional-device
index and owner uniqueness and the hashed-keypair allocation bound. The original
nonce loop and skb allocation map feed the actual enqueue paths, including EPIPE
dead publication and other-failure releases. No resident-peer, owner-word identity
or reference-count premise is added. This caller queues work; worker execution,
packet delivery and completion on arbitrary records are not asserted. -/
theorem original_send_staged_packets_tables (pid : PeerId) :
    Campaign2.Ensures (sendStagedPackets pid) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  sendStagedPackets_tables pid

/-- Original keepalive sending preserves the optional-device table invariant
on every normal return, including allocation failure, existing staged packets,
and the full staged-send suffix. No residency or reference-count premise is added;
the contract does not assert transmission or arbitrary-record completion. -/
theorem original_send_keepalive_tables (pid : PeerId) :
    Campaign2.Ensures (sendKeepalive pid) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  sendKeepalive_tables pid

/-- Every normal return of original handshake-packet reception preserves
optional-device numeric-index uniqueness, owner uniqueness and the hashed-keypair
allocation bound. This includes cookie replies, rejected packets, session
installation, keepalive enqueue paths and final peer release. No readiness,
residency or reference-count premise is added. It does not assert authentication,
transmission or completion on arbitrary records. -/
theorem original_receive_handshake_packet_tables (msg : List UInt8) (src : SkbSource) :
    Campaign2.Ensures (receiveHandshakePacket msg src) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  receiveHandshakePacket_tables msg src

/-- One original receive-queue iteration preserves the optional-device table
invariant on normal return, including the empty queue and removal of the selected
head before its packet body. This covers the actual packet caller and subsequent
queue-count decrement; it does not assert whole-worker or scheduler closure. -/
theorem original_receive_step_tables :
    Campaign2.Ensures receiveStep View.TablesSafe (fun _ s => View.TablesSafe s) :=
  receiveStep_tables

/-- Original queued key-material clearing preserves the optional-device table
invariant on normal return through handshake unhash, all three ordered keypair
releases, and the final peer put. No static release budget, slot distinctness,
owner-word identity or resident-peer premise is added. Completion is not asserted. -/
theorem original_queued_clear_tables (pid : PeerId) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  queuedExpiredZeroKeyMaterial_tables pid

/-- Every normal return of the original clear-work dispatcher preserves numeric
index uniqueness, owner uniqueness and the hashed-keypair allocation bound.
This includes actual named/head selection, queue removal and both section reads;
it does not assert that arbitrary queue states or records permit completion. -/
theorem original_clear_dispatch_tables :
    Campaign2.Product.Ensures Env.runOneClearWorker (fun s => View.TablesSafe s.toSnapshot)
      (fun _ s => View.TablesSafe s.toSnapshot) :=
  runOneClearWorker_tables

/-- All five original timer callbacks preserve the optional-device table
invariant on normal return. Actual retry, keepalive, queueing and compensating
release paths remain covered. No timer readiness, residency or reference-count
premise is required; subsequent worker execution is outside this contract. -/
theorem original_timer_callback_tables (pid : PeerId) (timer : PeerTimer) :
    Campaign2.Ensures (timerCallback pid timer) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  timerCallback_tables pid timer

/-- The current wheel dispatch unit preserves table safety on every normal
return through its actual worker/unit/step checks, detachment and section-wrapped
callback, without callback or readiness assumptions. This explicitly replaces
the removed horizon-based dispatcher: due selection belongs to the surrounding
wheel-loop source factor; whole-loop preservation is not claimed here. -/
theorem original_fire_timer_tables (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (entry : WheelEntry) (step : Option UInt64) :
    Campaign2.Product.Ensures
      (TimerDiscipline.timerDispatchUnit_variant worker pid timer entry step)
      (fun s => View.TablesSafe s.toSnapshot)
      (fun _ s => View.TablesSafe s.toSnapshot) :=
  fireTimer_tables worker pid timer entry step

/-- Original handshake-work draining preserves optional-device numeric-index
uniqueness, owner uniqueness and the hashed-keypair allocation bound on normal
return. This covers named and placeholder dispatch and the optional clear-work
stopping target, without assuming empty queues, resident peers or a work budget.
It does not assert successful draining or exclude the original stopped outcomes. -/
theorem original_drain_handshake_send_wq_tables (upTo : Option PeerId) :
    Campaign2.Ensures (drainHandshakeSendWq upTo) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  drainHandshakeSendWq_tables upTo

/-- Original timer stopping preserves the optional-device table invariant on
normal return through all five deletions and the conditional clear-work flush.
No timer readiness, queue emptiness or peer-residency premise is added. -/
theorem original_timers_stop_tables (pid : PeerId) :
    Campaign2.Ensures (timersStop pid) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  timersStop_tables pid

/-- Original removal after the deadness guard preserves the table invariant
on normal return through ordered keypair releases, timer stopping, both flushes,
peer-count accounting and final peer release. The original guard remains in the
computation; no deadness or release-readiness premise is added. This does not
cover the outer allowed-IP removal or assert completion on arbitrary states. -/
theorem original_peer_remove_after_dead_tables (pid : PeerId) :
    Campaign2.Ensures (peerRemoveAfterDead pid) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  peerRemoveAfterDead_tables pid

/-- Original session installation preserves table safety on normal return.
If it actually returns true, the allocation remains resident with one reference
and the caller's peer word, occupies the role-selected current/next slot, and
owns the former handshake index uniquely in the final table. The caller is
initially resident with a self handshake peer word; its actual rotation releases
exclude the allocation ID. These are static local premises, not established
reachable-state invariants. Allocation may overwrite an existing unhashed key;
global store/slot lifetime safety and completion are not claimed. -/
theorem original_begin_session_coherence (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (safe : DeviceTablesSafe d)
    (self : p.handshakeEntryPeer = some pid)
    (fresh : SessionRotationFresh p d.nextKeypairId) :
    Campaign2.Ensures (beginSession pid) (fun s => s.wg.device = some d)
      (fun ok s => ∃ final, s.wg.device = some final ∧ DeviceTablesSafe final ∧
        (ok = true → SessionInstalled pid d p final)) :=
  beginSession_coherence pid d p resident safe self fresh

/-- Every normal original session return preserves the resident-key allocation
bound. Its cursor advances exactly once on true and stays unchanged on false;
the allocation identity was absent from the entry store. Initial caller
residency and store boundedness are static premises, not reachable-state claims.
No slot-freshness, self peer-word or readiness premise is required. Rotation
may erase the new key, so final residency and completion are not asserted. -/
theorem original_begin_session_allocation (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (bound : KeypairStoreBounded d) :
    Campaign2.Ensures (beginSession pid) (fun s => s.wg.device = some d)
      (fun ok s => ∃ final, s.wg.device = some final ∧ KeypairStoreBounded final ∧
        final.nextKeypairId = d.nextKeypairId + (if ok then 1 else 0) ∧
        d.keypairs[d.nextKeypairId]? = none) :=
  beginSession_allocation pid d p resident bound

/-- Consecutive original session calls for the listed peers, with no interleaved
handshake installation. Entry observations erase exactly to the original mapM,
including stopped outcomes. On normal return, results retain input order and
length; successful observed entry IDs form the consecutive allocation range and
are pairwise distinct. The store bound and allocation freshness hold at each
actual entry, and the final bound and cursor account for every true result.
Only an initial device and store bound are assumed. Final key residency,
lifetime ownership, reachability and successful completion are not claimed. -/
theorem original_session_allocation_sequence (pids : List PeerId) :
    Campaign2.Product.AgreesOn (fun _ => True) (liftWG (pids.mapM beginSession))
      (do let calls ← observedSessionCalls pids
          pure (calls.map SessionAllocationCall.result)) ∧
    (∀ d, KeypairStoreBounded d →
      Campaign2.Product.Ensures (observedSessionCalls pids) (fun s => s.wg.device = some d)
        (SessionAllocationSequenceFacts d pids)) := by
  constructor
  · intro entry pre
    rw [observedSessionCalls_erase]
  · intro d bound
    exact observedSessionCalls_facts pids d bound


/-- Any successful original index lookup derives its first equal-index row and
permitted kind, initial owner word and resident peer, positive reference count
and non-overflowing acquisition. Its exact final device includes the ordered
peer acquisition and owner-word store, including aliased identities. Only the
entry device is assumed; no table uniqueness, owner/peer coherence, isDead flag,
or readiness premise is supplied. This normal-return implication does not
promise completion or identify the owner object with its referenced peer. -/
theorem original_index_lookup_success (kinds : List IndexKind) (index : Nat) (d : Device) :
    Campaign2.Ensures (indexLookup kinds index) (fun s => s.wg.device = some d)
      (fun result final => ∀ owner pid, result = some (owner, pid) →
        d.indexTable.find? (·.index == index) = some { index, owner } ∧
        kinds.contains (IndexEntry.kind { index, owner }) = true ∧
        ownerWord d owner = some (some pid) ∧ ∃ p,
          d.peers[pid]? = some p ∧ 0 < p.refcount ∧ p.refcount + 1 < 2 ^ 31 ∧
          final.wg.device = some (writeOwnerWord (acquirePeer d pid p) owner (some pid))) :=
  indexLookup_success kinds index d

/-- Every normally returned empty original lookup has exactly one of three
causes: the first equal numeric index is absent or its kind is disallowed;
the permitted row's resident owner object stores NULL; or its stored peer is
resident with zero references. The first case leaves the device unchanged.
The latter two execute the exact owner-word clear, retaining even the NULL
case's same-value map store. A missing owner object or dangling stored peer is
not a normal empty result. Only the entry device is assumed; no coherence,
uniqueness, isDead or readiness premise is supplied. This is normal-return
classification, not completion, reachability or lifetime ownership. -/
theorem original_index_lookup_none (kinds : List IndexKind) (index : Nat) (d : Device) :
    Campaign2.Ensures (indexLookup kinds index) (fun s => s.wg.device = some d)
      (fun result final => result = none → ∃ d', final.wg.device = some d' ∧
        ∃ cause, LookupNoneCase kinds index d d' cause ∧
          ∀ other, LookupNoneCase kinds index d d' other → other = cause) :=
  indexLookup_none kinds index d


/-- Every normal return of the original responder confirmation preserves numeric
index and owner uniqueness and the hashed-keypair allocation bound, including
its immediate release of the displaced previous key. No resident-peer, distinct
slot, reference-budget or successful-confirmation premise is assumed. -/
theorem original_received_with_keypair_tables (pid : PeerId) (received : KeypairId) :
    Campaign2.Ensures (receivedWithKeypair pid received) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  receivedWithKeypair_tables pid received


/-- Normal lookup preserves residency and positive references for every hashed
owner and its referenced peer, with handshake owners pointing to themselves.
This assumes the local entry invariant; it does not establish reachability.
Upper reference bounds, table uniqueness and alias distinctness are not assumed. -/
theorem original_index_lookup_owner_coherence (kinds : List IndexKind) (index : Nat) :
    Campaign2.Ensures (indexLookup kinds index) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) :=
  indexLookup_owner_coherent_safe kinds index


/-- Original allocation preserves both table safety and local hashed-owner
coherence, without requiring the un-hashed new object's peer word to be valid.
This permits refusal and arbitrary aliases and does not prove publication,
store freshness, completion or lifetime safety. -/
theorem original_keypair_create_owner_coherence (peer : Option PeerId) :
    Campaign2.Ensures (keypairCreate peer)
      (fun s => View.TablesSafe s ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.TablesSafe s ∧ View.OwnerCoherentSafe s) :=
  keypairCreate_coherent_tables peer

/-- Actual guarded index removal is total for a present device. It preserves
hashed-owner coherence without requiring the removed owner to be resident. -/
theorem original_index_remove_owner_coherence (owner : IndexOwner) (d : Device)
    (coherent : HashedOwnersCoherent d) :
    Campaign2.Returns (liftIndex (indexRemove owner)) (fun s => s.wg.device = some d)
      (fun _ s =>
        s.wg.device = some {d with indexTable := removeOwner owner d.indexTable} ∧
        HashedOwnersCoherent {d with indexTable := removeOwner owner d.indexTable}) :=
  indexRemove_owner_coherence owner d coherent

/-- The current keypair-removal primitive is the keypair specialization of
indexRemove. It does not dereference the removed owner's stored peer word. -/
theorem original_keypair_index_remove_owner_coherence (id : KeypairId) (d : Device)
    (coherent : HashedOwnersCoherent d) :
    Campaign2.Returns (liftIndex (indexRemove (.keypair id)))
      (fun s => s.wg.device = some d)
      (fun _ s =>
        s.wg.device = some {d with indexTable := removeOwner (.keypair id) d.indexTable} ∧
        HashedOwnersCoherent {d with indexTable := removeOwner (.keypair id) d.indexTable}) :=
  keypairIndexRemove_owner_coherence id d coherent

/-- Every normal insertion retains coherence when the newly published owner
is coherent initially. The original collision loop and all stopped outcomes
remain; no record readiness, uniqueness or allocation-freshness premise is added. -/
theorem original_index_insert_owner_coherence (owner : IndexOwner) (d : Device)
    (coherent : HashedOwnersCoherent d) (published : OwnerCoherent d owner) :
    Campaign2.Ensures (liftIndex (indexInsert owner)) (fun s => s.wg.device = some d)
      (fun index s =>
        let table := {index, owner} :: removeOwner owner d.indexTable
        s.wg.device = some {d with indexTable := table} ∧
        HashedOwnersCoherent {d with indexTable := table}) :=
  indexInsert_owner_coherence owner d coherent published

/-- Actual replacement retains coherence and its exact Boolean/table effect.
The destination owner's coherence is supplied, not inferred from the replaced
handshake. Existing destination rows are allowed; owner uniqueness is not claimed. -/
theorem original_index_replace_owner_coherence (pid : PeerId) (kp : KeypairId) (d : Device)
    (coherent : HashedOwnersCoherent d) (published : OwnerCoherent d (.keypair kp)) :
    Campaign2.Returns (liftIndex (indexReplaceHandshake pid kp))
      (fun s => s.wg.device = some d)
      (fun hashed s =>
        let updated := if hashed then {d with indexTable := replaceOwner pid kp d.indexTable} else d
        hashed = d.indexTable.any (·.owner == .handshake pid) ∧
        s.wg.device = some updated ∧ HashedOwnersCoherent updated) :=
  indexReplace_owner_coherence pid kp d coherent published

/-- Every normal return of the original data receive path preserves numeric
index and owner uniqueness and the hashed-keypair allocation bound, including
failed acquisition, dead peers, queue-full returns and immediate cleanup.
No queue consistency, ownership coherence or readiness premise is assumed.
This covers consumeData, not its caller or the later decrypt/poll workers. -/
theorem original_consume_data_tables (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Campaign2.Ensures (consumeData msg src ds) View.TablesSafe (fun _ => View.TablesSafe) :=
  consumeData_tables msg src ds

/-- Local hashed-owner coherence alone does not survive final peer release:
a coherent hashed keypair may still name the released peer. This witness runs
the original peerPut normally for arbitrary Ambient and other WG fields;
it makes no assertion about reachable states or a driver defect. -/
theorem original_peer_put_owner_coherence_counterexample :
    ∃ d : Device, HashedOwnersCoherent d ∧
      Campaign2.Observes (peerPut (some 0)) (fun s => s.wg.device = some d)
        (fun _ out => ∃ final, out = .ok ((), final) ∧ ¬ View.OwnerCoherentSafe final) :=
  peerPut_ownerCoherentSafe_counterexample

/-- For the exact last-release device transform, entry coherence survives
exactly when every retained hashed owner does not name the released peer.
This characterizes the missing ownership obligation; it does not establish
the original operation's release readiness or reachable-state invariant. -/
theorem last_peer_release_owner_coherence_iff (d : Device) (pid : PeerId) (p : Peer)
    (last : p.refcount = 1) (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent (releasedPeerDevice d pid p) ↔
      ∀ e ∈ d.indexTable, e.owner ≠ .handshake pid →
        ownerWord d e.owner ≠ some (some pid) :=
  lastPeerRelease_coherent_iff d pid p last coherent

/-- Removing a peer's Allowed IPs preserves numeric and owner index uniqueness
and the hashed-keypair allocation bound on normal return. The only premise
is table safety; trie shape, residency and completion are not assumed. -/
theorem original_remove_by_peer_tables (pid : PeerId) :
    Campaign2.Ensures (removeByPeer pid) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  removeByPeer_tables pid

/-- Original outer peer removal preserves index table safety through its
NULL branch, dead-marking, actual worker flushes and final peer release.
This is normal-return preservation, with no owner-residency, trie-shape,
record-readiness or completion premise. -/
theorem original_peer_remove_tables (peer : Option PeerId) :
    Campaign2.Ensures (peerRemove peer) View.TablesSafe
      (fun _ s => View.TablesSafe s) :=
  peerRemove_tables peer

/-- Actual normal peer release preserves local hashed-owner coherence when
the entry peer is resident and positive and, on final release, no retained
hashed owner names it. That detachment remains an explicit caller obligation.
Queue/timer refusal paths are retained, without any readiness premise. -/
theorem original_peer_put_owner_coherence (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (detached : p.refcount = 1 → ∀ e ∈ d.indexTable,
      e.owner ≠ .handshake pid → ownerWord d e.owner ≠ some (some pid)) :
    Campaign2.Ensures (peerPut (some pid))
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) :=
  peerPut_owner_coherent pid d p resident live detached

/-- Every normal keypair release preserves local hashed-owner coherence.
The only entry premise is that invariant: NULL input, retained NULL peer words,
immediate unhashing and final erasure retain their actual source behavior.
No residency, upper reference bound, detachment or readiness is assumed. -/
theorem original_keypair_put_owner_coherence (key : Option KeypairId) (now : Bool) :
    Campaign2.Ensures (keypairPut key now) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) :=
  keypairPut_owner_coherent key now

/-- Every normal session start preserves coherence of all hashed owners
under explicit allocation-owner bounds and freshness of the rotation's releases.
The actual successful run supplies the original handshake publication witness;
self peer-word and positive-peer facts are derived, not assumed separately.
This local contract covers both Boolean outcomes and establishes no reachability. -/
theorem original_begin_session_owner_coherence (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (bounded : KeypairOwnersBounded d)
    (fresh : SessionRotationFresh p d.nextKeypairId) :
    Campaign2.Ensures (beginSession pid)
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) :=
  beginSession_owner_coherent pid d p resident bounded fresh

/-- Actual responder confirmation preserves local coherence for every hashed
owner on all normal returns. No successful-confirmation, residency, slot
distinctness, reference-budget or readiness premise is added. -/
theorem original_received_with_keypair_owner_coherence (pid : PeerId) (received : KeypairId) :
    Campaign2.Ensures (receivedWithKeypair pid received) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) :=
  receivedWithKeypair_owner_coherent pid received

/-- Original slot clearing preserves local hashed-owner coherence on normal
return, retaining aliases and actual refused puts. Coherence is the sole entry
invariant; this theorem does not promise completion of all releases. -/
theorem original_keypairs_clear_owner_coherence (pid : PeerId) :
    Campaign2.Ensures (keypairsClear pid) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) :=
  keypairsClear_owner_coherent pid

/-- Normal data ingress preserves every hashed owner's resident peer/key
relation. Actual lookup/acquisition supply the references used by cleanup;
there is no entry reference bound, readiness or alias-distinctness premise. -/
theorem original_consume_data_owner_coherence (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Campaign2.Ensures (consumeData msg src ds) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) :=
  consumeData_owner_coherent msg src ds

/-- Normal handshake clearing preserves local hashed-owner coherence; no
residency, reference-budget or completion premise is added. -/
theorem original_handshake_clear_owner_coherence (pid : PeerId) :
    Campaign2.Ensures (handshakeClear pid) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) :=
  handshakeClear_owner_coherent pid

/-- Normal expiry preserves local hashed-owner coherence with arbitrary clock
inputs and aliased slots. This does not assert that the operation returns. -/
theorem original_expire_current_peer_keypairs_owner_coherence (pid : PeerId) :
    Campaign2.Ensures (expireCurrentPeerKeypairs pid) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) :=
  expireCurrentPeerKeypairs_owner_coherent pid


/-- Original response consumption preserves local hashed-owner coherence on
all normal returns, including every rejection that releases its acquired peer. -/
theorem original_consume_response_owner_coherence (msg : List UInt8) :
    Campaign2.Ensures (consumeResponse msg) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) :=
  consumeResponse_owner_coherent msg

/-- The actual cookie-reply consumer preserves local hashed-owner coherence
on every normal return, including lookup misses and rejected replies. Its
lookup supplies the held reference released after any cookie-field update. -/
theorem original_cookie_message_consume_owner_coherence (msg : List UInt8) :
    Campaign2.Ensures (cookieMessageConsume msg) View.OwnerCoherentSafe
      (fun _ s => View.OwnerCoherentSafe s) :=
  cookieMessageConsume_owner_coherent msg

/-- Every normal initiation-consumption outcome retains local hashed-owner
coherence, including rejected messages after their acquired reference is put. -/
theorem original_consume_initiation_owner_coherence (msg : List UInt8) :
    Campaign2.Ensures (consumeInitiation msg) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) :=
  consumeInitiation_owner_coherent msg


/-- The publishing peer's live self-owner relation is explicit, even if its
handshake entry is initially unhashed. This is partial preservation. -/
theorem original_create_initiation_owner_coherence (pid : PeerId) :
    Campaign2.Ensures (createInitiation pid) (View.HandshakePublisherSafe pid)
      (fun _ => View.HandshakePublisherSafe pid) :=
  createInitiation_owner_coherent pid

/-- Response creation preserves the same explicit publisher invariant on
all normal returns, including a wrong-state early return. -/
theorem original_create_response_owner_coherence (pid : PeerId) :
    Campaign2.Ensures (createResponse pid) (View.HandshakePublisherSafe pid)
      (fun _ => View.HandshakePublisherSafe pid) :=
  createResponse_owner_coherent pid


/-- Actual peer initialization preserves hashed-owner coherence and supplies
its own live self-owner for later handshake publication; aliases are admitted. -/
theorem original_peer_create_owner_coherence (publicKey : Key) (psk : Option Key) :
    Campaign2.Ensures (peerCreate publicKey psk) View.OwnerCoherentSafe
      (fun result s => View.OwnerCoherentSafe s ∧
        ∀pid, result = .ok pid → ∃d p,
          s.wg.device = some d ∧ d.peers[pid]? = some p ∧
          p.refcount = 1 ∧ p.handshakeEntryPeer = some pid) :=
  peerCreate_owner_coherent publicKey psk

/-- A checked local-state counterexample to owner-coherence preservation by
the whole peer-removal call. The normal outcome holds for arbitrary Ambient;
this does not assert that the fixture is reachable from driver initialization. -/
theorem original_peer_remove_owner_coherence_counterexample :
    HashedOwnersCoherent RemovalOwnerWitness.device ∧
    Campaign2.Observes (peerRemove (some 0))
      (fun s => s.wg.device = some RemovalOwnerWitness.device)
      (fun _ out => ∃ final, out = .ok ((), final) ∧
        final.wg.device = some RemovalOwnerWitness.finalDevice ∧
        ¬ View.OwnerCoherentSafe final) :=
  peerRemove_ownerCoherentSafe_counterexample

/-- Actual whole removal, with empty key slots, allowed-IP list and handshake
work queues. A last reference requires entry detachment of surviving hashed
owners. Every normal return preserves coherence; original refusals stay possible. -/
theorem original_peer_remove_quiet_owner_coherence (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (count : 0 < d.numPeers)
    (empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none)
    (noList : p.allowedipsList = [])
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (detached : LastOwnerDetached d pid p) :
    Campaign2.Ensures (peerRemove (some pid))
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) :=
  peerRemove_quiet_owner_coherent pid d p resident live count empty noList send clear detached

/-- Local owner coherence survives whole peer removal with live or aliased slots
under entry coverage at a last peer reference. This is partial correctness and
asserts neither adequate references nor global reachability. -/
theorem original_peer_remove_slot_owner_coherence (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (count : 0 < d.numPeers) (noList : p.allowedipsList = [])
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (covered : LastOwnerCovered d pid p) :
    Campaign2.Ensures (peerRemove (some pid))
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) :=
  peerRemove_slot_owner_coherent pid d p resident live count noList send clear covered

/-- Whole peer removal admits arbitrary allowed-IP lists while retaining the
entry last-reference slot-coverage obligation and empty handshake work queues.
The claim is normal-return preservation, not a readiness or reachability claim. -/
theorem original_peer_remove_covered_owner_coherence (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (count : 0 < d.numPeers) (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (covered : LastOwnerCovered d pid p) :
    Campaign2.Ensures (peerRemove (some pid))
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) :=
  peerRemove_covered_owner_coherent pid d p resident live count send clear covered

/-- Normal completion of the original zero-key worker preserves owner coherence
under explicit entry slot coverage at a last reference. The work item's
scheduling, reference readiness and reachability are not asserted. -/
theorem original_queued_zero_owner_coherence (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (covered : LastOwnerCovered d pid p) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid)
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.OwnerCoherentSafe s) :=
  queuedExpiredZeroKeyMaterial_owner_coherent pid d p resident live covered

/-- Actual queued clear-work dispatch, with the lifecycle obligation confined
to the peer its recorded identity or queue head selects. -/
theorem original_clear_worker_owner_coherence :
    Campaign2.Product.Ensures Env.runOneClearWorker ClearWorkerOwnerEntry
      (fun _ s => View.OwnerCoherentSafe s.toSnapshot) :=
  runOneClearWorker_owner_coherent

/-- Original handshake queueing preserves hashed-owner coherence on every
normal return in both retry modes. Arbitrary unpublished owner words, aliases,
queue states and Ambient inputs remain allowed. Actual acquisition supplies
the reference used on a rejected enqueue; missing inputs, reference faults and
record failures retain their original Stops. This is not worker completion or
a global reference-ownership claim. -/
theorem original_send_queued_handshake_owner_coherence (pid : PeerId) (retry : Bool) :
    Campaign2.Ensures (sendQueuedHandshakeInitiation pid retry) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) :=
  sendQueuedHandshakeInitiation_owner_coherent pid retry

/-- Every normal original new-handshake timer callback preserves local hashed
owner coherence, including endpoint-source/cache clearing and the actual send-queue test. -/
theorem original_new_handshake_owner_coherence (pid : PeerId) :
    Campaign2.Ensures (expiredNewHandshake pid) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) :=
  expiredNewHandshake_owner_coherent pid

/-- Every normal original zero-key timer callback preserves local hashed owner
coherence while attempting to queue clear work. This does not execute the
worker or assert its later release obligation. -/
theorem original_zero_key_callback_owner_coherence (pid : PeerId) :
    Campaign2.Ensures (expiredZeroKeyMaterial pid) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) :=
  expiredZeroKeyMaterial_owner_coherent pid

/-- Both branches of the original retransmit timer callback preserve local
hashed-owner coherence on normal return. Actual clock, cache, queue and wheel
Stops remain; this does not assert callback completion or outer selection. -/
theorem original_retransmit_owner_coherence (pid : PeerId) :
    Campaign2.Ensures (expiredRetransmitHandshake pid) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) :=
  expiredRetransmitHandshake_owner_coherent pid

/-- Local-state finding for the original complete persistent callback. This is
not a reachable-driver or kernel-defect claim. -/
theorem original_persistent_keepalive_owner_coherence_counterexample :
    ∃ d : Device, HashedOwnersCoherent d ∧
      Campaign2.Observes (expiredSendPersistentKeepalive 0)
        (fun s => s.wg.device = some d ∧ s.ambient.hidden = some [PersistentOwnerWitness.clock])
        (fun _ out => ∃ final, out = .ok ((), final) ∧ ¬ View.OwnerCoherentSafe final) :=
  expiredPersistent_ownerCoherentSafe_counterexample

/-- Actual session success can publish a missing allocation from an arbitrary
slot-incoherent entry satisfying all three tested index invariants. The actual
following lookup Stops; neither initialized reachability nor a kernel bug is asserted. -/
theorem original_session_alias_owner_coherence_counterexample (counter : Nat) :
    DeviceTablesSafe SessionAliasWitness.device ∧ HashedOwnersCoherent SessionAliasWitness.device ∧ KeypairStoreBounded SessionAliasWitness.device ∧
    Campaign2.Observes (beginSession 0) (SessionAliasWitness.input counter)
      (fun _ out => ∃ s final, out = .ok (true,s) ∧ s.wg.device = some final ∧
        final.keypairs[1]? = none ∧ final.indexTable = [SessionAliasWitness.published] ∧
        DeviceTablesSafe final ∧ ¬ HashedOwnersCoherent final ∧
        s.wg.keypairCounter = counter + 1) ∧
    Campaign2.Observes (do let _ ← beginSession 0; indexLookup [.keypair] 7) (SessionAliasWitness.input counter)
      (fun _ out => out = .error (.invariant "dangling keypair 1")) :=
  session_alias_owner_coherence_counterexample counter

/-- Session creation followed only on true by the original old-index lookup:
every normal successful handoff returns the newly allocated owner and caller.
Explicit rotation freshness excludes the checked SessionAlias witness; it is
not inferred from table safety, owner coherence, or initialized reachability.
False preserves Device only. Every actual Stop remains in the computation. -/
theorem original_session_lookup_handoff (pid : PeerId) (index : Nat) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (safe : DeviceTablesSafe d)
    (coherent : HashedOwnersCoherent d)
    (handshake : {index, owner := IndexOwner.handshake pid} ∈ d.indexTable)
    (fresh : SessionRotationFresh p d.nextKeypairId) :
    Campaign2.Ensures (sessionThenLookup pid index) (fun s => s.wg.device = some d)
      (fun result s => ∃ final, s.wg.device = some final ∧ DeviceTablesSafe final ∧
        HashedOwnersCoherent final ∧
        (result.1 = false → result.2 = none ∧ final = d) ∧
        (result.1 = true → result.2 = some (.keypair d.nextKeypairId,pid))) :=
  session_lookup_handoff pid index d p resident safe coherent handshake fresh

/-- Original bulk peer removal preserves both index uniqueness properties and
the hashed-keypair allocation bound on normal return. The actual allowed-IP
free and both saved-peer loops execute; their Stops are retained. No trie
shape, resident-peer, queue-readiness or completion assumption is added. -/
theorem original_bulk_peer_removal_table_safety :
    Campaign2.Ensures peerRemoveAll View.TablesSafe (fun _ => View.TablesSafe) :=
  peerRemoveAll_tables

/-- The original session call preserves compatible bounded references, unique
numeric indices and owners, and resident positive hashed owners together.
Rotation freshness and the hashed-key allocation bound follow from the entry
invariant; caller residency follows from the actual first read. -/
theorem original_session_index_invariant (pid : PeerId) :
    Campaign2.Ensures (beginSession pid) View.SessionIndexSafe
      (fun _ => View.SessionIndexSafe) :=
  beginSession_sessionIndexSafe pid

/-- Any finite list of consecutive original session calls preserves the same
initial invariant on normal return, without new assumptions at each cut.
This is not an initialized-driver or completion theorem; all original Stops
remain in the computation. -/
theorem original_session_calls_index_invariant (pids : List PeerId) :
    Campaign2.Ensures (pids.mapM beginSession) View.SessionIndexSafe
      (fun _ => View.SessionIndexSafe) :=
  sessionCalls_sessionIndexSafe pids

/-- The initialized original runner supplies actual resident-store bounds and
slot compatibility on every normal endpoint, with exact JSON and indexed Stops.
Hashed-owner coherence is deliberately not part of this endpoint claim. -/
theorem original_initialized_store_slot_bounds (trace : Runner.Trace) (placeholders : Bool) :
    (InitializedBounds.inspection trace placeholders).map Prod.fst =
      Runner.executeTrace trace placeholders ∧
    (match InitializedBounds.inspection trace placeholders with
      | .error _ => True
      | .ok (_,final) => InitializedBounds.EndpointSafe final) :=
  ⟨InitializedBounds.inspection_json trace placeholders,
    InitializedBounds.inspection_bounds trace placeholders⟩

/-- A successful actual keypair lookup selects a resident key in its actual
owner's slots and acquires a positive peer reference. Entry coherence and
coverage remain explicit; this is not initialized-driver closure. -/
theorem original_index_lookup_keypair_slot_held (index : Nat) :
    Campaign2.Ensures (indexLookup [.keypair] index)
      (fun s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s)
      (fun result s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s ∧
        ∀ owner pid, result = some (owner,pid) → ∃ kid d p key,
          owner = .keypair kid ∧ s.wg.device = some d ∧
          d.peers[pid]? = some p ∧ 1 < p.refcount ∧
          d.keypairs[kid]? = some key ∧ key.peer = some pid ∧
          0 < key.refcount ∧ some kid ∈ clearKeys p) :=
  indexLookup_keypair_slot_held index

/-- Actual clearing preserves coverage and coherence with arbitrary slot
aliases, empties all three slots, and derives the conditional detachment
obligation for a last peer release. No queue or reference budget is supplied. -/
theorem original_keypairs_clear_hash_slots (pid : PeerId) :
    Campaign2.Ensures (keypairsClear pid)
      (fun s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s)
      (fun _ s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s ∧
        ∃ final p, s.wg.device = some final ∧ final.peers[pid]? = some p ∧
          clearKeys p = [none,none,none] ∧ LastOwnerDetached final pid p) :=
  keypairsClear_hashSlots_detached pid

/-- The actual role-selected rotation preserves hashed-key slot coverage.
The original execution supplies successful immediate puts; aliases and
missing-input Stops keep their source meaning. -/
theorem original_add_new_keypair_hash_slots (pid : PeerId) (newKey : KeypairId)
    (d : Device) (p : Peer) (key : Keypair)
    (resident : d.peers[pid]? = some p) (stored : d.keypairs[newKey]? = some key) :
    Campaign2.Ensures (addNewKeypair pid newKey)
      (fun s => s.wg.device = some d ∧ View.HashSlotsSafe s)
      (fun _ s => View.HashSlotsSafe s) :=
  addNewKeypair_hashSlots pid newKey d p key resident stored

/-- Both results of actual confirmation preserve hashed-key slot coverage.
Caller residency comes from the first read, with no readiness premise. -/
theorem original_confirmation_hash_slots (pid : PeerId) (received : KeypairId) :
    Campaign2.Ensures (receivedWithKeypair pid received) View.HashSlotsSafe
      (fun _ s => View.HashSlotsSafe s) :=
  receivedWithKeypair_hashSlots pid received

/-- Actual session start preserves the existing combined session invariant
and hashed-slot coverage together. The supplied entry invariant derives
allocation/rotation freshness; this does not assert driver reachability. -/
theorem original_begin_session_hash_slots (pid : PeerId) :
    Campaign2.Ensures (beginSession pid)
      (fun s => View.SessionIndexSafe s ∧ View.HashSlotsSafe s)
      (fun _ s => View.SessionIndexSafe s ∧ View.HashSlotsSafe s) := by
  intro g ambient result out after pre run
  exact ⟨beginSession_sessionIndexSafe pid g ambient result out after pre.1 run,
    beginSession_sessionHashSlots pid g ambient result out after pre run⟩

/-- Both modes of the original keypair put preserve coverage and positive
hashed-owner coherence together. No readiness, residency or refcount budget
is assumed; failures remain outside the normal-return postcondition. -/
theorem original_keypair_put_hash_slots (key : Option KeypairId) (now : Bool) :
    Campaign2.Ensures (keypairPut key now)
      (fun s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s)
      (fun _ s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s) := by
  intro g ambient result out after pre run
  exact ⟨keypairPut_owner_coherent key now g ambient result out after pre.1 run,
    keypairPut_hashSlots key now g ambient result out after pre.2 run⟩

/-- Original peer release preserves coverage and coherence when the last
reference has empty slots. Coverage derives detachment at that branch;
the original queue/timer refusals and supplied positive entry remain explicit. -/
theorem original_peer_put_hash_slots (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (empty : p.refcount = 1 → clearKeys p = [none,none,none]) :
    Campaign2.Ensures (peerPut (some pid))
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s)
      (fun _ s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s) := by
  intro g ambient result out after pre run
  have detached : LastOwnerDetached d pid p := by
    intro last
    exact emptyPeer_hashSlot_detached d pid p resident
      (pre.2.1 d pre.1) (pre.2.2 d pre.1) (empty last) last
  exact ⟨peerPut_owner_coherent pid d p resident live detached
      g ambient result out after ⟨pre.1,pre.2.1⟩ run,
    peerPut_hashSlots pid d p resident live empty
      g ambient result out after ⟨pre.1,pre.2.2⟩ run⟩

/-- Every original normal drain derives selection from its actual queue
before applying the supplied callback contract. This is composition over a
WireGuard projection, not a promise of completion or global coherence. -/
theorem original_queue_selected_handshake_drain (P : Campaign2.State → Prop)
    (send : ∀ pid, Campaign2.Ensures (runFlushedSendWork pid)
      (fun s => P s.wg ∧ ∃ d, s.wg.device = some d ∧ pid ∈ d.sendWorkQueue)
      (fun _ s => P s.wg))
    (clear : ∀ pid, Campaign2.Ensures (runFlushedClearWork pid)
      (fun s => P s.wg ∧ ∃ d, s.wg.device = some d ∧ pid ∈ d.clearWorkQueue)
      (fun _ s => P s.wg))
    (upTo : Option PeerId) :
    Campaign2.Ensures (drainHandshakeSendWq upTo) (fun s => P s.wg)
      (fun _ s => P s.wg) :=
  drainHandshakeSendWq_selected P send clear upTo

/-- At every actual initialized normal endpoint, each nondead resident peer
has its real base-list occurrence and a positive reference. Dead-peer
retirement and hashed-key coherence are separate obligations. -/
theorem original_initialized_live_peer_credit (trace : Runner.Trace) (placeholders : Bool) :
    match InitializedBounds.inspection trace placeholders with
    | .error _ => True
    | .ok (_,final) => InitializedFunding.LivePeerCredit final :=
  InitializedFunding.inspection_live trace placeholders

/-- The complete queued clear worker preserves coverage, owner coherence and
the supplied retirement reservations together. Actual execution provides
caller residency and payment positivity; no readiness budget is supplied. -/
theorem original_queued_clear_hash_slots
    (retired : Queues.RxCredits.Reservations) (pid : PeerId) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid)
      (fun s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s ∧ View.RetirementSafe retired s) := by
  intro g ambient result out after pre run
  have slots := queuedExpiredZeroKeyMaterial_hashSlots_coherent pid
    g ambient result out after ⟨pre.1,pre.2.1⟩ run
  exact ⟨slots.1,slots.2,queuedExpiredZeroKeyMaterial_retirement retired pid
    g ambient result out after pre.2.2 run⟩

/-- The actual flushed-clear wrapper includes dequeue and records around the
same complete worker. All three supplied invariants survive its normal return. -/
theorem original_flushed_clear_hash_slots
    (retired : Queues.RxCredits.Reservations) (pid : PeerId) :
    Campaign2.Ensures (runFlushedClearWork pid)
      (fun s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s ∧ View.RetirementSafe retired s) := by
  intro g ambient result out after pre run
  have slots := runFlushedClearWork_hashSlots_coherent pid
    g ambient result out after ⟨pre.1,pre.2.1⟩ run
  exact ⟨slots.1,slots.2,runFlushedClearWork_retirement retired pid
    g ambient result out after pre.2.2 run⟩

/-- A positive resident's actual release preserves all three invariants when
no hashed owner other than its own handshake still names it at its final reference. Unhashed residual slots
need not be empty; the detachment obligation remains explicit. -/
theorem original_peer_put_hash_slots_detached
    (retired : Queues.RxCredits.Reservations) (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (detached : LastOwnerDetached d pid p) :
    Campaign2.Ensures (peerPut (some pid))
      (fun s => s.wg.device = some d ∧ View.HashSlotsSafe s ∧
        View.OwnerCoherentSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s ∧ View.RetirementSafe retired s) := by
  intro g ambient result out after pre run
  exact ⟨peerPut_hashSlots_detached pid d p resident live detached
      g ambient result out after ⟨pre.1,pre.2.1⟩ run,
    peerPut_owner_coherent pid d p resident live detached
      g ambient result out after ⟨pre.1,pre.2.2.1⟩ run,
    peerPut_retirement retired pid d p resident live
      g ambient result out after ⟨pre.1,pre.2.2.2⟩ run⟩

/-- Actual initiation creation preserves nullable self compatibility of the
selected caller, hashed-slot coverage and retirement reservations. Additional
caller positivity is local, alongside the initial hashed-owner coherence.
Publication derives non-NULL from its successful dereference, and early
refusal keeps its original meaning. -/
theorem original_initiation_compatible_hash_slots
    (retired : Queues.RxCredits.Reservations) (pid : PeerId) :
    Campaign2.Ensures (createInitiation pid)
      (fun s => View.HandshakeCompatibleSafe pid s ∧
        View.HashSlotsSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HandshakeCompatibleSafe pid s ∧
        View.HashSlotsSafe s ∧ View.RetirementSafe retired s) := by
  intro w a result v b pre run
  exact ⟨createInitiation_owner_compatible pid w a result v b pre.1 run,
    createInitiation_hashSlots_retirement retired pid w a result v b pre.2 run⟩

/-- Actual response creation has the same nullable caller and index
preservation contract, including its role refusal and recorded failures.
This is a normal-return claim, with no successful-creation premise. -/
theorem original_response_compatible_hash_slots
    (retired : Queues.RxCredits.Reservations) (pid : PeerId) :
    Campaign2.Ensures (createResponse pid)
      (fun s => View.HandshakeCompatibleSafe pid s ∧
        View.HashSlotsSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HandshakeCompatibleSafe pid s ∧
        View.HashSlotsSafe s ∧ View.RetirementSafe retired s) := by
  intro w a result v b pre run
  exact ⟨createResponse_owner_compatible pid w a result v b pre.1 run,
    createResponse_hashSlots_retirement retired pid w a result v b pre.2 run⟩

/-- Actual key clearing discharges the paid owner's retirement obligation.
Coverage excludes a surviving hashed key owned by that now-empty slot;
coherence and every remaining retirement obligation survive the same call. -/
theorem original_keypairs_clear_retirement_discharge
    (paid : Queues.RxCredits.Owner) (retired : Queues.RxCredits.Reservations) :
    Campaign2.Ensures (keypairsClear paid.slot)
      (fun s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s ∧
        View.RetirementSafe (paid :: retired) s)
      (fun _ s => View.HashSlotsSafe s ∧ View.OwnerCoherentSafe s ∧
        View.RetirementSafe retired s) :=
  keypairsClear_retirement_discharge paid retired

/-- Slot compatibility and resident-store bounds are enough for the actual
session step's coverage and owner coherence. Full affiliation is unnecessary;
the smaller bounds remain explicit entry facts, not an initialized history
claim or a retirement-publication guarantee. -/
theorem original_begin_session_bounded_hash_slots (pid : PeerId) :
    Campaign2.Ensures (beginSession pid)
      (fun s => InitializedBounds.EndpointSafe s ∧
        View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s)
      (fun _ s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s) :=
  beginSession_endpoint_hashSlots pid

/-- The whole original initiation sender preserves hashed-slot coverage and
retirement reservations on every normal return, including rate-limited and
no-creation paths. No socket-success or callback contract is supplied. -/
theorem original_send_initiation_hash_slots_retirement
    (retired : Queues.RxCredits.Reservations) (pid : PeerId) :
    Campaign2.Ensures (sendHandshakeInitiation pid)
      (fun s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s) :=
  sendHandshakeInitiation_hashSlots_retirement retired pid

/-- The complete original initiation sender preserves positive hashed-owner
coherence and its nullable caller compatibility. Positivity for the selected
resident is an entry premise; neither residency nor non-NULL is required. -/
theorem original_send_initiation_owner_compatible (pid : PeerId) :
    Campaign2.Ensures (sendHandshakeInitiation pid) (View.HandshakeCompatibleSafe pid)
      (fun _ => View.HandshakeCompatibleSafe pid) :=
  sendHandshakeInitiation_owner_compatible pid

/-- The actual session retains coverage, positive owner coherence and dead-owner
reservations under the smaller slot/store bounds. Its successful live-caller
guard discharges the new key's retirement duty; it is not an entry premise. -/
theorem original_begin_session_retirement
    (retired : Queues.RxCredits.Reservations) (pid : PeerId) :
    Campaign2.Ensures (beginSession pid)
      (fun s => InitializedBounds.EndpointSafe s ∧ View.OwnerCoherentSafe s ∧
        View.HashSlotsSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s ∧
        View.RetirementSafe retired s) := by
  intro g ambient result out after pre run
  have index := beginSession_endpoint_hashSlots pid g ambient result out after
    ⟨pre.1,pre.2.1,pre.2.2.1⟩ run
  exact ⟨index.1,index.2,beginSession_endpoint_retirement retired pid
    g ambient result out after ⟨pre.1,pre.2.1,pre.2.2.2⟩ run⟩

/-- Original peer creation retains coverage, positive owner coherence and
retirement on every normal errno or successful return. Configured entry bounds
derive vacancy at the actual allocation cursor; no fresh-target premise is supplied. -/
theorem original_peer_create_hash_slots_retirement
    (publicKey : Key) (psk : Option Key) (retired : Queues.RxCredits.Reservations) :
    Campaign2.Ensures (peerCreate publicKey psk)
      (fun s => View.ConfiguredSafe s ∧ View.OwnerCoherentSafe s ∧
        View.HashSlotsSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s ∧
        View.RetirementSafe retired s) := by
  intro g ambient result out after pre run
  have retained := peerCreate_hashSlots_retirement publicKey psk retired
    g ambient result out after ⟨pre.1,pre.2.2.1,pre.2.2.2⟩ run
  exact ⟨(peerCreate_owner_coherent publicKey psk
    g ambient result out after pre.2.1 run).1,retained⟩

/-- The complete original session retains the combined table, slot-coverage,
owner-coherence and empty-retirement package. Its slot/store bounds are entry
facts; this local claim does not assert that a driver history establishes them. -/
theorem original_begin_session_index_core (pid : PeerId) :
    Campaign2.Ensures (beginSession pid)
      (fun s => InitializedBounds.EndpointSafe s ∧ View.IndexCore s)
      (fun _ s => View.IndexCore s) :=
  Reached.session_core pid

/-- Original initiation consumption retains the full local index package on
every normal return. Failed authentication releases its actual acquired loan;
no successful lookup, record readiness or extra reference budget is assumed. -/
theorem original_consume_initiation_index_core (msg : List UInt8) :
    Campaign2.Ensures (consumeInitiation msg) View.IndexCore
      (fun _ => View.IndexCore) :=
  consumeInitiation_indexCore msg

/-- Original response consumption retains the same combined index facts,
including normal owner-word-clear lookup failures and rejection cleanup. -/
theorem original_consume_response_index_core (msg : List UInt8) :
    Campaign2.Ensures (consumeResponse msg) View.IndexCore
      (fun _ => View.IndexCore) :=
  consumeResponse_indexCore msg

/-- Original expiry retains table, slot and owner coherence and empty
retirement, allowing absent or aliased optional key slots and original Stops. -/
theorem original_expiry_index_core (pid : PeerId) :
    Campaign2.Ensures (expireCurrentPeerKeypairs pid) View.IndexCore
      (fun _ => View.IndexCore) :=
  expireCurrentPeerKeypairs_indexCore pid

/-- Original staged sending preserves the complete index component under the
current slot compatibility invariant. No successful allocation, queue readiness
or extra caller-reference premise is supplied. -/
theorem original_send_staged_index_core (pid : PeerId) :
    Campaign2.Ensures (sendStagedPackets pid) View.StagedIndexReady
      (fun _ => View.IndexCore) :=
  StagingRich.sendStaged_index pid

/-- Original keepalive sending has the same index guarantee, including its
normal allocation-refusal path and the actual staged-send continuation. -/
theorem original_send_keepalive_index_core (pid : PeerId) :
    Campaign2.Ensures (sendKeepalive pid) View.StagedIndexReady
      (fun _ => View.IndexCore) :=
  StagingRich.sendKeepalive_index pid

/-- The complete original response sender preserves the index component from
current slot/store bounds and nullable caller compatibility. Its reached source
adapter obtains that compatibility from the actual charged stamped loan. -/
theorem original_send_response_index_core (pid : PeerId) :
    Campaign2.Ensures (sendHandshakeResponse pid)
      (fun s => InitializedBounds.EndpointSafe s ∧ View.IndexCore s ∧
        View.HandshakeCompatibleSafe pid s)
      (fun _ => View.IndexCore) :=
  sendHandshakeResponse_indexCore pid

/-- Original public-key lookup retains the index component, and every returned
peer has the actual extra reference required for immediate rejection cleanup.
No successful acquisition or later preservation of that budget is assumed. -/
theorem original_pubkey_lookup_index_core (key : Key) :
    Campaign2.Ensures (pubkeyLookup key) View.IndexCore
      (fun result s => View.IndexCore s ∧
        ∀ pid, result = some pid → View.IndexCoreHeld pid s) :=
  pubkeyLookup_indexCore_held key

end Leanux.Proofs.WG.Index
