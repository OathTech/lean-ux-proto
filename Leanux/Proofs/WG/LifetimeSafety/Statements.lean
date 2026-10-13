import Leanux.Proofs.WG.Keypairs.Identity
import Leanux.Proofs.WG.ReplayWindow.Statements
import Leanux.Proofs.Logged.Checkpoints
import Leanux.Proofs.WG.LifetimeSafety.CursorWitness
import Leanux.Proofs.WG.Packets.Primitives
import Leanux.Proofs.WG.Peers.Allocation
import Leanux.Proofs.WG.Peers.Access
import Leanux.Proofs.WG.Peers.CreationAccess

/-! R2's store-identity components: whole-operation keypair evolution,
peer allocation/reference sequences, and packet primitive sequences within a device
epoch. Full caller and lifecycle coverage remain separate obligations. -/
namespace Leanux.Proofs.WG.LifetimeSafety
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.ReplayWindow

/-- Erasing all observations of peerCreate, including its cache, handshake and
clock initialization helpers, returns the exact original result or Stop for
every World and initial history. -/
theorem peer_create_access_erasure (key : Key) (psk : Option Key) :
    ErasesPrefix (Peers.peerCreatePrefix key psk) (peerCreate key psk) :=
  Peers.peerCreatePrefix_erases key psk

/-- The original creation core increments the identity counter and performs
the first insertion before any initializer runs. A present device emits exactly
allocation then write; the original no-device setter is a no-op. This all-input
statement does not assume an empty destination or log overwritten objects as
released. -/
theorem peer_creation_core_observation (pid : PeerId) (key : Key)
    (w : World) (h : List Peers.PeerEvent) :
    runPrefix (Peers.peerCreateCorePrefix pid key) w h =
      (.ok ((), Peers.creationCoreWorld w pid key),
        if w.k.wg.isSome then
          h ++ [.allocate pid (w.k.peerCounter + 1), .write pid (w.k.peerCounter + 1)]
        else h) := by
  rw [Peers.peerCreateCorePrefix_run, Peers.peerCreateCore_run]

/-- At the creation core followed by the first initializer, a failed recorded
cache-clock read retains the prior allocation and write observations. The
failure exposes no final World; this is the source's initialization cut, not a
whole-runner claim. -/
theorem peer_creation_record_failure_prefix (pid : PeerId) (key : Key)
    (w : World) (h : List Peers.PeerEvent) (e : Stop)
    (hd : w.k.wg.isSome = true) (ha : w.armRecords = true)
    (hc : w.dstCacheRecords = true)
    (hr : (hiddenU64 .dstCacheResetTs).run (Peers.creationCoreWorld w pid key) = .error e) :
    runPrefix (do Peers.peerCreateCorePrefix pid key; Peers.dstCacheResetPrefix pid) w h =
      (.error e, h ++ [.allocate pid (w.k.peerCounter + 1), .write pid (w.k.peerCounter + 1)]) :=
  Peers.creation_core_clock_failure pid key w h e hd ha hc hr

/-- Finite sequences of complete peerCreate, peerPut and wgGetDeviceDone calls
preserve the original execution and first Stop after observation erasure. The
family discards ordinary return values, including create's ordinary error code,
and retains the full World on success. -/
theorem peer_creation_call_sequence_erasure (calls : List Peers.CreationCall) :
    ErasesPrefix (Peers.CreationCall.observe calls) (Peers.CreationCall.execute calls) :=
  Peers.CreationCall.observe_erases calls

/-- In this finite creation/reference caller family, no read, write or new
allocation follows a release of the same identity, including prefixes ending in
failure. Initial resident identities are unique and frontier-bounded, and every
previously released identity is absent and frontier-bounded. This covers the
listed callers' internal accesses, not cursor provenance, other callers or
complete release reporting when malformed allocation slots overwrite peers. -/
theorem peer_creation_call_sequence_prefix_safe (calls : List Peers.CreationCall)
    (w : World) (h : List Peers.PeerEvent) (n : Nat) (hi : Peers.CreationInv h w) :
    Lifetimes.AccessEvent.Safe ((runPrefix (Peers.CreationCall.observe calls) w h).2.take n) :=
  (Peers.CreationCall.observe_preserves calls w h hi).choose_spec.2.1.take n

/-- The complete original peerPut is observed at both successful getter sites,
the actual setter and the inline release. For every World, erasing observations
returns the exact original result or Stop, while errors retain the exact prefix. -/
theorem peer_put_access_exact (peer : Option PeerId) (w : World) (h : List Peers.PeerEvent) :
    runPrefix (Peers.peerPutPrefix peer) w h =
      ((peerPut peer).run w, h ++ Peers.peerPutEvents peer w) :=
  Peers.peerPutPrefix_run peer w h

/-- The actual dump-completion callback has the same complete peer-access
observations as its peerPut call, including every failure prefix. This statement
neither asserts cursor provenance nor covers the separate dump-body caller. -/
theorem dump_done_access_exact (ctx : DumpCtx) (w : World) (h : List Peers.PeerEvent) :
    runPrefix (Peers.wgGetDeviceDonePrefix ctx) w h =
      ((wgGetDeviceDone ctx).run w, h ++ Peers.peerPutEvents ctx.nextPeer w) :=
  Peers.wgGetDeviceDonePrefix_run ctx w h

/-- Observation of a finite sequence drawn from peerPut and wgGetDeviceDone
preserves the complete original execution result, including its first error.
The family contains no allocation, device lifecycle or other WG caller. -/
theorem peer_release_call_sequence_erasure (calls : List Peers.AccessCall) :
    ErasesPrefix (Peers.AccessCall.observe calls) (Peers.AccessCall.execute calls) :=
  Peers.AccessCall.observe_erases calls

/-- For this finite no-allocation caller family, no observed access follows a
release of the same identity, even in a prefix ending in an error. The initial
invariant requires unique resident identities and absence of previously released
ones; it does not assume the desired property of future execution. -/
theorem peer_release_call_sequence_prefix_safe (calls : List Peers.AccessCall)
    (w : World) (h : List Peers.PeerEvent) (n : Nat) (hi : Peers.AccessInv h w) :
    Lifetimes.AccessEvent.Safe ((runPrefix (Peers.AccessCall.observe calls) w h).2.take n) :=
  (Peers.AccessCall.observe_preserves calls w h hi).choose_spec.2.1.take n

/-- The complete original peerCreate call has an exact identity-store effect:
an ordinary error result leaves it unchanged, while success increments the
frontier and inserts that fresh stamp at the returned slot. No assumption that
the old nextPeer slot was empty is made by this refinement. -/
theorem peer_create_exact (publicKey : Key) (psk : Option Key)
    (w w' : World) (result : Except Int PeerId)
    (hr : (peerCreate publicKey psk).run w = .ok (result, w')) :
    Peers.snapshot w' = match result with
      | .error _ => Peers.snapshot w
      | .ok pid => (Peers.snapshot w).allocate pid := by
  cases result <;> exact Peers.peerCreate_exact publicKey psk w w' _ hr

/-- A successful original peerCreate returns a slot containing the next global
peer allocation identity, strictly beyond the call's initial frontier. -/
theorem peer_create_fresh_identity (publicKey : Key) (psk : Option Key)
    (w w' : World) (pid : PeerId)
    (hr : (peerCreate publicKey psk).run w = .ok (.ok pid, w')) :
    (Peers.snapshot w').frontier = (Peers.snapshot w).frontier + 1 ∧
      (Peers.snapshot w').slots pid = some ((Peers.snapshot w).frontier + 1) :=
  Peers.peerCreate_fresh publicKey psk w w' pid hr

/-- Across a finite sequence of actual peer lookup, reference acquisition
(including get-unless-zero), release and atomic creation calls, every identity remains
within the allocation frontier. This is a primitive-call sequence contract,
not yet whole-syscall or internal-access coverage. -/
theorem peer_allocation_sequence_bounded (w w' : World)
    (h : Peers.AllocationSequence w w')
    (hb : Lifetimes.Bounded (Peers.snapshot w)) :
    Lifetimes.Bounded (Peers.snapshot w') :=
  (Peers.allocation_sequence_contract h hb).1

/-- An already allocated peer identity absent before such a finite sequence
cannot return through any mixture of those lookup, reference and creation calls.
The frontier bound excludes identities first allocated during the sequence. -/
theorem peer_allocation_sequence_no_resurrection (w w' : World)
    (h : Peers.AllocationSequence w w')
    (hb : Lifetimes.Bounded (Peers.snapshot w)) (stamp : Nat)
    (hs : stamp ≤ (Peers.snapshot w).frontier)
    (ha : Lifetimes.Absent (Peers.snapshot w) stamp) :
    Lifetimes.Absent (Peers.snapshot w') stamp :=
  (Peers.allocation_sequence_contract h hb).2.absent hs ha

/-- The original conditional reference-acquisition helper, including its null
and zero-count branches, preserves the complete peer identity projection. -/
theorem peer_get_unless_zero_preserves_identities (peer : Option PeerId)
    (w w' : World) (result : Option PeerId)
    (hr : (peerGetMaybeZero peer).run w = .ok (result, w')) :
    Peers.snapshot w' = Peers.snapshot w :=
  Peers.peerGetMaybeZero_samePeerSnapshot peer w result w' hr

/-- Every successful actual peer getter resolves the identity resident in its
slot now. It does not certify that a caller's raw slot reference owns a ref. -/
theorem peer_lookup_current (i : PeerId) (w w' : World) (p : Peer)
    (hr : (getPeer i).run w = .ok (p, w')) :
    w' = w ∧ (Peers.snapshot w).slots i = some p.internalId :=
  Peers.getPeer_current i w w' p hr

/-- The actual unconditional peer setter preserves store identities when its
replacement has the same identity as the current resident of that slot. -/
theorem peer_set_current_identity (i : PeerId) (p : Peer) (w w' : World)
    (hl : (Peers.snapshot w).slots i = some p.internalId)
    (hr : (setPeer i p).run w = .ok ((), w')) : Peers.snapshot w' = Peers.snapshot w :=
  Peers.setPeer_same i p w w' hl hr

/-- Finite successful sequences of the original getPeer, peerGet and peerPut
retain or remove store identities and leave the allocation frontier unchanged.
This is a helper-family statement, without a whole-run coverage premise. -/
theorem peer_reference_sequence_retains_identities (w w' : World)
    (h : Peers.Sequence w w') : Lifetimes.Retained (Peers.snapshot w) (Peers.snapshot w') :=
  Peers.sequence_retained h

/-- An identity absent before a finite original peer-reference helper sequence
cannot reappear afterward; these helpers perform no peer allocation. -/
theorem peer_reference_sequence_no_resurrection (w w' : World) (stamp : Nat)
    (h : Peers.Sequence w w') (ha : Lifetimes.Absent (Peers.snapshot w) stamp) :
    Lifetimes.Absent (Peers.snapshot w') stamp :=
  fun i hi => ha i ((Peers.sequence_retained h).2 i stamp hi)

/-- Any finite sequence of successful original packet-store primitives keeps
the device epoch, the allocation bound and every surviving old slot identity.
The named family is exactly the eight TX/RX helpers, not the whole runner. -/
theorem packet_primitive_sequence_lifetimes (w w' : World)
    (h : Packets.Sequence w w') (hi : Packets.Inv w) :
    Packets.Inv w' ∧ Packets.epoch w' = Packets.epoch w ∧
      Lifetimes.Transition (Packets.snapshot w) (Packets.snapshot w') :=
  Packets.sequence_contract h hi

/-- A previously allocated packet identity absent before a finite successful
sequence of original store primitives remains absent afterward. Device resets
and internal accesses in composite callers are outside this helper family. -/
theorem packet_primitive_sequence_no_resurrection (w w' : World) (stamp : Nat)
    (h : Packets.Sequence w w') (hi : Packets.Inv w)
    (hb : stamp ≤ (Packets.snapshot w).frontier)
    (ha : Lifetimes.Absent (Packets.snapshot w) stamp) :
    Lifetimes.Absent (Packets.snapshot w') stamp :=
  (Packets.sequence_contract h hi).2.2.absent hb ha

/-- Filling an empty packet slot through these original primitive executions
requires an allocation identity newer than their initial allocation frontier. -/
theorem packet_primitive_sequence_empty_slot_fresh (w w' : World)
    (slot : Packets.Slot) (stamp : Nat) (h : Packets.Sequence w w')
    (hi : Packets.Inv w) (he : (Packets.snapshot w).slots slot = none)
    (hl : (Packets.snapshot w').slots slot = some stamp) :
    (Packets.snapshot w).frontier < stamp :=
  (Packets.sequence_contract h hi).2.2.empty_fresh he hl

/-- Bounded packet stores make the shared next allocation slot empty in both
directions, so either original allocation helper allocates a fresh slot. -/
theorem packet_next_allocation_slots_empty (w : World) (d : Device)
    (hd : w.k.wg = some d) (hi : Packets.Inv w) :
    d.txSkbs[d.nextSkb]? = none ∧ d.rxSkbs[d.nextSkb]? = none :=
  Packets.allocation_slots_empty w d hd hi

/-- A successful original TX getter returns the current resident packet and
leaves the entire World unchanged. -/
theorem packet_tx_lookup_current (i : SkbId) (w w' : World) (p : DataPacket)
    (hr : (getTxSkb i).run w = .ok (p, w')) :
    w' = w ∧ ∃ d, w.k.wg = some d ∧ d.txSkbs[i]? = some p :=
  Packets.getTxSkb_current i w w' p hr

/-- A successful original RX getter returns the current resident packet and
leaves the entire World unchanged. -/
theorem packet_rx_lookup_current (i : SkbId) (w w' : World) (p : RxPacket)
    (hr : (getRxSkb i).run w = .ok (p, w')) :
    w' = w ∧ ∃ d, w.k.wg = some d ∧ d.rxSkbs[i]? = some p :=
  Packets.getRxSkb_current i w w' p hr

/-- A retained cursor slot 26 makes the actual dump-done callback release the
live replacement peer, allocation identity 55 with one reference, while its
configured peer list and public-key hash still retain slot 26. This is a
retargeted reference to a new identity; the original identity does not return.
The explicit-record runner replay separately establishes the replacement path. -/
theorem stale_cursor_retargets_replacement :
    CursorWitness.before = some (55, 1, false) ∧
    CursorWitness.afterDone = some (none, [26], [26]) := by
  decide

/-- After an actual TX free, no successful sequence of the eight original
packet primitives can make a later original getter at that slot succeed.
This statement covers one device epoch, without assuming TX/RX disjointness. -/
theorem packet_tx_free_prevents_later_lookup (i : SkbId) (w v u out : World)
    (p : DataPacket) (hi : Packets.Inv w)
    (hf : (freeTxSkb i).run w = .ok ((), v)) (hs : Packets.Sequence v u) :
    (getTxSkb i).run u ≠ .ok (p, out) :=
  Packets.freedTx_unreadable i w v u out p hi hf hs

/-- After an actual RX free, no successful sequence of the eight original
packet primitives can make a later original getter at that slot succeed.
This statement covers one device epoch, without assuming TX/RX disjointness. -/
theorem packet_rx_free_prevents_later_lookup (i : SkbId) (w v u out : World)
    (p : RxPacket) (hi : Packets.Inv w)
    (hf : (freeRxSkb i).run w = .ok ((), v)) (hs : Packets.Sequence v u) :
    (getRxSkb i).run u ≠ .ok (p, out) :=
  Packets.freedRx_unreadable i w v u out p hi hf hs

/-- The checkpoint observer used by concrete lifetime witnesses returns the
original runner's full JSON or exact indexed error after its observation list
is erased, for every trace, projection and initial observation list. -/
theorem checkpoint_runner_erasure (project : Nat → World → α)
    (trace : Leanux.Runner.Trace) (placeholders : Bool) (observed : List α) :
    Prod.fst <$> (executeTraceCheckpoints project trace placeholders).run observed =
      Leanux.Runner.executeTrace trace placeholders :=
  executeTraceCheckpoints_erases project trace placeholders observed

/-- Each checkpoint emission appends exactly one projection of the supplied
committed World and operation index. The observer has one such source site,
after the syscall, ambient consumption and all per-operation guards. -/
theorem checkpoint_observation_exact (project : Nat → World → α)
    (index : Nat) (w : World) (observed : List α) :
    (emitCheckpoint project index w).run observed =
      .ok ((), observed ++ [project index w]) :=
  emitCheckpoint_run project index w observed

/-- Across arbitrary finite lifetime evolution, an allocated keypair identity
that is absent from the store never returns, even when numeric slots are reused.
The frontier premise excludes identities first allocated in the future. -/
theorem keypair_no_resurrection (s t : Snapshot) (h g : History)
    (stamp : Nat) (he : Evolution s h t g)
    (hb : stamp ≤ s.frontier) (ha : LifetimeAbsent s stamp) :
    LifetimeAbsent t stamp :=
  he.absent_preserved stamp hb ha

/-- An identity present before one evolution, absent afterward, and therefore
released cannot reappear during any following evolution. The original
reachable-state invariant supplies its allocation-frontier bound. -/
theorem keypair_released_stays_absent (s t u : Snapshot) (h g k : History)
    (i : Nat) (old : Cell) (first : Evolution s h t g)
    (later : Evolution t g u k) (hi : Inv s h)
    (hc : s.slots i = some old) (ha : LifetimeAbsent t old.stamp) :
    LifetimeAbsent u old.stamp :=
  first.released_absent later hi hc ha

/-- Reusing an initially empty keypair slot creates an identity strictly newer
than the initial allocation frontier, through any finite lifetime evolution. -/
theorem keypair_reused_slot_is_fresh (s t : Snapshot) (h g : History)
    (i : Nat) (now : Cell) (he : Evolution s h t g)
    (hi : s.slots i = none) (hc : t.slots i = some now) :
    s.frontier < now.stamp :=
  he.empty_slot_fresh hi hc

/-- Every successful actual keypair lookup returns the object currently stored
at its slot, with its current allocation identity, and leaves the World intact. -/
theorem keypair_lookup_current (i : KeypairId) (w w' : World) (k : Keypair)
    (hr : (getKeypair i).run w = .ok (k, w')) :
    w' = w ∧ (snapshot w).slots i = some (cell k) :=
  getKeypair_current i w w' k hr

/-- A successful original syscall, including its scheduled receive work, never
reintroduces a previously allocated keypair identity absent at the start. -/
theorem keypair_syscall_no_resurrection (call : Syscall) (w w' : World)
    (ret : Int) (history : History) (stamp : Nat)
    (hi : Inv (snapshot w) history) (hb : stamp ≤ (snapshot w).frontier)
    (ha : LifetimeAbsent (snapshot w) stamp)
    (hr : (Leanux.syscall call).run w = .ok (ret, w')) :
    LifetimeAbsent (snapshot w') stamp := by
  obtain ⟨_, _, he⟩ := S3_syscall call w w' ret history hi hr
  exact he.absent_preserved stamp hb ha

/-- The same absence property holds for the original whole operation used by
the runner, including its post-syscall ambient-record consumption. -/
theorem keypair_ambient_no_resurrection (call : Syscall) (w w' : World)
    (ret : Int) (history : History) (stamp : Nat)
    (hi : Inv (snapshot w) history) (hb : stamp ≤ (snapshot w).frontier)
    (ha : LifetimeAbsent (snapshot w) stamp)
    (hr : (syscallWithAmbient call).run w = .ok (ret, w')) :
    LifetimeAbsent (snapshot w') stamp := by
  obtain ⟨_, _, he⟩ := S3_syscall_ambient call w w' ret history hi hr
  exact he.absent_preserved stamp hb ha

/-- A lookup after a successful original runner operation cannot return an
already released identity, including after any reuse of the queried slot. -/
theorem keypair_lookup_after_release (call : Syscall) (w mid out : World)
    (ret : Int) (history : History) (stamp i : Nat) (k : Keypair)
    (hi : Inv (snapshot w) history) (hb : stamp ≤ (snapshot w).frontier)
    (ha : LifetimeAbsent (snapshot w) stamp)
    (hr : (syscallWithAmbient call).run w = .ok (ret, mid))
    (hq : (getKeypair i).run mid = .ok (k, out)) : k.internalId ≠ stamp :=
  getKeypair_absent_identity i mid out k stamp
    (keypair_ambient_no_resurrection call w mid ret history stamp hi hb ha hr) hq

/-- If an original runner operation fills an empty keypair slot, a later
successful getter at that slot returns an identity newer than the operation's
starting allocation frontier. This states slot reuse directly over the mirror. -/
theorem keypair_ambient_reused_slot_fresh (call : Syscall) (w mid out : World)
    (ret : Int) (history : History) (i : Nat) (k : Keypair)
    (hi : Inv (snapshot w) history) (he : (snapshot w).slots i = none)
    (hr : (syscallWithAmbient call).run w = .ok (ret, mid))
    (hq : (getKeypair i).run mid = .ok (k, out)) :
    (snapshot w).frontier < k.internalId := by
  obtain ⟨_, _, hev⟩ := S3_syscall_ambient call w mid ret history hi hr
  exact hev.empty_slot_fresh he (getKeypair_current i mid out k hq).2

end Leanux.Proofs.WG.LifetimeSafety
