import Leanux.Proofs.WG.Lifetimes.TxStagingCalls
import Leanux.Proofs.WG.Keypairs.Identity
import Leanux.Proofs.WG.ReplayWindow.Statements
import Leanux.Proofs.Logged.Checkpoints
import Leanux.Proofs.WG.LifetimeSafety.CursorWitness
import Leanux.Proofs.WG.Packets.Primitives
import Leanux.Proofs.WG.Peers.Allocation
import Leanux.Proofs.WG.Peers.Access
import Leanux.Proofs.WG.Peers.CreationAccess
import Leanux.Proofs.WG.Lifetimes.Enqueue
import Leanux.Proofs.WG.Lifetimes.DecryptWorker
import Leanux.Proofs.WG.Lifetimes.ReleaseCalls
import Leanux.Proofs.WG.Lifetimes.ReleaseAmbient
import Leanux.Proofs.WG.Lifetimes.AllocationInitial
import Leanux.Proofs.WG.Lifetimes.AllocationAmbient
import Leanux.Proofs.WG.Lifetimes.SessionFailure
import Leanux.Proofs.WG.Lifetimes.PeerAllocationFailure
import Leanux.Proofs.WG.Lifetimes.ReceiveEntryFailure
import Leanux.Proofs.WG.Lifetimes.MaintenanceCalls

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

/-- Given callback erasure, the mixed receive-enqueue observer has the complete
original result and World, or the exact original error, on every input. -/
theorem enqueue_mixed_access_erasure (irq : Lifetimes.MixedM Unit) (original : M Unit)
    (he : ErasesPrefix irq original) (id : SkbId) (state : PacketState) :
    ErasesPrefix (Lifetimes.enqueuePerPeerRxPrefix irq id state)
      (enqueuePerPeerRx original id state) :=
  Lifetimes.enqueuePerPeerRxPrefix_erases he id state

/-- A callback satisfying the same invariant contract gives a safe appended
mixed access prefix on every enqueue outcome and preserves the store invariants
on success. These are identities actually resolved, not raw-reference provenance. -/
theorem enqueue_mixed_access_preserves (irq : Lifetimes.MixedM Unit)
    (hi : PrefixPreserves Lifetimes.MixedInv Lifetimes.LifetimeEvent.Safe irq)
    (id : SkbId) (state : PacketState) :
    PrefixPreserves Lifetimes.MixedInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.enqueuePerPeerRxPrefix irq id state) :=
  Lifetimes.enqueuePerPeerRxPrefix_preserves hi id state

/-- With the original no-op callback, receive enqueue preserves the mixed
access invariant and retains a safe observation prefix even when it fails. -/
theorem enqueue_mixed_access_pure (id : SkbId) (state : PacketState) :
    PrefixPreserves Lifetimes.MixedInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.enqueuePerPeerRxPrefix (pure ()) id state) :=
  Lifetimes.enqueuePerPeerRxPrefix_pure_preserves id state

/-- Keypair lookup failure during enqueue retains exactly the preceding RX
packet read and the prior mixed history, for every input World and callback. -/
theorem enqueue_keypair_failure_prefix (irq : Lifetimes.MixedM Unit) (id : SkbId)
    (state : PacketState) (w : World) (h : List Lifetimes.LifetimeEvent)
    (pkt : RxPacket) (e : Stop) (hr : (getRxSkb id).run w = .ok (pkt, w))
    (hk : (getKeypair pkt.keypair).run w = .error e) :
    runPrefix (Lifetimes.enqueuePerPeerRxPrefix irq id state) w h =
      (.error e, h ++ [.packet (.read (.inr id) (Lifetimes.packetStamp w id))]) :=
  Lifetimes.enqueuePerPeerRxPrefix_keypair_failure irq id state w h pkt e hr hk

/-- Original peer acquisition emits its two reads and conditional write in
source order, retaining the exact prefix on pending-worker or refcount failure. -/
theorem peer_acquire_access_exact (id : PeerId) (w : World) (h : List Peers.PeerEvent) :
    runPrefix (Lifetimes.peerGetLocal id) w h =
      ((peerGet id).run w, h ++ Lifetimes.peerGetEvents id w) :=
  Lifetimes.peerGetLocal_run id w h

/-- The mixed packet-decryption observer preserves the original complete
result and World, or exact error, for every input packet and World. -/
theorem decrypt_packet_access_erasure (pkt : RxPacket) :
    ErasesPrefix (Lifetimes.decryptPacketPrefix pkt) (decryptPacket pkt) :=
  Lifetimes.decryptPacketPrefix_erases pkt

/-- From the mixed store invariant, packet decryption appends a safe access
prefix on every outcome and preserves that invariant on success. The rejection
update uses the stamp resolved by its fresh second keypair getter. -/
theorem decrypt_packet_access_preserves (pkt : RxPacket) :
    PrefixPreserves Lifetimes.MixedInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.decryptPacketPrefix pkt) :=
  Lifetimes.decryptPacketPrefix_preserves pkt

/-- Failure in decryption's access-free rejection expression retains exactly
the first keypair read; no validity write has occurred. -/
theorem decrypt_rejection_failure_prefix (pkt : RxPacket) (w entered : World)
    (h : List Lifetimes.LifetimeEvent) (k : Keypair) (e : Stop)
    (hb : (branch .decNoKeypair false).run w = .ok (false, entered))
    (hg : (getKeypair pkt.keypair).run entered = .ok (k, entered))
    (hr : (Lifetimes.decryptKeyReject k).run entered = .error e) :
    runPrefix (Lifetimes.decryptPacketPrefix pkt) w h =
      (.error e, h ++ [.keypair (.read pkt.keypair k.internalId)]) :=
  Lifetimes.decryptPacketPrefix_reject_failure pkt w entered h k e hb hg hr

/-- Callback erasure contracts give all-input erasure for one original decrypt
worker iteration, including its enqueue, softirq, IRQ and rescheduling calls. -/
theorem decrypt_iteration_access_erasure (softirq irq : Lifetimes.MixedM Unit)
    (resched : Lifetimes.MixedM Bool) (originalSoftirq originalIrq : M Unit)
    (originalResched : M Bool) (hs : ErasesPrefix softirq originalSoftirq)
    (hi : ErasesPrefix irq originalIrq) (hr : ErasesPrefix resched originalResched) :
    ErasesPrefix (Lifetimes.decryptIterPrefix softirq irq resched)
      (decryptIter originalSoftirq originalIrq originalResched) :=
  Lifetimes.decryptIterPrefix_erases hs hi hr

/-- If each callback preserves the mixed access invariant, one decrypt worker
iteration retains a safe appended prefix even on failure. No identity-equality
frame across callbacks or whole-run scheduler coverage is assumed. -/
theorem decrypt_iteration_access_preserves (softirq irq : Lifetimes.MixedM Unit)
    (resched : Lifetimes.MixedM Bool)
    (hs : PrefixPreserves Lifetimes.MixedInv Lifetimes.LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves Lifetimes.MixedInv Lifetimes.LifetimeEvent.Safe irq)
    (hr : PrefixPreserves Lifetimes.MixedInv Lifetimes.LifetimeEvent.Safe resched) :
    PrefixPreserves Lifetimes.MixedInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.decryptIterPrefix softirq irq resched) :=
  Lifetimes.decryptIterPrefix_preserves hs hi hr

/-- Finite sequences of complete keypairGet/keypairPut, freeTxSkb/freeRxSkb
and keypairsClear calls erase to the original outcome and first Stop. The
sequence API discards keypairGet's optional result; the helper equation below
retains it. No arbitrary caller or scheduler coverage is claimed. -/
theorem release_call_sequence_erasure (calls : List Lifetimes.ReleaseCall) :
    ErasesPrefix (Lifetimes.ReleaseCall.observe calls) (Lifetimes.ReleaseCall.execute calls) :=
  Lifetimes.ReleaseCall.observe_erases calls

/-- Every outcome of this release-only family retains a safe appended mixed
history. Successful outcomes also preserve released-identity absence and
resident uniqueness. ReleaseInv adds keypair and cross-TX/RX uniqueness to
MixedInv; it assumes no allocation frontier and makes no allocation or device
lifecycle claim. -/
theorem release_call_sequence_preserves (calls : List Lifetimes.ReleaseCall) :
    PrefixPreserves Lifetimes.ReleaseInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.ReleaseCall.observe calls) :=
  Lifetimes.ReleaseCall.observe_preserves calls

/-- Keypair acquisition's exact result and observations on every input:
null/missing has no resolved access; zero and overflow retain only the read;
a successful increment also records the write. -/
theorem keypair_get_access_observation (kp : Option KeypairId) (w : World)
    (h : List Lifetimes.LifetimeEvent) :
    runPrefix (Lifetimes.keypairGetPrefix kp) w h =
      ((keypairGet kp).run w, h ++ Lifetimes.keypairGetEvents kp w) :=
  Lifetimes.keypairGetPrefix_run kp w h

/-- Keypair put reads and writes a resolved resident, then releases exactly
when its original count was one. The equation includes failing executions. -/
theorem keypair_put_access_observation (kp : Option KeypairId) (now : Bool)
    (w : World) (h : List Lifetimes.LifetimeEvent) :
    runPrefix (Lifetimes.keypairPutPrefix kp now) w h =
      ((keypairPut kp now).run w, h ++ Lifetimes.keypairPutEvents kp w) :=
  Lifetimes.keypairPutPrefix_run kp now w h

/-- A zero-count keypair put fails after the read and decrementing write.
Its retained prefix has no release; failure exposes no final World. -/
theorem keypair_zero_refcount_failure_prefix (id : KeypairId) (now : Bool)
    (w : World) (h : List Lifetimes.LifetimeEvent) (d : Device) (k : Keypair)
    (hd : w.k.wg = some d) (hk : d.keypairs[id]? = some k) (hz : k.refcount = 0) :
    runPrefix (Lifetimes.keypairPutPrefix (some id) now) w h =
      (.error (.outsideDomain
        s!"{Decision.refcountSubNonpositive.info.file}:{Decision.refcountSubNonpositive.info.line}"
        "refcount_warn_saturate (use after free)"),
        h ++ [.keypair (.read id k.internalId), .keypair (.write id k.internalId)]) :=
  Lifetimes.keypairPutPrefix_zero_failure id now w h d k hd hk hz

/-- TX free records its successful getter before the epoch-tagged release.
An unsuccessful getter records neither access nor release. -/
theorem free_tx_access_observation (id : SkbId) (w : World) (h : List Lifetimes.LifetimeEvent) :
    runPrefix (Lifetimes.freeTxSkbPrefix id) w h = match (getTxSkb id).run w with
      | .error e => (.error e, h)
      | .ok (_, _) => ((freeTxSkb id).run w,
          h ++ [.packet (.read (.inl id) (Lifetimes.packetStamp w id)),
                .packet (.release (.inl id) (Lifetimes.packetStamp w id))]) :=
  Lifetimes.freeTxSkbPrefix_run id w h

/-- RX free has the same getter-before-release order and preserves the
original failure when its packet is absent. -/
theorem free_rx_access_observation (id : SkbId) (w : World) (h : List Lifetimes.LifetimeEvent) :
    runPrefix (Lifetimes.freeRxSkbPrefix id) w h = match (getRxSkb id).run w with
      | .error e => (.error e, h)
      | .ok (_, _) => ((freeRxSkb id).run w,
          h ++ [.packet (.read (.inr id) (Lifetimes.packetStamp w id)),
                .packet (.release (.inr id) (Lifetimes.packetStamp w id))]) :=
  Lifetimes.freeRxSkbPrefix_run id w h

/-- Receive enqueue supports callbacks preserving the stronger release
invariant. Every outcome retains a safe prefix; success preserves uniqueness
and released-identity absence. The callback may change resident identities. -/
theorem enqueue_release_access_preserves (irq : Lifetimes.MixedM Unit)
    (hi : PrefixPreserves Lifetimes.ReleaseInv Lifetimes.LifetimeEvent.Safe irq)
    (id : SkbId) (state : PacketState) :
    PrefixPreserves Lifetimes.ReleaseInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.enqueuePerPeerRxPrefix irq id state) :=
  Lifetimes.enqueuePerPeerRxPrefix_release hi id state

/-- One original decrypt iteration supports softirq, IRQ, and rescheduling
observers preserving ReleaseInv. It retains safe failed prefixes and preserves
the stronger invariant on success. Concrete callback coverage, allocation,
device lifecycle, and whole scheduler closure remain separate obligations. -/
theorem decrypt_iteration_release_access_preserves (softirq irq : Lifetimes.MixedM Unit)
    (resched : Lifetimes.MixedM Bool)
    (hs : PrefixPreserves Lifetimes.ReleaseInv Lifetimes.LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves Lifetimes.ReleaseInv Lifetimes.LifetimeEvent.Safe irq)
    (hr : PrefixPreserves Lifetimes.ReleaseInv Lifetimes.LifetimeEvent.Safe resched) :
    PrefixPreserves Lifetimes.ReleaseInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.decryptIterPrefix softirq irq resched) :=
  Lifetimes.decryptIterPrefix_release hs hi hr

/-- Complete keypair creation, including hidden-input failures and ordinary
allocation refusal, erases to the original outcome and complete final World. -/
theorem keypair_allocation_access_erasure (pid : PeerId) :
    ErasesPrefix (Lifetimes.keypairCreatePrefix pid) (keypairCreate pid) :=
  Lifetimes.keypairCreatePrefix_erases pid

/-- Complete keypair creation retains safe failure prefixes and preserves the
allocation invariant on success. No caller, lifecycle, or scheduler closure is
assumed from this helper theorem. -/
theorem keypair_allocation_access_preserves (pid : PeerId) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.keypairCreatePrefix pid) :=
  Lifetimes.keypairCreatePrefix_preserves pid

/-- A successful insertion records allocation then initialization write. Failed
creation and normal memory refusal retain the incoming history exactly. -/
theorem keypair_allocation_access_observation (pid : PeerId) (w : World)
    (h : List Lifetimes.LifetimeEvent) :
    runPrefix (Lifetimes.keypairCreatePrefix pid) w h = match (keypairCreate pid).run w with
      | .error e => (.error e, h)
      | .ok (none, v) => (.ok (none, v), h)
      | .ok (some id, v) => (.ok (some id, v), h ++
          [.keypair (.allocate id (w.k.keypairCounter + 1)),
           .keypair (.write id (w.k.keypairCounter + 1))]) :=
  Lifetimes.keypairCreatePrefix_observation pid w h

/-- The two constructors name exactly newTxSkb and newRxSkb, with their real
packet argument. Their observer preserves every original outcome. -/
theorem packet_allocation_access_erasure (a : Lifetimes.PacketAllocation) :
    ErasesPrefix a.observed a.original := a.erases

/-- Both original packet allocators preserve the allocation bounds and tagged
lifetime invariant. This is a helper contract, not device lifecycle closure. -/
theorem packet_allocation_access_preserves (a : Lifetimes.PacketAllocation) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe a.observed :=
  a.preserves

/-- Packet allocation has no resolved read. Successful creation records the
epoch-tagged allocation and initializing write; failure records neither.
All-input equations do not assume vacant destinations; the preservation theorem
requires AllocationInv, which supplies vacancy. -/
theorem packet_allocation_access_observation (a : Lifetimes.PacketAllocation) (w : World)
    (h : List Lifetimes.LifetimeEvent) :
    runPrefix a.observed w h = match a.original.run w with
      | .error e => (.error e, h)
      | .ok (id, v) => (.ok (id, v), h ++
          [.packet (.allocate (a.slot id) (Lifetimes.packetStamp w id)),
           .packet (.write (a.slot id) (Lifetimes.packetStamp w id))]) :=
  a.observation w h

/-- The stronger invariant makes all four allocator destination slots vacant.
Peer lifetime bounds alone would not imply the peer slot fact. -/
theorem allocation_destinations_vacant (w : World) (d : Device)
    (h : List Lifetimes.LifetimeEvent) (hi : Lifetimes.AllocationInv h w)
    (hd : w.k.wg = some d) :
    d.peers[d.nextPeer]? = none ∧ d.keypairs[d.nextKeypairId]? = none ∧
    d.txSkbs[d.nextSkb]? = none ∧ d.rxSkbs[d.nextSkb]? = none :=
  ⟨hi.peer_vacant hd, hi.key_vacant hd, hi.packet_vacant hd⟩

/-- Every original runner fixture starts with the stronger allocation
invariant. All fixture flags are arbitrary, including seccompChild. -/
theorem allocation_initial_fixture (rlimit : Nat) (net bare foreign stepped seccompChild : Bool)
    (w : World) (hw : w.k = Runner.initialKernel rlimit net bare foreign stepped seccompChild) :
    Lifetimes.AllocationInv [] w :=
  Lifetimes.allocation_initial rlimit net bare foreign stepped seccompChild w hw


/-- The actual peer reference helpers retain allocation frontiers and released
stamp bounds, as well as safe history. This does not cover peer creation or
bulk device destruction. -/
theorem peer_reference_allocation_preserves (id : PeerId) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.peerGetMixed id) ∧
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.peerPutMixed (some id)) :=
  ⟨Lifetimes.peerGetMixed_allocation id, Lifetimes.peerPutMixed_allocation (some id)⟩

/-- Finite sequences of the five original acquire/put/free/clear calls preserve
AllocationInv on success and retain safe histories on every outcome. The
existing exact erasure and event equations still apply, including refcount
failures after writes. Allocation and lifecycle callers are separate families. -/
theorem release_family_allocation_preserves (cs : List Lifetimes.ReleaseCall) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.ReleaseCall.observe cs) :=
  Lifetimes.ReleaseCall.observe_preserves_allocation cs

/-- Receive enqueue carries allocation metadata and history bounds through a
callback that itself preserves AllocationInv. No identity-equality premise is
imposed on the callback. -/
theorem enqueue_allocation_access_preserves (irq : Lifetimes.MixedM Unit)
    (hi : PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe irq)
    (id : SkbId) (state : PacketState) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.enqueuePerPeerRxPrefix irq id state) :=
  Lifetimes.enqueuePerPeerRxPrefix_allocation hi id state

/-- Complete packet decryption preserves the allocation-aware invariant and
retains safe error prefixes. Its observation and erasure definitions are the
same as in the earlier mixed-access result. -/
theorem decrypt_packet_allocation_access_preserves (pkt : RxPacket) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.decryptPacketPrefix pkt) :=
  Lifetimes.decryptPacketPrefix_allocation pkt

/-- One decrypt iteration carries AllocationInv through explicitly contracted
callbacks. Concrete callback coverage, device epochs across destruction and
creation, and whole-scheduler closure remain separate obligations. -/
theorem decrypt_iteration_allocation_access_preserves (softirq irq : Lifetimes.MixedM Unit)
    (resched : Lifetimes.MixedM Bool)
    (hs : PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe irq)
    (hr : PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe resched) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.decryptIterPrefix softirq irq resched) :=
  Lifetimes.decryptIterPrefix_allocation hs hi hr

/-- Both complete original rotation calls preserve their exact outcomes and
Worlds after observations are erased. Scalar keypair slots may alias. -/
theorem keypair_rotation_access_erasure (pid : PeerId) (kp : KeypairId) :
    ErasesPrefix (Lifetimes.addNewKeypairPrefix pid kp) (addNewKeypair pid kp) ∧
    ErasesPrefix (Lifetimes.receivedWithKeypairPrefix pid kp) (receivedWithKeypair pid kp) :=
  ⟨Lifetimes.addNewKeypairPrefix_erases pid kp, Lifetimes.receivedWithKeypairPrefix_erases pid kp⟩

/-- Rotation and responder confirmation retain safe access prefixes on every
outcome and preserve allocation bounds on success. This does not establish
ownership or validity of scalar keypair references stored in a peer. -/
theorem keypair_rotation_access_preserves (pid : PeerId) (kp : KeypairId) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.addNewKeypairPrefix pid kp) ∧
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.receivedWithKeypairPrefix pid kp) :=
  ⟨Lifetimes.addNewKeypairPrefix_allocation pid kp, Lifetimes.receivedWithKeypairPrefix_allocation pid kp⟩

/-- The complete original beginSession call, including allocation, initialization,
rotation, and scalar index replacement, is recovered on every input World. -/
theorem begin_session_access_erasure (pid : PeerId) :
    ErasesPrefix (Lifetimes.beginSessionPrefix pid) (beginSession pid) :=
  Lifetimes.beginSessionPrefix_erases pid

/-- Session creation observes all resolved peer and keypair accesses, retaining
safe prefixes on failure and AllocationInv on success. Caller, scheduler,
device-lifecycle, and scalar-reference integrity remain separate obligations. -/
theorem begin_session_access_preserves (pid : PeerId) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.beginSessionPrefix pid) :=
  Lifetimes.beginSessionPrefix_allocation pid

/-- A conditional whole-call equation for the actual birthdate-clock failure
path. The consecutive original-run premises determine the retained allocation
and access prefix; this is not a recorded runner reproduction. -/
theorem begin_session_birthdate_failure_prefix (pid : PeerId) (kp : KeypairId)
    (w allocEntry allocated guarded configured clockEntry : World)
    (h : List Lifetimes.LifetimeEvent) (before current : Peer) (k : Keypair)
    (selected : Bool) (e : Stop)
    (hbefore : (getPeer pid).run w = .ok (before, w))
    (hstate : (Lifetimes.sessionStateRejected before.handshakeState).run w = .ok (false, allocEntry))
    (hcreate : (keypairCreate pid).run allocEntry = .ok (some kp, allocated))
    (hguard : (branch .sessionNoKeypair (Option.isNone (some kp))).run allocated = .ok (false, guarded))
    (hpeer : (getPeer pid).run guarded = .ok (current, guarded))
    (hkey : (getKeypair kp).run guarded = .ok (k, guarded))
    (hwrite : (setKeypair kp {k with iAmTheInitiator := before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE, remoteIndex := current.remoteIndex}).run guarded = .ok ((), configured))
    (hselect : (branch .sessionInitiator (before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE)).run configured =
      .ok (selected, clockEntry))
    (hclock : (hiddenClock .deriveKeysBirthdate).run clockEntry = .error e) :
    runPrefix (Lifetimes.beginSessionPrefix pid) w h =
      (.error e, h ++ [.peer (.read pid before.internalId),
        .keypair (.allocate kp (allocEntry.k.keypairCounter + 1)),
        .keypair (.write kp (allocEntry.k.keypairCounter + 1)),
        .peer (.read pid current.internalId), .keypair (.read kp k.internalId),
        .keypair (.write kp k.internalId)]) :=
  Lifetimes.beginSessionPrefix_clock_failure pid kp w allocEntry allocated guarded configured clockEntry
    h before current k selected e hbefore hstate hcreate hguard hpeer hkey hwrite hselect hclock


/-- Focusing the existing complete peer-creation observer into the mixed
history preserves the exact original result, Stop, and successful World for
all inputs. The event stream comes from the existing complete peer observer. -/
theorem peer_create_mixed_access_erasure (key : Key) (psk : Option Key) :
    ErasesPrefix (Lifetimes.peerCreateMixed key psk) (peerCreate key psk) :=
  Lifetimes.peerCreateMixed_erases key psk

/-- Complete peer creation retains safe mixed histories on failure and
preserves AllocationInv on success. The slot bound supplies vacancy in this
safety domain; no lifecycle or scalar-reference ownership claim is made. -/
theorem peer_create_allocation_access_preserves (key : Key) (psk : Option Key) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.peerCreateMixed key psk) :=
  Lifetimes.peerCreateMixed_preserves key psk

/-- Original successful execution preserves other-family residents and
allocation metadata except nextPeer. A created ID is the old nextPeer, whose
final value advances to ID+1; ordinary refusal leaves the metadata unchanged.
This exact geometry does not itself assume a vacant destination. -/
theorem peer_create_allocation_geometry (key : Key) (psk : Option Key)
    (w v : World) (result : Except Int PeerId)
    (hr : (peerCreate key psk).run w = .ok (result, v)) :
    Lifetimes.PeerCreationGeometry w result v :=
  Lifetimes.peerCreate_geometry key psk w v result hr

/-- A conditional whole-call equation: the first initializer's clock failure
retains the allocation and initial peer write. Premises execute the original
prelude; this is not a recorded runner reproduction. -/
theorem peer_create_cache_clock_failure_prefix (key : Key) (psk : Option Key)
    (w guarded allocated reserved entry : World) (d : Device)
    (h : List Lifetimes.LifetimeEvent) (e : Stop)
    (hdev : getDev.run w = .ok (d, w))
    (hfull : (branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE)
      d.numPeers MAX_PEERS_PER_DEVICE).run w = .ok (false, guarded))
    (halloc : (hiddenAlloc .kmemCacheZallocPeer).run guarded = .ok (true, allocated))
    (hmem : (branch .peerCreateNoMem false).run allocated = .ok (false, reserved))
    (hcache : (branch .peerCreateDstCacheFail false).run reserved = .ok (false, entry))
    (ha : entry.armRecords = true) (hc : entry.dstCacheRecords = true)
    (hclock : (hiddenU64 .dstCacheResetTs).run
      (Peers.creationCoreWorld entry d.nextPeer key) = .error e) :
    runPrefix (Lifetimes.peerCreateMixed key psk) w h =
      (.error e, h ++ [.peer (.allocate d.nextPeer (entry.k.peerCounter + 1)),
        .peer (.write d.nextPeer (entry.k.peerCounter + 1))]) :=
  Lifetimes.peerCreateMixed_cache_clock_failure key psk w guarded allocated reserved entry d h e
    hdev hfull halloc hmem hcache ha hc hclock

/-- Complete optional-peer acquisition and scalar index/public-key lookup
recover the original result, Stop, and successful World on every input.
Index lookup stops at the first equal index even when its kind is rejected. -/
theorem receive_lookup_access_erasure (peer : Option PeerId) (kinds : List IndexKind)
    (index : Nat) (key : Key) :
    ErasesPrefix (Lifetimes.peerGetMaybeZeroPrefix peer) (peerGetMaybeZero peer) ∧
    ErasesPrefix (Lifetimes.indexLookupPrefix kinds index) (indexLookup kinds index) ∧
    ErasesPrefix (Lifetimes.pubkeyLookupPrefix key) (pubkeyLookup key) :=
  ⟨Lifetimes.peerGetMaybeZeroPrefix_erases peer,
    Lifetimes.indexLookupPrefix_erases kinds index, Lifetimes.pubkeyLookupPrefix_erases key⟩

/-- Lookup retains safe resolved-store access prefixes on every outcome and
preserves AllocationInv on success. No scalar-index consistency or ownership
premise is required or established. -/
theorem receive_lookup_allocation_access_preserves (peer : Option PeerId)
    (kinds : List IndexKind) (index : Nat) (key : Key) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.peerGetMaybeZeroPrefix peer) ∧
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.indexLookupPrefix kinds index) ∧
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.pubkeyLookupPrefix key) :=
  ⟨Lifetimes.AmbientContracts.drop
      (Lifetimes.peerGetMaybeZeroPrefix_spec_ambient Lifetimes.allocationAmbient (fun _ => True) peer),
    Lifetimes.indexLookupPrefix_preserves_ambient Lifetimes.allocationAmbient kinds index,
    Lifetimes.pubkeyLookupPrefix_preserves_ambient Lifetimes.allocationAmbient key⟩

/-- Complete device/peer receive enqueue and consumeData preserve the original
outcomes and successful Worlds after erasure. This includes the ENOSPC
invariant Stop and the EPIPE dead-packet enqueue with its original pure callback. -/
theorem receive_entry_access_erasure (id : SkbId) (msg : List UInt8)
    (src : SkbSource) (ds : Nat) :
    ErasesPrefix (Lifetimes.enqueuePerDeviceAndPeerRxPrefix id) (enqueuePerDeviceAndPeerRx id) ∧
    ErasesPrefix (Lifetimes.consumeDataPrefix msg src ds) (consumeData msg src ds) :=
  ⟨Lifetimes.enqueuePerDeviceAndPeerRxPrefix_erases id,
    Lifetimes.consumeDataPrefix_erases msg src ds⟩

/-- Both complete receive-entry calls retain safe access histories on failure
and AllocationInv on success. This is resolved-store lifetime safety, not
packet delivery, reference ownership, lifecycle, or whole-scheduler closure. -/
theorem receive_entry_allocation_access_preserves (id : SkbId) (msg : List UInt8)
    (src : SkbSource) (ds : Nat) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.enqueuePerDeviceAndPeerRxPrefix id) ∧
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe
      (Lifetimes.consumeDataPrefix msg src ds) :=
  ⟨Lifetimes.enqueuePerDeviceAndPeerRxPrefix_allocation id,
    Lifetimes.consumeDataPrefix_allocation msg src ds⟩

/-- A conditional whole-call equation for device-work queue-record failure:
the original-run premises, including the setter's nested getter, determine
five retained accesses. This is not a recorded runner reproduction. -/
theorem receive_enqueue_queue_failure_prefix (id : SkbId)
    (w marked checked queued selected cpuSet queueEntry : World)
    (h : List Lifetimes.LifetimeEvent) (initial pkt : RxPacket) (p : Peer) (d : Device)
    (cpu : Int) (e : Stop)
    (hfirst : (getRxSkb id).run w = .ok (initial, w))
    (hmark : (setRxSkb id fun p => {p with state := .uncrypted}).run w = .ok ((), marked))
    (hpacket : (getRxSkb id).run marked = .ok (pkt, marked))
    (hpeer : (getPeer pkt.peer).run marked = .ok (p, marked))
    (hfull : (branch .enqueuePeerQueueFull (p.rxQueue.count ≥ MAX_QUEUED_PACKETS)).run marked =
      .ok (false, checked))
    (hwrite : (setPeer pkt.peer {p with rxQueue := p.rxQueue.enqueue id}).run checked = .ok ((), queued))
    (hdev : getDev.run queued = .ok (d, queued))
    (hcpu : (cpumaskNextOnlineFrom d.decryptLastCpu).run queued = .ok (cpu, selected))
    (hset : (modifyDev fun d => {d with decryptLastCpu := cpu}).run selected = .ok ((), cpuSet))
    (hring : (branch .enqueueRingFull d.decryptQueue.full).run cpuSet = .ok (false, queueEntry))
    (hqueue : (queueDeviceWork .decryptWorker).run queueEntry = .error e) :
    runPrefix (Lifetimes.enqueuePerDeviceAndPeerRxPrefix id) w h =
      (.error e, h ++ [.packet (.read (.inr id) (Lifetimes.packetStamp w id)),
        .packet (.write (.inr id) (Lifetimes.packetStamp w id)),
        .packet (.read (.inr id) (Lifetimes.packetStamp marked id)),
        .peer (.read pkt.peer p.internalId), .peer (.write pkt.peer p.internalId)]) :=
  Lifetimes.enqueuePerDeviceAndPeerRxPrefix_queue_failure id w marked checked queued selected cpuSet queueEntry
    h initial pkt p d cpu e hfirst hmark hpacket hpeer hfull hwrite hdev hcpu hset hring hqueue

/-- Every call in the receive-maintenance family erases to its original
result, Stop, and successful World on all inputs, retaining Boolean results
for the timer guard and modifier. This does not execute queued workers. -/
theorem receive_maintenance_access_erasure (call : Lifetimes.MaintenanceCall) :
    ErasesPrefix call.observed call.original := call.erases

/-- Generic resolved-access safety requires an explicit frame for appending
the send-work queue. The ambient contract may include allocation frontiers
and released identities; no time bound or scheduler closure is asserted. -/
theorem receive_maintenance_ambient_access_preserves
    (c : Lifetimes.AmbientContracts I)
    (hq : ∀ pid, PrefixPreserves I Lifetimes.LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})))
    (call : Lifetimes.MaintenanceCall) :
    PrefixPreserves I Lifetimes.LifetimeEvent.Safe call.observed :=
  call.preserves_ambient c hq

/-- Complete endpoint/cache, timer, queued-handshake and receive-key-refresh
calls retain safe access histories on every outcome and AllocationInv on
success. The concrete queue frame is discharged over the original update. -/
theorem receive_maintenance_allocation_access_preserves (call : Lifetimes.MaintenanceCall) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe call.observed :=
  call.allocation

/-- Conditional whole-call failure equation: a handshake-completion clock
Stop retains the two preceding peer reads and writes. Premises name only
consecutive original executions, not an observed history or invariant. -/
theorem receive_maintenance_clock_failure_prefix (pid : PeerId) (site : HiddenSite)
    (w afterDelete clockEntry : World) (p q : Peer) (h : List Lifetimes.LifetimeEvent) (e : Stop)
    (hp : (getPeer pid).run w = .ok (p, w))
    (hdel : (setPeer pid (p.setTimer .retransmitHandshake none)).run w = .ok ((), afterDelete))
    (hq : (getPeer pid).run afterDelete = .ok (q, afterDelete))
    (hreset : (setPeer pid {q with timerHandshakeAttempts := 0, sentLastminuteHandshake := false}).run afterDelete = .ok ((), clockEntry))
    (hclock : (hidden site).run clockEntry = .error e) :
    runPrefix (Lifetimes.timersHandshakeCompletePrefix pid site) w h =
      (.error e, h ++ [.peer (.read pid p.internalId), .peer (.write pid p.internalId),
        .peer (.read pid q.internalId), .peer (.write pid q.internalId)]) :=
  Lifetimes.timersHandshakeCompletePrefix_clock_failure pid site w afterDelete clockEntry p q h e
    hp hdel hq hreset hclock


/-- All seven TX staging-family observers erase to the original result,
Stop, and complete successful World on every input. CPU selection and device
enqueue retain their Nat and Int results. Queued workers are not executed. -/
theorem tx_staging_access_erasure (call : Lifetimes.TxStagingCall) :
    ErasesPrefix call.observed call.original := call.erases

/-- Generic resolved-store access safety for the complete staging family,
with explicit TX allocation/release and scalar device-update contracts.
Cached identity predicates are preserved where the original writes require them. -/
theorem tx_staging_ambient_access_preserves (c : Lifetimes.AmbientContracts I)
    (t : Lifetimes.TxContracts I) (call : Lifetimes.TxStagingCall) :
    PrefixPreserves I Lifetimes.LifetimeEvent.Safe call.observed :=
  call.preserves_ambient c t

/-- The concrete AllocationInv instance retains safe histories on every
outcome and allocation bounds on success. No distinct-packet-ID, ownership,
queue-coherence, delivery, or whole-scheduler premise or conclusion is added. -/
theorem tx_staging_allocation_access_preserves (call : Lifetimes.TxStagingCall) :
    PrefixPreserves Lifetimes.AllocationInv Lifetimes.LifetimeEvent.Safe call.observed :=
  call.allocation

/-- The original TX setter reads its resident before writing. A failing
getter emits nothing; successful resolution emits the read and write in order. -/
theorem tx_setter_exact_observation (id : SkbId) (f : DataPacket → DataPacket)
    (w : World) (h : List Lifetimes.LifetimeEvent) :
    runPrefix (Lifetimes.setTxSkbPrefix id f) w h =
      match (getTxSkb id).run w with
      | .error e => (.error e, h)
      | .ok (_, _) => ((setTxSkb id f).run w,
          h ++ [.packet (.read (.inl id) (Lifetimes.packetStamp w id)),
            .packet (.write (.inl id) (Lifetimes.packetStamp w id))]) :=
  Lifetimes.setTxSkbPrefix_run id f w h

/-- Conditional whole-call equation for a keepalive allocation-record Stop:
the initial peer read remains in the history. Premises describe original
operations; this is not a recorded runner reproduction or normal refusal. -/
theorem tx_keepalive_allocation_failure_prefix (pid : PeerId) (w checked : World) (p : Peer)
    (h : List Lifetimes.LifetimeEvent) (e : Stop)
    (hp : (getPeer pid).run w = .ok (p, w))
    (hb : (branch .keepaliveStagedEmpty p.staged.isEmpty).run w = .ok (true, checked))
    (ha : (hiddenAlloc .keepaliveSkb).run checked = .error e) :
    runPrefix (Lifetimes.sendKeepalivePrefix pid) w h =
      (.error e, h ++ [.peer (.read pid p.internalId)]) :=
  Lifetimes.sendKeepalivePrefix_alloc_failure pid w checked p h e hp hb ha

end Leanux.Proofs.WG.LifetimeSafety
