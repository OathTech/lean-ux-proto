import Leanux.Proofs.WG.Lifetimes.RunnerSafety
import Leanux.Proofs.WG.Lifetimes.SyscallsAudit
import Leanux.Proofs.WG.Lifetimes.EnvRemainingCalls
import Leanux.Proofs.WG.Lifetimes.EnvDeferredCalls
import Leanux.Proofs.WG.Lifetimes.BatchAudit
import Leanux.Proofs.WG.Lifetimes.DumpAccess
import Leanux.Proofs.WG.Lifetimes.PeerRemoval
import Leanux.Proofs.WG.Lifetimes.DeviceControls
import Leanux.Proofs.WG.Lifetimes.DeviceLifecycle
import Leanux.Proofs.WG.Lifetimes.TimerCallbacks
import Leanux.Proofs.WG.Lifetimes.AllowedIpsAccess
import Leanux.Proofs.WG.Lifetimes.AllowedIpsInsert
import Leanux.Proofs.WG.Lifetimes.ConfigurationDevice
import Leanux.Proofs.WG.Lifetimes.BatchCalls
import Leanux.Proofs.WG.Lifetimes.ReceiveIngress
import Leanux.Proofs.WG.Lifetimes.SocketCalls
import Leanux.Proofs.WG.Lifetimes.EncryptWorker
import Leanux.Proofs.WG.Lifetimes.TxWorker
import Leanux.Proofs.WG.Lifetimes.HandshakeCalls
import Leanux.Proofs.WG.Lifetimes.HandshakeSend
import Leanux.Proofs.WG.Lifetimes.CookieAccess
import Leanux.Proofs.WG.Lifetimes.ReceivePoll
import Leanux.Proofs.WG.Lifetimes.ReceiveFailure
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
import Leanux.Proofs.WG.Lifetimes.StackAccess

/-! R2's store-identity components: whole-operation keypair evolution,
peer allocation/reference sequences, and packet primitive sequences within a device
epoch. The final three exports supply initialized caller and lifecycle closure. -/
namespace Leanux.Proofs.WG.LifetimeSafety
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.ReplayWindow
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.Framing

/-- Erasing all observations of peerCreate, including its cache, handshake and
clock initialization helpers, returns the exact original result or Stop for
every WG and Ambient state and initial history. -/
theorem peer_create_access_erasure (key : Key) (psk : Option Key) :
    ErasesStatePrefix (Peers.peerCreatePrefix key psk) (peerCreate key psk) :=
  Peers.peerCreatePrefix_erases key psk

/-- The original creation core increments the identity counter and performs
the first insertion before any initializer runs. A present device emits exactly
allocation then write; the original no-device setter is a no-op. This all-input
statement does not assume an empty destination or log overwritten objects as
released. -/
theorem peer_creation_core_observation (pid : PeerId) (key : Key)
    (w : WGWorld) (ambient : Ambient) (h : List Peers.PeerEvent) :
    runStatePrefix (Peers.peerCreateCorePrefix pid key) w ambient h =
      (.ok (((), Peers.creationCoreWorld w pid key), ambient),
        if w.dev.isSome then
          h ++ [.allocate pid (w.peerCounter + 1), .write pid (w.peerCounter + 1)]
        else h) := by
  rw [Peers.peerCreateCorePrefix_run, Peers.peerCreateCore_run]

/-- At the creation core followed by the first initializer, a failed recorded
cache-clock read retains the prior allocation and write observations. The
failure exposes no final WG and Ambient state; this is the source's initialization cut, not a
whole-runner claim. -/
theorem peer_creation_record_failure_prefix (pid : PeerId) (key : Key) (w : WGWorld)
    (ambient : Ambient) (h : List Peers.PeerEvent) (e : Stop) (hd : w.dev.isSome = true)
    (ha : ambient.armRecords = true) (hc : w.dstCacheRecords = true)
    (hr : ((hiddenJiffies .dstCacheResetTs : WG.M UInt64).run
      (Peers.creationCoreWorld w pid key)).run ambient = .error e) :
    runStatePrefix (do Peers.peerCreateCorePrefix pid key; Peers.dstCacheResetPrefix pid) w ambient h =
      (.error e, h ++ [.allocate pid (w.peerCounter + 1), .write pid (w.peerCounter + 1)]) :=
  Peers.creation_core_clock_failure pid key w ambient h e hd ha hc hr

/-- Finite sequences of complete peerCreate, peerPut and wgGetDeviceDone calls
preserve the original execution and first Stop after observation erasure. The
family discards ordinary return values, including create's ordinary error code,
and retains the full WG and Ambient state on success. -/
theorem peer_creation_call_sequence_erasure (calls : List Peers.CreationCall) : ErasesStatePrefix (Peers.CreationCall.observe calls) (Peers.CreationCall.execute calls) :=
  Peers.CreationCall.observe_erases calls

/-- In this finite creation/reference caller family, no read, write or new
allocation follows a release of the same identity, including prefixes ending in
failure. Initial resident identities are unique and frontier-bounded, and every
previously released identity is absent and frontier-bounded. This covers the
listed callers' internal accesses, not cursor provenance, other callers or
complete release reporting when malformed allocation slots overwrite peers. -/
theorem peer_creation_call_sequence_prefix_safe (calls : List Peers.CreationCall)
    (w : WGWorld) (ambient : Ambient) (h : List Peers.PeerEvent) (n : Nat)
    (hi : Peers.CreationInv h w) :
    Lifetimes.AccessEvent.Safe
      ((runStatePrefix (Peers.CreationCall.observe calls) w ambient h).2.take n) :=
  (Peers.CreationCall.observe_preserves calls w ambient h hi).choose_spec.2.1.take n

/-- The complete original peerPut is observed at its successful getter,
the actual setter and the inline release. For every WG and Ambient state, erasing observations
returns the exact original result or Stop, while errors retain the exact prefix. -/
theorem peer_put_access_exact (peer : Option PeerId) (w : WGWorld) (ambient : Ambient) (h : List Peers.PeerEvent) :
    runStatePrefix (Peers.peerPutPrefix peer) w ambient h =
      (((peerPut peer).run w).run ambient, h ++ Peers.peerPutEvents peer w) :=
  Peers.peerPutPrefix_run peer w ambient h

/-- The actual dump-completion callback has the same complete peer-access
observations as its peerPut call, including every failure prefix. This statement
neither asserts cursor provenance nor covers the separate dump-body caller. -/
theorem dump_done_access_exact (ctx : DumpCtx) (w : WGWorld) (ambient : Ambient) (h : List Peers.PeerEvent) :
    runStatePrefix (Peers.wgGetDeviceDonePrefix ctx) w ambient h =
      (((wgGetDeviceDone ctx).run w).run ambient, h ++ Peers.peerPutEvents ctx.nextPeer w) :=
  Peers.wgGetDeviceDonePrefix_run ctx w ambient h

/-- Observation of a finite sequence drawn from peerPut and wgGetDeviceDone
preserves the complete original execution result, including its first error.
The family contains no allocation, device lifecycle or other WG caller. -/
theorem peer_release_call_sequence_erasure (calls : List Peers.AccessCall) : ErasesStatePrefix (Peers.AccessCall.observe calls) (Peers.AccessCall.execute calls) :=
  Peers.AccessCall.observe_erases calls

/-- For this finite no-allocation caller family, no observed access follows a
release of the same identity, even in a prefix ending in an error. The initial
invariant requires unique resident identities and absence of previously released
ones; it does not assume the desired property of future execution. -/
theorem peer_release_call_sequence_prefix_safe (calls : List Peers.AccessCall)
    (w : WGWorld) (ambient : Ambient) (h : List Peers.PeerEvent) (n : Nat)
    (hi : Peers.AccessInv h w) :
    Lifetimes.AccessEvent.Safe
      ((runStatePrefix (Peers.AccessCall.observe calls) w ambient h).2.take n) :=
  (Peers.AccessCall.observe_preserves calls w ambient h hi).choose_spec.2.1.take n

/-- The complete original peerCreate call has an exact identity-store effect:
an ordinary error result leaves it unchanged, while success increments the
frontier and inserts that fresh stamp at the returned slot. No assumption that
the old nextPeer slot was empty is made by this refinement. -/
theorem peer_create_exact (publicKey : Key) (psk : Option Key)
    (w w' : WGWorld) (result : Except Int PeerId) (ambient ambient' : Ambient)
    (hr : ((peerCreate publicKey psk).run w).run ambient = .ok ((result, w'), ambient')) :
    Peers.snapshot w' = match result with
      | .error _ => Peers.snapshot w
      | .ok pid => (Peers.snapshot w).allocate pid :=
  Peers.peerCreate_exact publicKey psk w w' result ambient ambient' hr

/-- A successful original peerCreate returns a slot containing the next global
peer allocation identity, strictly beyond the call's initial frontier. -/
theorem peer_create_fresh_identity (publicKey : Key) (psk : Option Key)
    (w w' : WGWorld) (pid : PeerId) (ambient ambient' : Ambient)
    (hr : ((peerCreate publicKey psk).run w).run ambient = .ok ((.ok pid, w'), ambient')) :
    (Peers.snapshot w').frontier = (Peers.snapshot w).frontier + 1 ∧
      (Peers.snapshot w').slots pid = some ((Peers.snapshot w).frontier + 1) :=
  Peers.peerCreate_fresh publicKey psk w w' pid ambient ambient' hr

/-- Across a finite sequence of actual peer lookup, reference acquisition
(including get-unless-zero), release and atomic creation calls, every identity remains
within the allocation frontier. This is a primitive-call sequence contract,
not yet whole-syscall or internal-access coverage. -/
theorem peer_allocation_sequence_bounded (w w' : WGWorld) (ambient ambient' : Ambient)
    (h : Peers.AllocationSequence w ambient w' ambient')
    (hb : Lifetimes.Bounded (Peers.snapshot w)) :
    Lifetimes.Bounded (Peers.snapshot w') :=
  (Peers.allocation_sequence_contract h hb).1

/-- An already allocated peer identity absent before such a finite sequence
cannot return through any mixture of those lookup, reference and creation calls.
The frontier bound excludes identities first allocated during the sequence. -/
theorem peer_allocation_sequence_no_resurrection (w w' : WGWorld) (ambient ambient' : Ambient)
    (h : Peers.AllocationSequence w ambient w' ambient')
    (hb : Lifetimes.Bounded (Peers.snapshot w)) (stamp : Nat)
    (hs : stamp ≤ (Peers.snapshot w).frontier)
    (ha : Lifetimes.Absent (Peers.snapshot w) stamp) :
    Lifetimes.Absent (Peers.snapshot w') stamp :=
  (Peers.allocation_sequence_contract h hb).2.absent hs ha

/-- The original conditional reference-acquisition helper, including its null
and zero-count branches, preserves the complete peer identity projection. -/
theorem peer_get_unless_zero_preserves_identities (peer : Option PeerId)
    (w w' : WGWorld) (ambient ambient' : Ambient) (result : Option PeerId)
    (hr : ((peerGetMaybeZero peer).run w).run ambient = .ok ((result, w'), ambient')) :
    Peers.snapshot w' = Peers.snapshot w :=
  (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (Peers.peerGetMaybeZero_samePeerSnapshot peer) w ambient result w' ambient' hr

/-- Every successful actual peer getter resolves the identity resident in its
slot now. It does not certify that a caller's raw slot reference owns a ref. -/
theorem peer_lookup_current (i : PeerId) (w w' : WGWorld) (p : Peer)
    (ambient ambient' : Ambient)
    (hr : ((getPeer i).run w).run ambient = .ok ((p, w'), ambient')) :
    w' = w ∧ ambient' = ambient ∧ (Peers.snapshot w).slots i = some p.internalId :=
  Peers.getPeer_current i w w' p ambient ambient' hr

/-- The actual unconditional peer setter preserves store identities when its
replacement has the same identity as the current resident of that slot. -/
theorem peer_set_current_identity (i : PeerId) (p : Peer) (w w' : WGWorld)
    (ambient ambient' : Ambient)
    (hl : (Peers.snapshot w).slots i = some p.internalId)
    (hr : ((setPeer i p).run w).run ambient = .ok (((), w'), ambient')) :
    Peers.snapshot w' = Peers.snapshot w :=
  Peers.setPeer_same i p w w' ambient ambient' hl hr

/-- Finite successful sequences of the original getPeer, peerGet and peerPut
retain or remove store identities and leave the allocation frontier unchanged.
This is a helper-family statement, without a whole-run coverage premise. -/
theorem peer_reference_sequence_retains_identities (w w' : WGWorld) (ambient ambient' : Ambient)
    (h : Peers.Sequence w ambient w' ambient') : Lifetimes.Retained (Peers.snapshot w) (Peers.snapshot w') :=
  Peers.sequence_retained h

/-- An identity absent before a finite original peer-reference helper sequence
cannot reappear afterward; these helpers perform no peer allocation. -/
theorem peer_reference_sequence_no_resurrection (w w' : WGWorld) (ambient ambient' : Ambient) (stamp : Nat)
    (h : Peers.Sequence w ambient w' ambient') (ha : Lifetimes.Absent (Peers.snapshot w) stamp) :
    Lifetimes.Absent (Peers.snapshot w') stamp :=
  fun i hi => ha i ((Peers.sequence_retained h).2 i stamp hi)

/-- Any finite sequence of successful original packet-store primitives keeps
the device epoch, the allocation bound and every surviving old slot identity.
The named family is exactly the eight TX/RX helpers, not the whole runner. -/
theorem packet_primitive_sequence_lifetimes (w w' : WGWorld) (ambient ambient' : Ambient)
    (h : Packets.Sequence w ambient w' ambient') (hi : Packets.Inv w) :
    Packets.Inv w' ∧ Packets.epoch w' = Packets.epoch w ∧
      Lifetimes.Transition (Packets.snapshot w) (Packets.snapshot w') :=
  Packets.sequence_contract h hi

/-- A previously allocated packet identity absent before a finite successful
sequence of original store primitives remains absent afterward. Device resets
and internal accesses in composite callers are outside this helper family. -/
theorem packet_primitive_sequence_no_resurrection (w w' : WGWorld) (ambient ambient' : Ambient) (stamp : Nat)
    (h : Packets.Sequence w ambient w' ambient') (hi : Packets.Inv w)
    (hb : stamp ≤ (Packets.snapshot w).frontier)
    (ha : Lifetimes.Absent (Packets.snapshot w) stamp) :
    Lifetimes.Absent (Packets.snapshot w') stamp :=
  (Packets.sequence_contract h hi).2.2.absent hb ha

/-- Filling an empty packet slot through these original primitive executions
requires an allocation identity newer than their initial allocation frontier. -/
theorem packet_primitive_sequence_empty_slot_fresh (w w' : WGWorld) (ambient ambient' : Ambient)
    (slot : Packets.Slot) (stamp : Nat) (h : Packets.Sequence w ambient w' ambient')
    (hi : Packets.Inv w) (he : (Packets.snapshot w).slots slot = none)
    (hl : (Packets.snapshot w').slots slot = some stamp) :
    (Packets.snapshot w).frontier < stamp :=
  (Packets.sequence_contract h hi).2.2.empty_fresh he hl

/-- Bounded packet stores make the shared next allocation slot empty in both
directions, so either original allocation helper allocates a fresh slot. -/
theorem packet_next_allocation_slots_empty (w : WGWorld) (d : Device)
    (hd : w.dev = some d) (hi : Packets.Inv w) :
    d.txSkbs[d.nextSkb]? = none ∧ d.rxSkbs[d.nextSkb]? = none :=
  Packets.allocation_slots_empty w d hd hi

/-- A successful original TX getter returns the current resident packet and
leaves the entire WG and Ambient state unchanged. -/
theorem packet_tx_lookup_current (i : SkbId) (w w' : WGWorld) (p : DataPacket)
    (ambient ambient' : Ambient)
    (hr : ((getTxSkb i).run w).run ambient = .ok ((p, w'), ambient')) :
    w' = w ∧ ambient' = ambient ∧ ∃ d, w.dev = some d ∧ d.txSkbs[i]? = some p :=
  Packets.getTxSkb_current i w w' p ambient ambient' hr

/-- A successful original RX getter returns the current resident packet and
leaves the entire WG and Ambient state unchanged. -/
theorem packet_rx_lookup_current (i : SkbId) (w w' : WGWorld) (p : RxPacket)
    (ambient ambient' : Ambient)
    (hr : ((getRxSkb i).run w).run ambient = .ok ((p, w'), ambient')) :
    w' = w ∧ ambient' = ambient ∧ ∃ d, w.dev = some d ∧ d.rxSkbs[i]? = some p :=
  Packets.getRxSkb_current i w w' p ambient ambient' hr

/-- A retained cursor slot 26 makes the actual dump-done callback release the
live replacement peer, allocation identity 55 with one reference, while its
configured peer list and public-key hash still retain slot 26. This is a
retargeted reference to a new identity; the original identity does not return.
The historical explicit-record runner replay established the replacement path
before c047e64; the current runner rejects deletion while that dump is pending. -/
theorem stale_cursor_retargets_replacement :
    CursorWitness.before = some (55, 1, false) ∧
    CursorWitness.afterDone = some (none, [26], [26]) := by
  decide

/-- After an actual TX free, no successful sequence of the eight original
packet primitives can make a later original getter at that slot succeed.
This statement covers one device epoch, without assuming TX/RX disjointness. -/
theorem packet_tx_free_prevents_later_lookup (i : SkbId) (w v u out : WGWorld) (p : DataPacket)
    (ambient afterFree afterSequence afterGet : Ambient)
    (hi : Packets.Inv w) (hf : ((freeTxSkb i).run w).run ambient = .ok (((), v), afterFree))
    (hs : Packets.Sequence v afterFree u afterSequence) :
    ((getTxSkb i).run u).run afterSequence ≠ .ok ((p, out), afterGet) :=
  Packets.freedTx_unreadable i w v u out p ambient afterFree afterSequence afterGet hi hf hs

/-- After an actual RX free, no successful sequence of the eight original
packet primitives can make a later original getter at that slot succeed.
This statement covers one device epoch, without assuming TX/RX disjointness. -/
theorem packet_rx_free_prevents_later_lookup (i : SkbId) (w v u out : WGWorld) (p : RxPacket)
    (ambient afterFree afterSequence afterGet : Ambient)
    (hi : Packets.Inv w) (hf : ((freeRxSkb i).run w).run ambient = .ok (((), v), afterFree))
    (hs : Packets.Sequence v afterFree u afterSequence) :
    ((getRxSkb i).run u).run afterSequence ≠ .ok ((p, out), afterGet) :=
  Packets.freedRx_unreadable i w v u out p ambient afterFree afterSequence afterGet hi hf hs

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

/-- Every successful actual keypair lookup returns the object currently stored at its slot, with
its current allocation identity, and leaves the WG and Ambient state intact. -/
theorem keypair_lookup_current (i : KeypairId) (w w' : WGWorld)
    (ambient ambient' : Ambient) (k : Keypair)
    (hr : ((getKeypair i).run w).run ambient = .ok ((k, w'), ambient')) :
    w' = w ∧ ambient' = ambient ∧ (Keypairs.snapshot w).slots i = some (Keypairs.cell k) :=
  Keypairs.getKeypair_current i w w' ambient ambient' k hr

/-- A successful original syscall, including its scheduled receive work, never
reintroduces a previously allocated keypair identity absent at the start. -/
theorem keypair_syscall_no_resurrection (call : Syscall) (w w' : World)
    (ret : Int) (history : History) (stamp : Nat)
    (hi : Inv (snapshot w.wg) history) (hb : stamp ≤ (snapshot w.wg).frontier)
    (ha : LifetimeAbsent (snapshot w.wg) stamp)
    (hr : (Leanux.syscall call).run w = .ok (ret, w')) :
    LifetimeAbsent (snapshot w'.wg) stamp := by
  obtain ⟨_, _, he⟩ := S3_syscall call w w' ret history hi hr
  exact he.absent_preserved stamp hb ha

/-- The same absence property holds for the original whole operation used by
the runner, including its post-syscall ambient-record consumption. -/
theorem keypair_ambient_no_resurrection (call : Syscall) (w w' : World)
    (ret : Int) (history : History) (stamp : Nat)
    (hi : Inv (snapshot w.wg) history) (hb : stamp ≤ (snapshot w.wg).frontier)
    (ha : LifetimeAbsent (snapshot w.wg) stamp)
    (hr : (syscallWithAmbient call).run w = .ok (ret, w')) :
    LifetimeAbsent (snapshot w'.wg) stamp := by
  obtain ⟨_, _, he⟩ := S3_syscall_ambient call w w' ret history hi hr
  exact he.absent_preserved stamp hb ha

/-- A lookup after a successful original runner operation cannot return an
already released identity, including after any reuse of the queried slot. -/
theorem keypair_lookup_after_release (call : Syscall) (w mid : World)
    (out : WGWorld) (ambientOut : Ambient)
    (ret : Int) (history : History) (stamp i : Nat) (k : Keypair)
    (hi : Inv (snapshot w.wg) history) (hb : stamp ≤ (snapshot w.wg).frontier)
    (ha : LifetimeAbsent (snapshot w.wg) stamp)
    (hr : (syscallWithAmbient call).run w = .ok (ret, mid))
    (hq : ((getKeypair i).run mid.wg).run mid.ambient = .ok ((k, out), ambientOut)) :
    k.internalId ≠ stamp :=
  getKeypair_absent_identity i mid.wg out mid.ambient ambientOut k stamp
    (keypair_ambient_no_resurrection call w mid ret history stamp hi hb ha hr) hq

/-- If an original runner operation fills an empty keypair slot, a later
successful getter at that slot returns an identity newer than the operation's
starting allocation frontier. This states slot reuse directly over the mirror. -/
theorem keypair_ambient_reused_slot_fresh (call : Syscall) (w mid : World)
    (out : WGWorld) (ambientOut : Ambient)
    (ret : Int) (history : History) (i : Nat) (k : Keypair)
    (hi : Inv (snapshot w.wg) history) (he : (snapshot w.wg).slots i = none)
    (hr : (syscallWithAmbient call).run w = .ok (ret, mid))
    (hq : ((getKeypair i).run mid.wg).run mid.ambient = .ok ((k, out), ambientOut)) :
    (snapshot w.wg).frontier < k.internalId := by
  obtain ⟨_, _, hev⟩ := S3_syscall_ambient call w mid ret history hi hr
  exact hev.empty_slot_fresh he
    (getKeypair_current i mid.wg out mid.ambient ambientOut k hq).2.2

/-- Given callback erasure, the mixed receive-enqueue observer has the complete
original result and World, or the exact original error, on every input. -/
theorem enqueue_mixed_access_erasure (irq : PrefixM Lifetimes.LifetimeEvent Unit) (original : Leanux.M Unit)
    (he : ErasesPrefix irq original) (id : SkbId) (state : PacketState) :
    ErasesPrefix (Lifetimes.enqueuePerPeerRxPrefix irq id state)
      (enqueuePerPeerRx original id state) :=
  Lifetimes.enqueuePerPeerRxPrefix_erases he id state

/-- A callback satisfying the same invariant contract gives a safe appended
mixed access prefix on every enqueue outcome and preserves the store invariants
on success. These are identities actually resolved, not raw-reference provenance. -/
theorem enqueue_mixed_access_preserves (irq : PrefixM Lifetimes.LifetimeEvent Unit)
    (hi : PrefixPreserves (fun h w => Lifetimes.MixedInv h w.wg) Lifetimes.LifetimeEvent.Safe irq)
    (id : SkbId) (state : PacketState) :
    PrefixPreserves (fun h w => Lifetimes.MixedInv h w.wg) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.enqueuePerPeerRxPrefix irq id state) :=
  Lifetimes.enqueuePerPeerRxPrefix_preserves hi id state

/-- With the original no-op callback, receive enqueue preserves the mixed
access invariant and retains a safe observation prefix even when it fails. -/
theorem enqueue_mixed_access_pure (id : SkbId) (state : PacketState) :
    PrefixPreserves (fun h w => MixedInv h w.wg) LifetimeEvent.Safe (enqueuePerPeerRxPrefix (pure ()) id state) :=
  Lifetimes.enqueuePerPeerRxPrefix_pure_preserves id state

/-- Keypair lookup failure during enqueue retains exactly the preceding RX
packet read and the prior mixed history, for every input World and callback. -/
theorem enqueue_keypair_failure_prefix (irq : PrefixM LifetimeEvent Unit) (id : SkbId)
    (state : PacketState) (w : World) (h : List LifetimeEvent) (pkt : RxPacket) (e : Stop)
    (hr : ((getRxSkb id).run w.wg).run w.ambient = .ok ((pkt, w.wg), w.ambient))
    (hk : ((getKeypair pkt.keypair).run w.wg).run w.ambient = .error e) :
    runPrefix (enqueuePerPeerRxPrefix irq id state) w h =
      (.error e, h ++ [.packet (.read (.inr id) (packetStamp w.wg id))]) :=
  Lifetimes.enqueuePerPeerRxPrefix_keypair_failure irq id state w h pkt e hr hk

/-- Original peer acquisition emits its read and conditional write in
source order, retaining the exact prefix on refcount failure. -/
theorem peer_acquire_access_exact (id : PeerId) (w : WGWorld) (ambient : Ambient) (h : List Peers.PeerEvent) :
    runStatePrefix (peerGetLocal id) w ambient h = (((peerGet id).run w).run ambient, h ++ peerGetEvents id w) :=
  Lifetimes.peerGetLocal_run id w ambient h

/-- The mixed packet-decryption observer preserves the original complete result and WG and
Ambient state, or exact error, for every input packet and WG and Ambient state. -/
theorem decrypt_packet_access_erasure (pkt : RxPacket) :
    ErasesStatePrefix (decryptPacketPrefix pkt) (decryptPacket pkt) :=
  Lifetimes.decryptPacketPrefix_erases pkt

/-- From the mixed store invariant, packet decryption appends a safe access
prefix on every outcome and preserves that invariant on success. The rejection
update uses the stamp resolved by its fresh second keypair getter. -/
theorem decrypt_packet_access_preserves (pkt : RxPacket) :
    StatePrefixPreserves (fun h w _ => MixedInv h w) LifetimeEvent.Safe (decryptPacketPrefix pkt) :=
  Lifetimes.decryptPacketPrefix_preserves pkt

/-- Failure in decryption's access-free rejection expression retains exactly
the first keypair read; no validity write has occurred. -/
theorem decrypt_rejection_failure_prefix (pkt : RxPacket) (w entered : WGWorld) (ambient enteredAmbient : Ambient)
    (h : List LifetimeEvent) (k : Keypair) (e : Stop)
    (hb : ((branch .decNoKeypair false : WG.M Bool).run w).run ambient = .ok ((false, entered), enteredAmbient))
    (hg : ((getKeypair pkt.keypair).run entered).run enteredAmbient = .ok ((k, entered), enteredAmbient))
    (hr : ((decryptKeyReject k).run entered).run enteredAmbient = .error e) :
    runStatePrefix (decryptPacketPrefix pkt) w ambient h =
      (.error e, h ++ [.keypair (.read pkt.keypair k.internalId)]) :=
  Lifetimes.decryptPacketPrefix_reject_failure pkt w entered ambient enteredAmbient h k e hb hg hr

/-- Callback erasure contracts give all-input erasure for one original decrypt
worker iteration, including its enqueue, softirq, IRQ and rescheduling calls. -/
theorem decrypt_iteration_access_erasure (softirq irq : PrefixM Lifetimes.LifetimeEvent Unit)
    (resched : PrefixM Lifetimes.LifetimeEvent Bool) (originalSoftirq originalIrq : Leanux.M Unit)
    (originalResched : Leanux.M Bool) (hs : ErasesPrefix softirq originalSoftirq)
    (hi : ErasesPrefix irq originalIrq) (hr : ErasesPrefix resched originalResched) :
    ErasesPrefix (Lifetimes.decryptIterPrefix softirq irq resched)
      (decryptIter originalSoftirq originalIrq originalResched) :=
  Lifetimes.decryptIterPrefix_erases hs hi hr

/-- If each callback preserves the mixed access invariant, one decrypt worker
iteration retains a safe appended prefix even on failure. No identity-equality
frame across callbacks or whole-run scheduler coverage is assumed. -/
theorem decrypt_iteration_access_preserves (softirq irq : PrefixM Lifetimes.LifetimeEvent Unit)
    (resched : PrefixM Lifetimes.LifetimeEvent Bool)
    (hs : PrefixPreserves (fun h w => Lifetimes.MixedInv h w.wg) Lifetimes.LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves (fun h w => Lifetimes.MixedInv h w.wg) Lifetimes.LifetimeEvent.Safe irq)
    (hr : PrefixPreserves (fun h w => Lifetimes.MixedInv h w.wg) Lifetimes.LifetimeEvent.Safe resched) :
    PrefixPreserves (fun h w => Lifetimes.MixedInv h w.wg) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.decryptIterPrefix softirq irq resched) :=
  Lifetimes.decryptIterPrefix_preserves hs hi hr

/-- Finite sequences of complete keypairGet/keypairPut, freeTxSkb/freeRxSkb
and keypairsClear calls erase to the original outcome and first Stop. The
sequence API discards keypairGet's optional result; the helper equation below
retains it. No arbitrary caller or scheduler coverage is claimed. -/
theorem release_call_sequence_erasure (cs : List ReleaseCall) : ErasesStatePrefix (Lifetimes.ReleaseCall.observe cs) (Lifetimes.ReleaseCall.execute cs) :=
  Lifetimes.ReleaseCall.observe_erases cs

/-- Every outcome of this release-only family retains a safe appended mixed
history. Successful outcomes also preserve released-identity absence and
resident uniqueness. ReleaseInv adds keypair and cross-TX/RX uniqueness to
MixedInv; it assumes no allocation frontier and makes no allocation or device
lifecycle claim. -/
theorem release_call_sequence_preserves (cs : List ReleaseCall) :
    StatePrefixPreserves (fun h w _ => ReleaseInv h w) LifetimeEvent.Safe (Lifetimes.ReleaseCall.observe cs) :=
  Lifetimes.ReleaseCall.observe_preserves cs

/-- Keypair acquisition's exact result and observations on every input:
null/missing has no resolved access; zero and overflow retain only the read;
a successful increment also records the write. -/
theorem keypair_get_access_observation (kp : Option KeypairId) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (keypairGetPrefix kp) w ambient h = (((keypairGet kp).run w).run ambient, h ++ keypairGetEvents kp w) :=
  Lifetimes.keypairGetPrefix_run kp w ambient h

/-- Keypair put observes the current owner word at each actual unhash. NULL
may Stop before a write or release; the equation includes every failing prefix. -/
theorem keypair_put_access_observation (kp : Option KeypairId) (now : Bool) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (keypairPutPrefix kp now) w ambient h = (((keypairPut kp now).run w).run ambient, h ++ keypairPutEvents kp now w) :=
  Lifetimes.keypairPutPrefix_run kp now w ambient h

/-- A zero-count put retains the source-order prefix, including an earlier
NULL Stop when immediate unhashing is requested. Neither arm releases. -/
theorem keypair_zero_refcount_failure_prefix (id : KeypairId) (now : Bool)
    (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) (d : Device) (k : Keypair)
    (hd : w.dev = some d) (hk : d.keypairs[id]? = some k) (hz : k.refcount = 0) :
    runStatePrefix (keypairPutPrefix (some id) now) w ambient h =
      (if now && k.peer.isNone then
        (.error (.outsideDomain
          s!"{Decision.keypairPutUnreferenceNow.info.file}:{Decision.keypairPutUnreferenceNow.info.line}"
          "entry->peer is NULL: the C dereferences it"),
          h ++ [.keypair (.read id k.internalId), .keypair (.read id k.internalId)])
      else
        (.error (.outsideDomain
          s!"{Decision.refcountSubNonpositive.info.file}:{Decision.refcountSubNonpositive.info.line}"
          "refcount_warn_saturate (use after free)"),
          h ++ ([.keypair (.read id k.internalId)] ++
            (if now then [.keypair (.read id k.internalId)] else []) ++
            [.keypair (.write id k.internalId)]))) :=
  Lifetimes.keypairPutPrefix_zero_failure id now w ambient h d k hd hk hz

/-- TX free records its successful getter before the epoch-tagged release.
An unsuccessful getter records neither access nor release. -/
theorem free_tx_access_observation (id : SkbId) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (freeTxSkbPrefix id) w ambient h = match ((getTxSkb id).run w).run ambient with
      | .error e => (.error e, h)
      | .ok (_, _) => (((freeTxSkb id).run w).run ambient,
          h ++ [.packet (.read (.inl id) (packetStamp w id)),
                .packet (.release (.inl id) (packetStamp w id))]) :=
  Lifetimes.freeTxSkbPrefix_run id w ambient h

/-- RX free has the same getter-before-release order and preserves the
original failure when its packet is absent. -/
theorem free_rx_access_observation (id : SkbId) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (freeRxSkbPrefix id) w ambient h = match ((getRxSkb id).run w).run ambient with
      | .error e => (.error e, h)
      | .ok (_, _) => (((freeRxSkb id).run w).run ambient,
          h ++ [.packet (.read (.inr id) (packetStamp w id)),
                .packet (.release (.inr id) (packetStamp w id))]) :=
  Lifetimes.freeRxSkbPrefix_run id w ambient h

/-- Receive enqueue supports callbacks preserving the stronger release
invariant. Every outcome retains a safe prefix; success preserves uniqueness
and released-identity absence. The callback may change resident identities. -/
theorem enqueue_release_access_preserves (irq : PrefixM Lifetimes.LifetimeEvent Unit)
    (hi : PrefixPreserves (fun h w => Lifetimes.ReleaseInv h w.wg) Lifetimes.LifetimeEvent.Safe irq)
    (id : SkbId) (state : PacketState) :
    PrefixPreserves (fun h w => Lifetimes.ReleaseInv h w.wg) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.enqueuePerPeerRxPrefix irq id state) :=
  Lifetimes.enqueuePerPeerRxPrefix_release hi id state

/-- One original decrypt iteration supports softirq, IRQ, and rescheduling
observers preserving ReleaseInv. It retains safe failed prefixes and preserves
the stronger invariant on success. Concrete callback coverage, allocation,
device lifecycle, and whole scheduler closure remain separate obligations. -/
theorem decrypt_iteration_release_access_preserves (softirq irq : PrefixM Lifetimes.LifetimeEvent Unit)
    (resched : PrefixM Lifetimes.LifetimeEvent Bool)
    (hs : PrefixPreserves (fun h w => Lifetimes.ReleaseInv h w.wg) Lifetimes.LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves (fun h w => Lifetimes.ReleaseInv h w.wg) Lifetimes.LifetimeEvent.Safe irq)
    (hr : PrefixPreserves (fun h w => Lifetimes.ReleaseInv h w.wg) Lifetimes.LifetimeEvent.Safe resched) :
    PrefixPreserves (fun h w => Lifetimes.ReleaseInv h w.wg) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.decryptIterPrefix softirq irq resched) :=
  Lifetimes.decryptIterPrefix_release hs hi hr

/-- Complete keypair creation, including hidden-input failures and ordinary
allocation refusal, erases to the original outcome and complete final WG and Ambient state. -/
theorem keypair_allocation_access_erasure (pid : Option PeerId) :
    ErasesStatePrefix (keypairCreatePrefix pid) (keypairCreate pid) :=
  Lifetimes.keypairCreatePrefix_erases pid

/-- Complete keypair creation retains safe failure prefixes and preserves the
allocation invariant on success. No caller, lifecycle, or scheduler closure is
assumed from this helper theorem. -/
theorem keypair_allocation_access_preserves (pid : Option PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (keypairCreatePrefix pid) :=
  Lifetimes.keypairCreatePrefix_preserves pid

/-- A successful insertion records allocation then initialization write. Failed
creation and normal memory refusal retain the incoming history exactly. -/
theorem keypair_allocation_access_observation (pid : Option PeerId) (w : WGWorld)
    (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (keypairCreatePrefix pid) w ambient h =
      match ((keypairCreate pid).run w).run ambient with
      | .error e => (.error e, h)
      | .ok ((none, v), ambient') => (.ok ((none, v), ambient'), h)
      | .ok ((some id, v), ambient') => (.ok ((some id, v), ambient'), h ++
          [.keypair (.allocate id (w.keypairCounter + 1)),
           .keypair (.write id (w.keypairCounter + 1))]) :=
  Lifetimes.keypairCreatePrefix_observation pid w ambient h

/-- The two constructors name exactly newTxSkb and newRxSkb, with their real
packet argument. Their observer preserves every original outcome. -/
theorem packet_allocation_access_erasure (a : PacketAllocation) : ErasesStatePrefix a.observed a.original :=
  Lifetimes.PacketAllocation.erases a

/-- Both original packet allocators preserve the allocation bounds and tagged
lifetime invariant. This is a helper contract, not device lifecycle closure. -/
theorem packet_allocation_access_preserves (a : PacketAllocation) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe a.observed :=
  Lifetimes.PacketAllocation.preserves a

/-- Packet allocation has no resolved read. Successful creation records the
epoch-tagged allocation and initializing write; failure records neither.
All-input equations do not assume vacant destinations; the preservation theorem
requires AllocationInv, which supplies vacancy. -/
theorem packet_allocation_access_observation (a : PacketAllocation) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix a.observed w ambient h = match (a.original.run w).run ambient with
      | .error e => (.error e, h)
      | .ok ((id, v), ambient') => (.ok ((id, v), ambient'), h ++
          [.packet (.allocate (a.slot id) (packetStamp w id)),
           .packet (.write (a.slot id) (packetStamp w id))]) :=
  Lifetimes.PacketAllocation.observation a w ambient h

/-- The stronger invariant makes all four allocator destination slots vacant.
Peer lifetime bounds alone would not imply the peer slot fact. -/
theorem allocation_destinations_vacant (w : WGWorld) (d : Device)
    (h : List Lifetimes.LifetimeEvent) (hi : Lifetimes.AllocationInv h w)
    (hd : w.dev = some d) :
    d.peers[d.nextPeer]? = none ∧ d.keypairs[d.nextKeypairId]? = none ∧
    d.txSkbs[d.nextSkb]? = none ∧ d.rxSkbs[d.nextSkb]? = none :=
  ⟨hi.peer_vacant hd, hi.key_vacant hd, hi.packet_vacant hd⟩

/-- The native WG portion of every original runner fixture starts with the
allocation invariant. The premise observes the original seven WG store fields;
flags belonging to other subsystem initializers do not restrict this claim. -/
theorem allocation_initial_fixture (net bare : Bool) (w : WGWorld)
    (hw : wgStoreView w = wgStoreView (Runner.initialWG net bare)) :
    Lifetimes.AllocationInv [] w :=
  Lifetimes.allocation_initial net bare w hw


/-- The actual peer reference helpers retain allocation frontiers and released
stamp bounds, as well as safe history. This does not cover peer creation or
bulk device destruction. -/
theorem peer_reference_allocation_preserves (id : PeerId) :
    StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.peerGetMixed id) ∧
    StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.peerPutMixed (some id)) :=
  ⟨Lifetimes.peerGetMixed_allocation id, Lifetimes.peerPutMixed_allocation (some id)⟩

/-- Finite sequences of the five original acquire/put/free/clear calls preserve
AllocationInv on success and retain safe histories on every outcome. The
existing exact erasure and event equations still apply, including refcount
failures after writes. Allocation and lifecycle callers are separate families. -/
theorem release_family_allocation_preserves (cs : List ReleaseCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (Lifetimes.ReleaseCall.observe cs) :=
  Lifetimes.ReleaseCall.observe_preserves_allocation cs

/-- Receive enqueue carries allocation metadata and history bounds through a
callback that itself preserves AllocationInv. No identity-equality premise is
imposed on the callback. -/
theorem enqueue_allocation_access_preserves (irq : PrefixM Lifetimes.LifetimeEvent Unit)
    (hi : PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe irq)
    (id : SkbId) (state : PacketState) :
    PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.enqueuePerPeerRxPrefix irq id state) :=
  Lifetimes.enqueuePerPeerRxPrefix_allocation hi id state

/-- Complete packet decryption preserves the allocation-aware invariant and
retains safe error prefixes. Its observation and erasure definitions are the
same as in the earlier mixed-access result. -/
theorem decrypt_packet_allocation_access_preserves (pkt : RxPacket) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (decryptPacketPrefix pkt) :=
  Lifetimes.decryptPacketPrefix_allocation pkt

/-- One decrypt iteration carries AllocationInv through explicitly contracted
callbacks. Concrete callback coverage, device epochs across destruction and
creation, and whole-scheduler closure remain separate obligations. -/
theorem decrypt_iteration_allocation_access_preserves (softirq irq : PrefixM Lifetimes.LifetimeEvent Unit)
    (resched : PrefixM Lifetimes.LifetimeEvent Bool)
    (hs : PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe irq)
    (hr : PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe resched) :
    PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.decryptIterPrefix softirq irq resched) :=
  Lifetimes.decryptIterPrefix_allocation hs hi hr

/-- Both complete original rotation calls preserve their exact outcomes and
WG and Ambient states after observations are erased. Scalar keypair slots may alias. -/
theorem keypair_rotation_access_erasure (pid : PeerId) (kp : KeypairId) :
    ErasesStatePrefix (Lifetimes.addNewKeypairPrefix pid kp) (addNewKeypair pid kp) ∧
    ErasesStatePrefix (Lifetimes.receivedWithKeypairPrefix pid kp) (receivedWithKeypair pid kp) :=
  ⟨Lifetimes.addNewKeypairPrefix_erases pid kp, Lifetimes.receivedWithKeypairPrefix_erases pid kp⟩

/-- Rotation and responder confirmation retain safe access prefixes on every
outcome and preserve allocation bounds on success. This does not establish
ownership or validity of scalar keypair references stored in a peer. -/
theorem keypair_rotation_access_preserves (pid : PeerId) (kp : KeypairId) :
    StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.addNewKeypairPrefix pid kp) ∧
    StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.receivedWithKeypairPrefix pid kp) :=
  ⟨Lifetimes.addNewKeypairPrefix_allocation pid kp, Lifetimes.receivedWithKeypairPrefix_allocation pid kp⟩

/-- The complete original beginSession call, including allocation, initialization,
rotation, and scalar index replacement, is recovered on every input WG and Ambient state. -/
theorem begin_session_access_erasure (pid : PeerId) :
    ErasesStatePrefix (beginSessionPrefix pid) (beginSession pid) :=
  Lifetimes.beginSessionPrefix_erases pid

/-- Session creation observes all resolved peer and keypair accesses, retaining
safe prefixes on failure and AllocationInv on success. Caller, scheduler,
device-lifecycle, and scalar-reference integrity remain separate obligations. -/
theorem begin_session_access_preserves (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (beginSessionPrefix pid) :=
  Lifetimes.beginSessionPrefix_allocation pid

/-- A conditional whole-call equation for the actual birthdate-clock failure
path. The consecutive original-run premises determine the retained allocation
and access prefix; this is not a recorded runner reproduction. -/
theorem begin_session_birthdate_failure_prefix (pid : PeerId) (kp : KeypairId)
    (w allocEntry allocated guarded configured clockEntry : WGWorld)
    (ambient allocAmbient allocatedAmbient guardedAmbient configuredAmbient clockAmbient : Ambient)
    (h : List LifetimeEvent) (before current : Peer) (k : Keypair)
    (selected : Bool) (e : Stop)
    (hbefore : ((getPeer pid).run w).run ambient = .ok ((before, w), ambient))
    (hstate : ((MonadLift.monadLift (sessionStateRejected before.handshakeState) : WG.M Bool).run w).run ambient =
      .ok ((false, allocEntry), allocAmbient))
    (hcreate : ((keypairCreate before.handshakeEntryPeer).run allocEntry).run allocAmbient =
      .ok ((some kp, allocated), allocatedAmbient))
    (hguard : ((branch .sessionNoKeypair (Option.isNone (some kp)) : WG.M Bool).run allocated).run allocatedAmbient =
      .ok ((false, guarded), guardedAmbient))
    (hpeer : ((getPeer pid).run guarded).run guardedAmbient = .ok ((current, guarded), guardedAmbient))
    (hkey : ((getKeypair kp).run guarded).run guardedAmbient = .ok ((k, guarded), guardedAmbient))
    (hwrite : ((setKeypair kp {k with iAmTheInitiator := before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE, remoteIndex := current.remoteIndex}).run guarded).run guardedAmbient = .ok (((), configured), configuredAmbient))
    (hselect : ((branch .sessionInitiator (before.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) : WG.M Bool).run configured).run configuredAmbient =
      .ok ((selected, clockEntry), clockAmbient))
    (hclock : ((hiddenClock64 .deriveKeysBirthdate : WG.M Int64).run clockEntry).run clockAmbient = .error e) :
    runStatePrefix (beginSessionPrefix pid) w ambient h =
      (.error e, h ++ [.peer (.read pid before.internalId), .peer (.read pid before.internalId),
        .keypair (.allocate kp (allocEntry.keypairCounter + 1)),
        .keypair (.write kp (allocEntry.keypairCounter + 1)),
        .peer (.read pid current.internalId), .keypair (.read kp k.internalId),
        .keypair (.write kp k.internalId)]) :=
  Lifetimes.beginSessionPrefix_clock_failure pid kp w allocEntry allocated guarded configured clockEntry ambient allocAmbient allocatedAmbient guardedAmbient configuredAmbient clockAmbient h before current k selected e hbefore hstate hcreate hguard hpeer hkey hwrite hselect hclock


/-- Focusing the existing complete peer-creation observer into the mixed
history preserves the exact original result, Stop, and successful WG and Ambient state for
all inputs. The event stream comes from the existing complete peer observer. -/
theorem peer_create_mixed_access_erasure (key : Key) (psk : Option Key) :
    ErasesStatePrefix (peerCreateMixed key psk) (peerCreate key psk) :=
  Lifetimes.peerCreateMixed_erases key psk

/-- Complete peer creation retains safe mixed histories on failure and
preserves AllocationInv on success. The slot bound supplies vacancy in this
safety domain; no lifecycle or scalar-reference ownership claim is made. -/
theorem peer_create_allocation_access_preserves (key : Key) (psk : Option Key) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (peerCreateMixed key psk) :=
  Lifetimes.peerCreateMixed_preserves key psk

/-- Original successful execution preserves other-family residents and
allocation metadata except nextPeer. A created ID is the old nextPeer, whose
final value advances to ID+1; ordinary refusal leaves the metadata unchanged.
This exact geometry does not itself assume a vacant destination. -/
theorem peer_create_allocation_geometry (key : Key) (psk : Option Key) (w v : WGWorld)
    (result : Except Int PeerId) (ambient ambient' : Ambient)
    (hr : ((peerCreate key psk).run w).run ambient = .ok ((result, v), ambient')) :
    PeerCreationGeometry w result v :=
  Lifetimes.peerCreate_geometry key psk w v result ambient ambient' hr

/-- A conditional whole-call equation: the first initializer's clock failure
retains the allocation and initial peer write. Premises execute the original
prelude; this is not a recorded runner reproduction. -/
theorem peer_create_cache_clock_failure_prefix (key : Key) (psk : Option Key)
    (w guarded allocated reserved entry : WGWorld) (d : Device)
    (ambient guardedAmbient allocatedAmbient reservedAmbient entryAmbient : Ambient)
    (h : List LifetimeEvent) (e : Stop)
    (hdev : ((getDev).run w).run ambient = .ok ((d, w), ambient))
    (hfull : ((branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE)
      d.numPeers MAX_PEERS_PER_DEVICE : WG.M Bool).run w).run ambient =
        .ok ((false, guarded), guardedAmbient))
    (halloc : ((hiddenAlloc .kmemCacheZallocPeer : WG.M Bool).run guarded).run guardedAmbient =
      .ok ((true, allocated), allocatedAmbient))
    (hmem : ((branch .peerCreateNoMem false : WG.M Bool).run allocated).run allocatedAmbient =
      .ok ((false, reserved), reservedAmbient))
    (hcache : ((branch .peerCreateDstCacheFail false : WG.M Bool).run reserved).run reservedAmbient =
      .ok ((false, entry), entryAmbient))
    (ha : entryAmbient.armRecords = true) (hc : entry.dstCacheRecords = true)
    (hclock : ((hiddenJiffies .dstCacheResetTs : WG.M UInt64).run
      (Peers.creationCoreWorld entry d.nextPeer key)).run entryAmbient = .error e) :
    runStatePrefix (peerCreateMixed key psk) w ambient h =
      (.error e, h ++ [.peer (.allocate d.nextPeer (entry.peerCounter + 1)),
        .peer (.write d.nextPeer (entry.peerCounter + 1))]) :=
  Lifetimes.peerCreateMixed_cache_clock_failure key psk w guarded allocated reserved entry d ambient guardedAmbient allocatedAmbient reservedAmbient entryAmbient h e hdev hfull halloc hmem hcache ha hc hclock

/-- Complete optional-peer acquisition and scalar index/public-key lookup
recover the original result, Stop, and successful WG and Ambient state on every input.
Index lookup stops at the first equal index even when its kind is rejected. -/
theorem receive_lookup_access_erasure (peer : Option PeerId) (kinds : List IndexKind)
    (index : Nat) (key : Key) :
    ErasesStatePrefix (Lifetimes.peerGetMaybeZeroPrefix peer) (peerGetMaybeZero peer) ∧
    ErasesStatePrefix (Lifetimes.indexLookupPrefix kinds index) (indexLookup kinds index) ∧
    ErasesStatePrefix (Lifetimes.pubkeyLookupPrefix key) (pubkeyLookup key) :=
  ⟨Lifetimes.peerGetMaybeZeroPrefix_erases peer,
    Lifetimes.indexLookupPrefix_erases kinds index, Lifetimes.pubkeyLookupPrefix_erases key⟩

/-- Lookup retains safe resolved-store access prefixes on every outcome and
preserves AllocationInv on success. No scalar-index consistency or ownership
premise is required or established. -/
theorem receive_lookup_allocation_access_preserves (peer : Option PeerId)
    (kinds : List IndexKind) (index : Nat) (key : Key) :
    StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.peerGetMaybeZeroPrefix peer) ∧
    StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.indexLookupPrefix kinds index) ∧
    StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.pubkeyLookupPrefix key) :=
  ⟨Lifetimes.AmbientContracts.drop
      (Lifetimes.peerGetMaybeZeroPrefix_spec_ambient Lifetimes.allocationAmbient (fun _ => True) peer),
    Lifetimes.indexLookupPrefix_preserves_ambient Lifetimes.allocationAmbient kinds index,
    Lifetimes.pubkeyLookupPrefix_preserves_ambient Lifetimes.allocationAmbient key⟩

/-- Complete device/peer receive enqueue and consumeData preserve the original
outcomes and successful WG and Ambient states after erasure. This includes the ENOSPC
reference releases and packet free, and the EPIPE dead-packet enqueue with its
original pure callback. -/
theorem receive_entry_access_erasure (id : SkbId) (msg : List UInt8)
    (src : SkbSource) (ds : Nat) :
    ErasesStatePrefix (Lifetimes.enqueuePerDeviceAndPeerRxPrefix id) (enqueuePerDeviceAndPeerRx id) ∧
    ErasesStatePrefix (Lifetimes.consumeDataPrefix msg src ds) (consumeData msg src ds) :=
  ⟨Lifetimes.enqueuePerDeviceAndPeerRxPrefix_erases id,
    Lifetimes.consumeDataPrefix_erases msg src ds⟩

/-- Both complete receive-entry calls retain safe access histories on failure
and AllocationInv on success. This is resolved-store lifetime safety, not
packet delivery, reference ownership, lifecycle, or whole-scheduler closure. -/
theorem receive_entry_allocation_access_preserves (id : SkbId) (msg : List UInt8)
    (src : SkbSource) (ds : Nat) :
    StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.enqueuePerDeviceAndPeerRxPrefix id) ∧
    StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.consumeDataPrefix msg src ds) :=
  ⟨Lifetimes.enqueuePerDeviceAndPeerRxPrefix_allocation id,
    Lifetimes.consumeDataPrefix_allocation msg src ds⟩

/-- A conditional whole-call equation for device-work queue-record failure:
the original-run premises, including the setter's nested getter, determine
five retained accesses. This is not a recorded runner reproduction. -/
theorem receive_enqueue_queue_failure_prefix (id : SkbId)
    (w marked checked queued selected cpuSet queueEntry : WGWorld)
    (ambient markedAmbient checkedAmbient queuedAmbient selectedAmbient cpuSetAmbient queueAmbient : Ambient)
    (h : List LifetimeEvent) (initial pkt : RxPacket) (p : Peer) (d : Device)
    (cpu : Int) (e : Stop)
    (hfirst : ((getRxSkb id).run w).run ambient = .ok ((initial, w), ambient))
    (hmark : ((setRxSkb id fun p => {p with state := .uncrypted}).run w).run ambient =
      .ok (((), marked), markedAmbient))
    (hpacket : ((getRxSkb id).run marked).run markedAmbient = .ok ((pkt, marked), markedAmbient))
    (hpeer : ((getPeer pkt.peer).run marked).run markedAmbient = .ok ((p, marked), markedAmbient))
    (hfull : ((branch .enqueuePeerQueueFull (p.rxQueue.count ≥ MAX_QUEUED_PACKETS) : WG.M Bool).run marked).run markedAmbient =
      .ok ((false, checked), checkedAmbient))
    (hwrite : ((setPeer pkt.peer {p with rxQueue := p.rxQueue.enqueue id}).run checked).run checkedAmbient =
      .ok (((), queued), queuedAmbient))
    (hdev : (getDev.run queued).run queuedAmbient = .ok ((d, queued), queuedAmbient))
    (hcpu : ((cpumaskNextOnlineFrom d.decryptLastCpu).run queued).run queuedAmbient =
      .ok ((cpu, selected), selectedAmbient))
    (hset : ((modifyDev fun d => {d with decryptLastCpu := cpu}).run selected).run selectedAmbient =
      .ok (((), cpuSet), cpuSetAmbient))
    (hring : ((branch .enqueueRingFull d.decryptQueue.full : WG.M Bool).run cpuSet).run cpuSetAmbient =
      .ok ((false, queueEntry), queueAmbient))
    (hqueue : ((queueDeviceWork .decryptWorker : WG.M Unit).run queueEntry).run queueAmbient = .error e) :
    runStatePrefix (enqueuePerDeviceAndPeerRxPrefix id) w ambient h =
      (.error e, h ++ [.packet (.read (.inr id) (packetStamp w id)),
        .packet (.write (.inr id) (packetStamp w id)),
        .packet (.read (.inr id) (packetStamp marked id)),
        .peer (.read pkt.peer p.internalId), .peer (.write pkt.peer p.internalId)]) :=
  Lifetimes.enqueuePerDeviceAndPeerRxPrefix_queue_failure id w marked checked queued selected cpuSet queueEntry ambient markedAmbient checkedAmbient queuedAmbient selectedAmbient cpuSetAmbient queueAmbient h initial pkt p d cpu e hfirst hmark hpacket hpeer hfull hwrite hdev hcpu hset hring hqueue

/-- Every call in the receive-maintenance family erases to its original
result, Stop, and successful WG and Ambient state on all inputs, retaining Boolean results
for the timer guard and modifier. This does not execute queued workers. -/
theorem receive_maintenance_access_erasure (call : MaintenanceCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.MaintenanceCall.erases call

/-- Generic resolved-access safety requires an explicit frame for appending
the send-work queue. The ambient contract may include allocation frontiers
and released identities; no time bound or scheduler closure is asserted. -/
theorem receive_maintenance_ambient_access_preserves (c : ProductAmbientContracts I)
    (hq : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))))
    (call : MaintenanceCall) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.MaintenanceCall.preserves_product c hq call

/-- Complete endpoint/cache, timer, queued-handshake and receive-key-refresh
calls retain safe access histories on every outcome and AllocationInv on
success. The concrete queue frame is discharged over the original update. -/
theorem receive_maintenance_allocation_access_preserves (call : MaintenanceCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.MaintenanceCall.allocation call

/-- Conditional whole-call failure equation: a handshake-completion clock
Stop retains the two preceding peer reads and writes. Premises name only
consecutive original executions, not an observed history or invariant. -/
theorem receive_maintenance_clock_failure_prefix (pid : PeerId) (site : HiddenSite)
    (w afterDelete clockEntry : WGWorld) (ambient : Ambient)
    (p q : Peer) (h : List LifetimeEvent) (e : Stop)
    (hp : ((getPeer pid).run w).run ambient = .ok ((p, w), ambient))
    (hdel : ((setPeer pid (p.setTimer .retransmitHandshake none)).run w).run ambient = .ok (((), afterDelete), ambient))
    (hq : ((getPeer pid).run afterDelete).run ambient = .ok ((q, afterDelete), ambient))
    (hreset : ((setPeer pid {q with timerHandshakeAttempts := 0, sentLastminuteHandshake := false}).run afterDelete).run ambient = .ok (((), clockEntry), ambient))
    (hclock : (((hidden site : WG.M (List UInt8))).run clockEntry).run ambient = .error e) :
    runStatePrefix (timersHandshakeCompletePrefix pid site) w ambient h =
      (.error e, h ++ [.peer (.read pid p.internalId), .peer (.write pid p.internalId),
        .peer (.read pid q.internalId), .peer (.write pid q.internalId)]) :=
  Lifetimes.timersHandshakeCompletePrefix_clock_failure pid site w afterDelete clockEntry ambient p q h e hp hdel hq hreset hclock


/-- All seven TX staging-family observers erase to the original result,
Stop, and complete successful WG and Ambient state on every input. CPU selection and device
enqueue retain their Nat and Int results. Queued workers are not executed. -/
theorem tx_staging_access_erasure (call : TxStagingCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.TxStagingCall.erases call

/-- Generic resolved-store access safety for the complete staging family,
with explicit TX allocation/release and scalar device-update contracts.
Cached identity predicates are preserved where the original writes require them. -/
theorem tx_staging_ambient_access_preserves (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (call : TxStagingCall) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.TxStagingCall.preserves_product c t call

/-- The concrete AllocationInv instance retains safe histories on every
outcome and allocation bounds on success. No distinct-packet-ID, ownership,
queue-coherence, delivery, or whole-scheduler premise or conclusion is added. -/
theorem tx_staging_allocation_access_preserves (call : TxStagingCall) : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.TxStagingCall.allocation call

/-- The original TX setter reads its resident before writing. A failing
getter emits nothing; successful resolution emits the read and write in order. -/
theorem tx_setter_exact_observation (id : SkbId) (f : DataPacket → DataPacket)
    (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (setTxSkbPrefix id f) w ambient h = match ((getTxSkb id).run w).run ambient with
      | .error e => (.error e, h)
      | .ok _ => (((setTxSkb id f).run w).run ambient,
          h ++ [.packet (.read (.inl id) (packetStamp w id)),
                .packet (.write (.inl id) (packetStamp w id))]) :=
  Lifetimes.setTxSkbPrefix_run id f w ambient h

/-- Conditional whole-call equation for a keepalive allocation-record Stop:
the initial peer read remains in the history. Premises describe original
operations; this is not a recorded runner reproduction or normal refusal. -/
theorem tx_keepalive_allocation_failure_prefix (pid : PeerId) (w checked : WGWorld) (ambient checkedAmbient : Ambient) (p : Peer)
    (h : List LifetimeEvent) (e : Stop)
    (hp : ((getPeer pid).run w).run ambient = .ok ((p, w), ambient))
    (hb : ((branch .keepaliveStagedEmpty p.staged.isEmpty : WG.M Bool).run w).run ambient =
      .ok ((true, checked), checkedAmbient))
    (ha : ((hiddenAlloc .keepaliveSkb : WG.M Bool).run checked).run checkedAmbient = .error e) :
    runStatePrefix (sendKeepalivePrefix pid) w ambient h =
      (.error e, h ++ [.peer (.read pid p.internalId)]) :=
  Lifetimes.sendKeepalivePrefix_alloc_failure pid w checked ambient checkedAmbient p h e hp hb ha


/-- Counter observation erases to the original validator on every WG and Ambient state,
including malformed bitmaps and early rejections. -/
theorem counter_validate_access_erasure (kp : KeypairId) (nonce : Nat) :
    ErasesStatePrefix (counterValidatePrefix kp nonce) (counterValidate kp nonce) :=
  Lifetimes.counterValidatePrefix_erases kp nonce

/-- Counter access safety has no 128-word bitmap premise. It includes the
original duplicate-bit rejection path; errors retain safe appended histories. -/
theorem counter_validate_access_preserves (c : Lifetimes.ProductAmbientContracts I)
    (kp : KeypairId) (nonce : Nat) :
    PrefixPreserves I Lifetimes.LifetimeEvent.Safe
      (liftWGObserver (Lifetimes.counterValidatePrefix kp nonce)) :=
  Lifetimes.ProductAmbientContracts.drop
    (Lifetimes.counterValidatePrefix_spec_product c (fun _ => True) kp nonce)

/-- Node search and subsequent peer acquisition erase to the original lookup
without a valid-trie assumption. This is an access contract, not a routing result. -/
theorem allowed_lookup_access_erasure (root : Option NodeId) (bits key : Nat) :
    ErasesStatePrefix (lookupPrefix root bits key) (lookup root bits key) :=
  Lifetimes.lookupPrefix_erases root bits key

/-- The original lookup's resolved peer accesses preserve AllocationInv.
Malformed nodes and missing or dying peers remain admitted error paths. -/
theorem allowed_lookup_allocation_access_preserves (root : Option NodeId) (bits key : Nat) :
    StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.lookupPrefix root bits key) :=
  Lifetimes.AmbientContracts.drop
    (Lifetimes.lookupPrefix_spec Lifetimes.allocationAmbient (fun _ => True) root bits key)

/-- Complete receive completion, including source lookup, maintenance and
staged sending, has exactly the original result, Stop, and successful WG and Ambient state. -/
theorem receive_completion_access_erasure (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    ErasesStatePrefix (consumeDataDonePrefix pid pkt e) (consumeDataDone pid pkt e) :=
  Lifetimes.consumeDataDonePrefix_erases pid pkt e

/-- Receive completion retains safe histories on all outcomes and AllocationInv
on success. Returned bytes do not themselves establish stack delivery. -/
theorem receive_completion_allocation_access_preserves (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.consumeDataDonePrefix pid pkt e) :=
  Lifetimes.consumeDataDonePrefix_preserves_ambient Lifetimes.allocationAmbient
    Lifetimes.allocationTx Lifetimes.allocationRx pid pkt e

/-- The whole original NAPI poll is observed for arbitrary budgets and Worlds,
provided the named stack callback observer erases to its original callback,
including the GRO batch flushes inside the poll and the completion flush. -/
theorem receive_poll_access_erasure (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM LifetimeEvent Unit) (original : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ gro, ErasesPrefix (callback gro) (original gro)) :
    ErasesPrefix (rxPollPrefix pid budget callback) (rxPoll pid budget original) :=
  Lifetimes.rxPollPrefix_erases pid budget callback original hc

/-- All poll prefixes are safe under an explicit AllocationInv-preserving
callback. The final World satisfies AllocationInv on success. This does not
close the actual Stack callback, scheduling, delivery, or order obligations. -/
theorem receive_poll_allocation_access_preserves (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM Lifetimes.LifetimeEvent Unit)
    (hc : ∀ gro, PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe (callback gro)) :
    PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.rxPollPrefix pid budget callback) :=
  Lifetimes.rxPollPrefix_preserves_ambient (Lifetimes.ProductAmbientContracts.ofNative Lifetimes.allocationAmbient)
    (Lifetimes.ProductTxContracts.ofNative Lifetimes.allocationTx)
    ⟨fun len => (Lifetimes.allocationRx.stats len).liftWGObserver,
      fun why => (Lifetimes.allocationRx.dishonest why).liftWGObserver,
      fun id => (Lifetimes.allocationRx.free id).liftWGObserver⟩ pid budget callback hc

/-- A malformed empty bitmap gives an actual invariant Stop after the keypair
read, with no write. Premises describe the original getter and counter value. -/
theorem counter_bitmap_failure_prefix (kp : KeypairId) (w : WGWorld) (ambient : Ambient)
    (k : Keypair) (h : List LifetimeEvent)
    (hg : ((getKeypair kp).run w).run ambient = .ok ((k, w), ambient))
    (hc : k.receivingCounter = ⟨0, #[]⟩) :
    runStatePrefix (counterValidatePrefix kp 0) w ambient h =
      (.error (.invariant "backtrack[0] beyond the bitmap"),
        h ++ [.keypair (.read kp k.internalId)]) :=
  Lifetimes.counterValidatePrefix_empty_bitmap kp w ambient k h hg hc

/-- The saved-map any scan returns the original Boolean and records exactly
its demanded prefix, including the first true entry. This all-input equation
records supplied stamps; current residency is a separate safety premise. -/
theorem saved_peer_scan_observation (test : Peer → Bool) (xs : List (PeerId × Peer)) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (savedPeerAny test xs) w ambient h =
      (.ok ((xs.any (fun x => test x.2), w), ambient), h ++ savedPeerAnyEvents test xs) :=
  Lifetimes.savedPeerAny_run test xs w ambient h

/-- A saved-map scan has a safe appended prefix when every supplied entry's
stamp is still resident. The observer performs no additional getter lookup. -/
theorem saved_peer_scan_safety (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (test : Peer → Bool) (xs : List (PeerId × Peer)) :
    ProductAmbientSpec I (fun s => P s ∧ SavedPeers xs s)
      (liftWGObserver (savedPeerAny test xs)) (fun _ => P) :=
  Lifetimes.savedPeerAny_spec_product c P test xs

/-- Every named cache, endpoint, loopback or socket-send call erases to its
complete original result/WG and Ambient state or exact Stop on arbitrary inputs, including both
IPv4 and IPv6 sends. Socket setup and reinitialization remain separate callers. -/
theorem socket_family_erasure (call : SocketCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.SocketCall.erases call

/-- The complete named Socket calls retain a safe event prefix and carry the
ambient invariant and cached identity predicates on success. Device-statistics
preservation is an explicit extra contract, separate from access coverage. -/
theorem socket_family_ambient_safety (c : ProductAmbientContracts I) (sc : ProductSocketContracts I) (P : IdentityView → Prop)
    (call : SocketCall) : ProductAmbientSpec I P (liftWGObserver call.observed) (fun _ => P) :=
  Lifetimes.SocketCall.spec_product c sc P call

/-- Concrete allocation-bound and resolved-store lifetime safety for each
named Socket call, including failed prefixes. This does not assert reference
ownership, outer-scheduler coverage or packet delivery. -/
theorem socket_family_allocation_safety (call : SocketCall) : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.SocketCall.allocation call

/-- A cache-get refresh-clock Stop follows the peer read and precedes the
cache write. The conditional complete-call equation uses original operation
premises and is not a recorded runner reproduction. -/
theorem socket_cache_clock_failure (pid gen : Nat) (w : WGWorld) (ambient : Ambient) (p : Peer)
    (h : List LifetimeEvent) (e : Stop)
    (ha : ambient.armRecords = true) (hc : w.dstCacheRecords = true)
    (hp : ((getPeer pid).run w).run ambient = .ok ((p, w), ambient)) (hs : p.dstCache.slot = none)
    (hf : ((hiddenJiffies .dstCacheRefreshTs : WG.M UInt64).run w).run ambient = .error e) :
    runStatePrefix (dstCacheGetPrefix pid gen) w ambient h =
      (.error e, h ++ [.peer (.read pid p.internalId)]) :=
  Lifetimes.dstCacheGetPrefix_clock_failure pid gen w ambient p h e ha hc hp hs hf

/-- In the IPv4 source-clear/reset segment, the endpoint read and write
survive a later reset-clock Stop. This uses original operation executions;
it is a conditional segment equation, not an accepted runner witness. -/
theorem socket_ipv4_clear_reset_failure (pid : PeerId) (w v : WGWorld) (ambient ambient' : Ambient) (p : Peer)
    (h : List LifetimeEvent) (err : Stop)
    (hd : w.dev.isSome = true)
    (hp : ((getPeer pid).run w).run ambient = .ok ((p, w), ambient))
    (hw : ((setPeer pid {p with endpoint := p.endpoint.map fun e => {e with src := 0, srcIf := 0}}).run w).run ambient = .ok (((), v), ambient'))
    (ha : ambient'.armRecords = true) (hc : v.dstCacheRecords = true)
    (hf : ((hiddenJiffies .dstCacheResetTs : WG.M UInt64).run v).run ambient' = .error err) :
    runStatePrefix (do send4ClearSrcPrefix (some pid); dstCacheResetMixed pid) w ambient h =
      (.error err, h ++ [.peer (.read pid p.internalId), .peer (.write pid p.internalId)]) :=
  Lifetimes.send4_clear_reset_clock_failure pid w v ambient ambient' p h err hd hp hw ha hc hf

/-- The observed complete wgXmit entry returns the original result, WG and Ambient state or
Stop on every input, including all error and staged-queue paths. -/
theorem transmit_entry_erasure (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    ErasesStatePrefix (wgXmitPrefix family addr pkts mtu) (wgXmit family addr pkts mtu) :=
  Lifetimes.wgXmitPrefix_erases family addr pkts mtu

/-- Transmit entry retains a safe prefix under explicit ambient, staging and
error-statistics contracts. No queue-ownership or routing theorem is assumed. -/
theorem transmit_entry_ambient_safety (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (x : ProductWgXmitContracts I) (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (wgXmitPrefix family addr pkts mtu)) :=
  Lifetimes.wgXmitPrefix_preserves_product c t x family addr pkts mtu

/-- Complete transmit entry has safe resolved-store accesses, including every
failed prefix, and preserves allocation bounds on success. -/
theorem transmit_entry_allocation_safety (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    StatePrefixPreserves (fun h w _ => Lifetimes.AllocationInv h w) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.wgXmitPrefix family addr pkts mtu) :=
  Lifetimes.wgXmitPrefix_preserves Lifetimes.allocationAmbient Lifetimes.allocationTx
    Lifetimes.allocationWgXmit family addr pkts mtu

/-- The actual inner-packet stack observer erases to Env.deliverInner on every
input, retaining the original input exclusions and TCP reply re-entry. -/
theorem actual_stack_erasure (pkt : List UInt8) :
    ErasesPrefix (stackReceivePrefix pkt) (Leanux.Env.deliverInner pkt) :=
  Lifetimes.stackReceivePrefix_erases pkt

/-- The actual stack callback satisfies the ambient lifetime contract, with
TCP replies composed through the complete transmit entry. -/
theorem actual_stack_ambient_safety (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (x : ProductWgXmitContracts I) (pkt : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (stackReceivePrefix pkt) :=
  Lifetimes.stackReceivePrefix_preserves c t x pkt

/-- The actual stack callback has safe failure prefixes and preserves allocation
bounds on success. This states lifetime safety, not successful delivery. -/
theorem actual_stack_allocation_safety (pkt : List UInt8) :
    PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.stackReceivePrefix pkt) :=
  Lifetimes.stackReceivePrefix_preserves (Lifetimes.ProductAmbientContracts.ofNative Lifetimes.allocationAmbient) (Lifetimes.ProductTxContracts.ofNative Lifetimes.allocationTx)
    ⟨fun P => (Lifetimes.allocationWgXmit.errors P).liftWGObserver⟩ pkt

/-- Polling with the actual List.forM deliverInner callback returns the original
result, World or Stop, for any peer, budget and input World. -/
theorem actual_receive_poll_erasure (pid : PeerId) (budget : Nat) :
    ErasesPrefix (rxPollStackPrefix pid budget)
      (rxPoll pid budget (fun pkts => pkts.forM Leanux.Env.deliverInner)) :=
  Lifetimes.rxPollStackPrefix_erases pid budget

/-- Polling and its concrete stack callback compose under the ambient lifetime
contracts; callback behavior is discharged rather than assumed separately. -/
theorem actual_receive_poll_ambient_safety (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (r : ProductRxContracts I) (x : ProductWgXmitContracts I) (pid : PeerId) (budget : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (rxPollStackPrefix pid budget) :=
  Lifetimes.rxPollStackPrefix_preserves c t r x pid budget

/-- Complete receive polling with its actual stack callback has safe failure
prefixes and preserves allocation bounds on success. Surrounding scheduling
and delivery-order obligations remain separate. -/
theorem actual_receive_poll_allocation_safety (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.rxPollStackPrefix pid budget) :=
  Lifetimes.rxPollStackPrefix_preserves (Lifetimes.ProductAmbientContracts.ofNative Lifetimes.allocationAmbient) (Lifetimes.ProductTxContracts.ofNative Lifetimes.allocationTx)
    ⟨fun len => (Lifetimes.allocationRx.stats len).liftWGObserver,
      fun why => (Lifetimes.allocationRx.dishonest why).liftWGObserver,
      fun id => (Lifetimes.allocationRx.free id).liftWGObserver⟩ ⟨fun P => (Lifetimes.allocationWgXmit.errors P).liftWGObserver⟩ pid budget

/-- Packet encryption preserves the complete original result, successful
World and Stop on all inputs, with an explicitly observed checksum callback. -/
theorem encrypt_packet_access_erasure
    (checksum : Packet → PrefixM Lifetimes.LifetimeEvent Packet) (originalChecksum : Packet → Leanux.M Packet)
    (hc : ∀ pkt, ErasesPrefix (checksum pkt) (originalChecksum pkt)) (kp : KeypairId) (pkt : DataPacket) :
    ErasesPrefix (Lifetimes.encryptPacketPrefix checksum kp pkt) (encryptPacket originalChecksum kp pkt) :=
  Lifetimes.encryptPacketPrefix_erases hc kp pkt

/-- Callback preservation suffices for resolved-current-store access safety.
No continued association with the caller's saved keypair ID is asserted. -/
theorem encrypt_packet_ambient_access_preserves (c : Lifetimes.ProductAmbientContracts I)
    (checksum : Packet → PrefixM Lifetimes.LifetimeEvent Packet)
    (hc : ∀ pkt, PrefixPreserves I Lifetimes.LifetimeEvent.Safe (checksum pkt))
    (kp : KeypairId) (pkt : DataPacket) :
    PrefixPreserves I Lifetimes.LifetimeEvent.Safe (Lifetimes.encryptPacketPrefix checksum kp pkt) :=
  Lifetimes.encryptPacketPrefix_preserves_ambient c hc kp pkt

/-- The concrete checksum helper preserves the product World. Projecting that
frame to the original 43-field store observation discharges its callback contract,
including rejected packet inputs and their Stops. -/
theorem encrypt_packet_allocation_access_preserves (kp : KeypairId) (pkt : DataPacket) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe
      (encryptPacketPrefix (fun p => liftPrefix (Leanux.Env.checksumHelp p)) kp pkt) :=
  Lifetimes.encryptPacketPrefix_allocation kp pkt

/-- The original encrypt step replaces the consumed ring before invoking
softirq, retains every packet getter/setter, and enqueues the whole item after a dead break. -/
theorem encrypt_step_access_erasure
    (checksum : Packet → PrefixM Lifetimes.LifetimeEvent Packet) (originalChecksum : Packet → Leanux.M Packet)
    (softirq : PrefixM Lifetimes.LifetimeEvent Unit) (originalSoftirq : Leanux.M Unit)
    (hc : ∀ pkt, ErasesPrefix (checksum pkt) (originalChecksum pkt))
    (hs : ErasesPrefix softirq originalSoftirq) :
    ErasesPrefix (Lifetimes.encryptStepPrefix checksum softirq) (encryptStep originalChecksum originalSoftirq) :=
  Lifetimes.encryptStepPrefix_erases hc hs

/-- Ring replacement has an explicit contract distinct from produce.
Callbacks may change identities; malformed and duplicate item IDs are admitted. -/
theorem encrypt_step_ambient_access_preserves (c : Lifetimes.ProductAmbientContracts I)
    (t : Lifetimes.ProductTxContracts I) (checksum : Packet → PrefixM Lifetimes.LifetimeEvent Packet)
    (softirq : PrefixM Lifetimes.LifetimeEvent Unit)
    (hq : ∀ ring : PtrRing (List SkbId), PrefixPreserves I Lifetimes.LifetimeEvent.Safe
      (liftPrefix (liftWG (modifyDev fun d => {d with encryptQueue := ring}))))
    (hc : ∀ pkt, PrefixPreserves I Lifetimes.LifetimeEvent.Safe (checksum pkt))
    (hs : PrefixPreserves I Lifetimes.LifetimeEvent.Safe softirq) :
    PrefixPreserves I Lifetimes.LifetimeEvent.Safe (Lifetimes.encryptStepPrefix checksum softirq) :=
  Lifetimes.encryptStepPrefix_preserves_ambient c t hq hc hs

/-- Complete encrypt-step safety at AllocationInv, retaining failed prefixes.
Only the explicitly supplied softirq observer remains a callback obligation. -/
theorem encrypt_step_allocation_access_preserves (softirq : PrefixM Lifetimes.LifetimeEvent Unit)
    (hs : PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe softirq) :
    PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.encryptStepPrefix (fun p => liftPrefix (Leanux.Env.checksumHelp p)) softirq) :=
  Lifetimes.encryptStepPrefix_allocation hs

/-- Exact worker iteration includes ended/yielded/continued results and calls
the rescheduling callback only after a true step. Erasure has no validity premise. -/
theorem encrypt_iteration_access_erasure
    (checksum : Packet → PrefixM Lifetimes.LifetimeEvent Packet) (originalChecksum : Packet → Leanux.M Packet)
    (softirq : PrefixM Lifetimes.LifetimeEvent Unit) (originalSoftirq : Leanux.M Unit)
    (needResched : PrefixM Lifetimes.LifetimeEvent Bool) (originalResched : Leanux.M Bool)
    (hc : ∀ pkt, ErasesPrefix (checksum pkt) (originalChecksum pkt))
    (hs : ErasesPrefix softirq originalSoftirq) (hr : ErasesPrefix needResched originalResched) :
    ErasesPrefix (Lifetimes.encryptIterPrefix checksum softirq needResched)
      (encryptIter originalChecksum originalSoftirq originalResched) :=
  Lifetimes.encryptIterPrefix_erases hc hs hr

/-- Explicit callback and ring-replacement contracts compose through the
original iteration, without queue geometry, ownership or batch homogeneity. -/
theorem encrypt_iteration_ambient_access_preserves (c : Lifetimes.ProductAmbientContracts I)
    (t : Lifetimes.ProductTxContracts I) (checksum : Packet → PrefixM Lifetimes.LifetimeEvent Packet)
    (softirq : PrefixM Lifetimes.LifetimeEvent Unit) (needResched : PrefixM Lifetimes.LifetimeEvent Bool)
    (hq : ∀ ring : PtrRing (List SkbId), PrefixPreserves I Lifetimes.LifetimeEvent.Safe
      (liftPrefix (liftWG (modifyDev fun d => {d with encryptQueue := ring}))))
    (hc : ∀ pkt, PrefixPreserves I Lifetimes.LifetimeEvent.Safe (checksum pkt))
    (hs : PrefixPreserves I Lifetimes.LifetimeEvent.Safe softirq)
    (hr : PrefixPreserves I Lifetimes.LifetimeEvent.Safe needResched) :
    PrefixPreserves I Lifetimes.LifetimeEvent.Safe
      (Lifetimes.encryptIterPrefix checksum softirq needResched) :=
  Lifetimes.encryptIterPrefix_preserves_ambient c t hq hc hs hr

/-- The concrete checksum and consumed-ring update preserve AllocationInv;
softirq and rescheduling remain explicit. This is not full scheduler closure. -/
theorem encrypt_iteration_allocation_access_preserves (softirq : PrefixM Lifetimes.LifetimeEvent Unit)
    (needResched : PrefixM Lifetimes.LifetimeEvent Bool)
    (hs : PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe softirq)
    (hr : PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe needResched) :
    PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.encryptIterPrefix (fun p => liftPrefix (Leanux.Env.checksumHelp p)) softirq needResched) :=
  Lifetimes.encryptIterPrefix_allocation hs hr

/-- Five complete TX completion helpers and the complete worker step erase
to their originals on every WG and Ambient state and history, with no validity premise. -/
theorem tx_family_access_erasure (call : TxCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.TxCall.erases call

/-- Explicit ambient, TX and socket contracts compose resolved access safety
through the complete TX family, including failed prefixes and cleanup. -/
theorem tx_family_ambient_access_preserves (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (sc : ProductSocketContracts I) (call : TxCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.TxCall.preserves_product c t sc call

/-- Concrete allocation contracts discharge all TX-family leaves. Duplicate
packet IDs and saved-head references gain no ownership or identity premise. -/
theorem tx_family_allocation_access_preserves (call : TxCall) : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.TxCall.allocation call

/-- The original TX iteration retains ended/yielded/continued results and
invokes rescheduling only after a true, completely cleaned-up worker step. -/
theorem tx_iteration_access_erasure (pid : PeerId)
    (needResched : PrefixM Lifetimes.LifetimeEvent Bool) (originalResched : Leanux.M Bool)
    (hr : ErasesPrefix needResched originalResched) :
    ErasesPrefix (Lifetimes.txIterPrefix pid needResched) (txIter pid originalResched) :=
  Lifetimes.txIterPrefix_erases pid hr

/-- The explicit rescheduling observer may change identities while preserving
the ambient invariant; saved-reference association is not asserted. -/
theorem tx_iteration_ambient_access_preserves (c : Lifetimes.ProductAmbientContracts I)
    (t : Lifetimes.ProductTxContracts I) (sc : Lifetimes.ProductSocketContracts I) (pid : PeerId)
    (needResched : PrefixM Lifetimes.LifetimeEvent Bool)
    (hr : PrefixPreserves I Lifetimes.LifetimeEvent.Safe needResched) :
    PrefixPreserves I Lifetimes.LifetimeEvent.Safe (Lifetimes.txIterPrefix pid needResched) :=
  Lifetimes.txIterPrefix_preserves_ambient c t sc pid hr

/-- Complete TX-iteration safety at AllocationInv, with failure history
retained. The actual outer rescheduling caller remains a separate obligation. -/
theorem tx_iteration_allocation_access_preserves (pid : PeerId)
    (needResched : PrefixM Lifetimes.LifetimeEvent Bool)
    (hr : PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe needResched) :
    PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe
      (Lifetimes.txIterPrefix pid needResched) := Lifetimes.txIterPrefix_allocation pid hr

/-- After the original caller-jiffies read succeeds, an original jitter Stop
retains the preceding peer read and occurs before
the timer guard. These are original-run premises, not a desired-prefix premise
or an accepted-run witness. -/
theorem tx_timer_jitter_failure (pid : PeerId) (w entered clocked : WGWorld) (ambient enteredAmbient clockedAmbient : Ambient) (jc : Option UInt64)
    (p : Peer) (h : List LifetimeEvent) (e : Stop)
    (hp : ((getPeer pid).run w).run ambient = .ok ((p, w), ambient))
    (hb : ((branch .timersDataSentNotPending !(p.timerPending .newHandshake) : WG.M Bool).run w).run ambient = .ok ((true, entered), enteredAmbient))
    (hc : ((callerJiffies .timerJiffiesDataSent).run entered).run enteredAmbient = .ok ((jc, clocked), clockedAmbient))
    (hj : ((jitterBelowRekeyTimeout .newHandshakeJitter).run clocked).run clockedAmbient = .error e) :
    runStatePrefix (timersDataSentPrefix pid) w ambient h = (.error e, h ++ [.peer (.read pid p.internalId)]) :=
  Lifetimes.timersDataSentPrefix_jitter_failure pid w entered clocked ambient enteredAmbient clockedAmbient jc p h e hp hb hc hj


/-- The two Noise constructors, both consumers and MAC addition retain their
original result types and exact WG and Ambient state/Stop behavior for every input/history. -/
theorem handshake_family_access_erasure (call : HandshakeCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.HandshakeCall.erases call

/-- Complete local handshake access prefixes are safe under the ambient
contracts and an explicit original scalar-index-insertion contract. This does
not assert the lookup table's ownership or an outer worker's execution. -/
theorem handshake_family_ambient_access_preserves (c : ProductAmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (liftIndex (indexInsert owner)))))
    (call : HandshakeCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.HandshakeCall.preserves_ambient_product c hi call

/-- The concrete allocation invariant discharges every named handshake leaf,
including index insertion, reference-taking lookups and failure releases.
Normal rejection and later Stops both retain preceding resolved accesses. -/
theorem handshake_family_allocation_access_preserves (call : HandshakeCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.HandshakeCall.allocation call

/-- A failed original cookie-age test retains the earlier MAC1 peer read and
write. Consecutive original-run premises locate this failure; they do not assume
the desired history or claim an accepted runner witness. -/
theorem handshake_mac_clock_failure (pid : PeerId) (msg : List UInt8)
    (w written clockEntry : WGWorld) (ambient writtenAmbient clockAmbient : Ambient)
    (p : Peer) (h : List LifetimeEvent) (e : Stop)
    (hp : ((getPeer pid).run w).run ambient = .ok ((p, w), ambient))
    (hw : ((setPeer pid {p with lastMac1Sent := blake2s 16 p.cookieMac1Key (msg.take (msg.length - 32)), haveSentMac1 := true}).run w).run ambient = .ok (((), written), writtenAmbient))
    (hb : ((branch .addMacCookieValid p.cookieIsValid : WG.M Bool).run written).run writtenAmbient = .ok ((true, clockEntry), clockAmbient))
    (hc : ((branchExpired .addMacCookieFresh p.cookieBirthdate COOKIE_FRESH_SECONDS (!·)).run clockEntry).run clockAmbient = .error e) :
    runStatePrefix (addMacToPacketPrefix pid msg) w ambient h =
      (.error e, h ++ [.peer (.read pid p.internalId), .peer (.write pid p.internalId)]) :=
  Lifetimes.addMacToPacketPrefix_clock_failure pid msg w written clockEntry ambient writtenAmbient clockAmbient p h e hp hw hb hc

/-- The complete buffer send, two timer helpers, initiation, response and send
worker retain their original Unit results, WG and Ambient states and Stops on every input and
history. Buffer allocation refusal occurs before any resolved peer access. -/
theorem handshake_send_family_access_erasure (call : HandshakeSendCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.HandshakeSendCall.erases call

/-- Explicit ambient, socket and primitive index/session contracts compose
safe resolved access prefixes through the six original send calls. A normal
initiation return reaches the worker's put; a Stop skips that later cleanup. -/
theorem handshake_send_family_ambient_access_preserves (c : ProductAmbientContracts I) (sc : ProductSocketContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (liftIndex (indexInsert owner)))))
    (create : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairCreatePrefix pid)))
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now)))
    (replace : ∀ pid kp, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (liftIndex (indexReplaceHandshake pid kp)))))
    (call : HandshakeSendCall) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.HandshakeSendCall.preserves_ambient_product c sc hi create put replace call

/-- Concrete allocation contracts discharge every send-family leaf, including
socket paths, index insertion and session allocation/rotation. This does not
assert ownership of saved scalar references or closure of outer scheduling. -/
theorem handshake_send_family_allocation_access_preserves (call : HandshakeSendCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.HandshakeSendCall.allocation call

/-- The four complete local cookie calls retain their original byte-list,
MAC-state or Unit result, success WG and Ambient state and Stop for every input/history.
Consumption observes the reference-taking lookup, fresh peer reads, write and
final puts; the other three calls are access-free by source inspection. -/
theorem cookie_family_access_erasure (call : CookieCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.CookieCall.erases call

/-- Explicit ambient contracts and stability under cookie-secret and
ratelimiter-table updates compose safe access prefixes. Failed authentication
still reaches the ordinary final put; a preceding Stop skips later cleanup. -/
theorem cookie_family_ambient_access_preserves (c : ProductAmbientContracts I) (hc : ProductCookieStable I)
    (call : CookieCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.CookieCall.preserves_product c hc call

/-- Allocation geometry discharges cookie-state stability and every consume
access/reference contract. No successful authentication, packet shape or
index-owner coherence premise is required. Outer receive workers and ownership
of saved references remain separate obligations. -/
theorem cookie_family_allocation_access_preserves (call : CookieCall) : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.CookieCall.allocation call

/-- Endpoint-from-skb, cookie reply, cookie send, full handshake receive and
queue step preserve every original result, WG and Ambient state and Stop for every history.
Nested normal returns and failed-record prefixes retain source ordering. -/
theorem handshake_receive_family_access_erasure (call : HandshakeReceiveCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.HandshakeReceiveCall.erases call

/-- Explicit ambient and named lower-helper contracts compose the complete
handshake receive family. A false beginSession return still reaches common completion;
queue decrement occurs only after a normal handler return. -/
theorem handshake_receive_family_ambient_access_preserves (c : ProductAmbientContracts I) (r : ProductHandshakeReceiveContracts I)
    (q : ProductReceiveQueueContracts I) (call : HandshakeReceiveCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.HandshakeReceiveCall.preserves_ambient_product c r q call

/-- Allocation geometry discharges socket, cookie, session, staging, statistics
and queue-bookkeeping contracts, including normal rejection and Stop prefixes.
No saved-reference ownership or outer scheduler closure is asserted. -/
theorem handshake_receive_family_allocation_access_preserves (call : HandshakeReceiveCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.HandshakeReceiveCall.allocation call

/-- Exact source erasure for one original receive-worker iteration and the
whole original bounded worker. Callback erasure is explicit; the capacity-plus-one (4097-poll)
exhaustion Stop is preserved, without an assumed queue-drain premise. -/
theorem handshake_receive_worker_access_erasure
    (hi : ErasesPrefix afterItem originalAfter) (hc : ErasesPrefix condResched originalResched) :
    ErasesPrefix (Lifetimes.receiveIterPrefix afterItem)
      (workerIter .receiveWorker none (liftWG receiveStep) originalAfter) ∧
    ErasesPrefix (Lifetimes.handshakeReceiveWorkerPrefix condResched)
      (handshakeReceiveWorker originalResched) :=
  ⟨Lifetimes.receiveIterPrefix_erases hi, Lifetimes.handshakeReceiveWorkerPrefix_erases hc⟩

/-- Complete failed and successful worker prefixes compose under explicit
rescheduling contracts. The callback runs only after the handler and counter
decrement; callbacks may change residents while preserving the invariant. -/
theorem handshake_receive_worker_ambient_access_preserves (c : Lifetimes.ProductAmbientContracts I)
    (r : Lifetimes.ProductHandshakeReceiveContracts I) (q : Lifetimes.ProductReceiveQueueContracts I)
    (hi : PrefixPreserves I Lifetimes.LifetimeEvent.Safe afterItem)
    (hc : PrefixPreserves I Lifetimes.LifetimeEvent.Safe condResched) :
    PrefixPreserves I Lifetimes.LifetimeEvent.Safe (Lifetimes.receiveIterPrefix afterItem) ∧
    PrefixPreserves I Lifetimes.LifetimeEvent.Safe (Lifetimes.handshakeReceiveWorkerPrefix condResched) :=
  ⟨Lifetimes.receiveIterPrefix_preserves c r q hi,
   Lifetimes.handshakeReceiveWorkerPrefix_preserves c r q hc⟩

/-- The original receive step and all local helpers discharge concrete
allocation safety; only the caller-provided rescheduling observations retain
an explicit contract. This is local worker composition, not a scheduler proof. -/
theorem handshake_receive_worker_allocation_access_preserves
    (hi : PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe afterItem)
    (hc : PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe condResched) :
    PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe (Lifetimes.receiveIterPrefix afterItem) ∧
    PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe (Lifetimes.handshakeReceiveWorkerPrefix condResched) :=
  handshake_receive_worker_ambient_access_preserves (Lifetimes.ProductAmbientContracts.ofNative Lifetimes.allocationAmbient)
    (Lifetimes.ProductHandshakeReceiveContracts.ofNative Lifetimes.allocationHandshakeReceive) (Lifetimes.ProductReceiveQueueContracts.ofNative Lifetimes.allocationReceiveQueue) hi hc

/-- Original CPU selection, packet receive and UDP entry have exact result,
WG and Ambient state and Stop erasure. Header and DS-field leaves are resident-access-free by
source inspection; data consumption uses its complete existing observer. -/
theorem receive_ingress_access_erasure (call : ReceiveIngressCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.ReceiveIngressCall.erases call

/-- Explicit queue/CPU-update and existing data-consumption contracts compose
safe ingress prefixes through ordinary drops and unsupported/record Stops. -/
theorem receive_ingress_ambient_access_preserves (c : ProductAmbientContracts I) (r : ProductReceiveIngressContracts I)
    (call : ReceiveIngressCall) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.ReceiveIngressCall.preserves_ambient_product c r call

/-- Allocation geometry discharges all ingress contracts without packet-shape,
authentication, queue-drain or index-owner premises. The byte/source handshake
queue is distinct from resident rx-skbs; worker scheduling remains separate. -/
theorem receive_ingress_allocation_access_preserves (call : ReceiveIngressCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.ReceiveIngressCall.allocation call

/-- Every demanded entry of an eager saved-peer filter contributes exactly one
read, including misses, before any later scheduler callback. This is an exact
observation equation; residency for safety is supplied at the source capture. -/
theorem scheduler_saved_filter_exact (f : PeerId → Peer → Option α)
    (xs : List (PeerId × Peer)) (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) :
    runStatePrefix (savedPeerFilterMap f xs) w ambient h =
      (.ok ((xs.filterMap (fun x => f x.1 x.2), w), ambient),
        h ++ xs.map (fun x => LifetimeEvent.peer (.read x.1 x.2.internalId))) :=
  Lifetimes.savedPeerFilterMap_run f xs w ambient h

/-- A section wrapper preserves its original start/stop and NET_RX metadata,
including failures before or after its callback. Callback safety is explicit. -/
theorem scheduler_section_access_contract (worker : Worker)
    (observed : PrefixM Lifetimes.LifetimeEvent Unit) (original : Leanux.M Unit)
    (he : ErasesPrefix observed original)
    (hs : PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe observed) :
    ErasesPrefix (runWorkerPrefix worker observed) (Env.runWorker worker original) ∧
      PrefixPreserves (fun h w => Lifetimes.AllocationInv h w.wg) Lifetimes.LifetimeEvent.Safe
        (runWorkerPrefix worker observed) :=
  ⟨runWorkerPrefix_erases worker he,
    runWorkerPrefix_preserves (Lifetimes.ProductAmbientContracts.ofNative Lifetimes.allocationAmbient).safe
      (Lifetimes.ProductAmbientContracts.ofNative Lifetimes.allocationAmbient).storeStable worker hs⟩

/-- Ten concrete Batch calls retain their original result type, full normal
World and exact Stop on every input. Committed histories exclude consistency
trials, whose copied-world execution is certified separately below. -/
theorem scheduler_family_access_erasure (call : BatchCall) : ErasesPrefix call.observed call.original :=
  Lifetimes.BatchCall.erases call

/-- Concrete NAPI/stack, encryption/checksum, TX, decrypt and handshake-receive
callbacks discharge all scheduler callback contracts. Every outcome retains a
safe committed access prefix; successful outcomes preserve allocation geometry.
This does not establish saved-reference ownership or progress without Stops. -/
theorem scheduler_family_allocation_access (call : BatchCall) : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe call.observed :=
  Lifetimes.BatchCall.allocation call

/-- The whole original consistency filter agrees with separately observed
trials in source order, including its first non-hidden Stop. Every candidate's
trial prefix is safe from the same entry invariant; the equation does not claim
unevaluated candidates ran. No speculative history or World is committed. -/
theorem scheduler_trial_filter_access (xs : List Activation) (w : World)
    (h : List Lifetimes.LifetimeEvent) (hi : Lifetimes.AllocationInv h w.wg) :
    runPrefix (liftPrefix (xs.filterM Env.Activation.consistent)) w h =
      ((xs.filterM (fun a => Lifetimes.activationTrialDecision a w h)).map (fun ys => (ys, w)), h) ∧
      ∀ a ∈ xs, Lifetimes.LifetimeEvent.Safe
        (runPrefix (Lifetimes.activationRunPrefix a) w h).2 :=
  ⟨Prod.ext (Lifetimes.activationTrials_filter xs w h) rfl,
    Lifetimes.activationTrials_safe xs w h hi⟩

/-- Six original allowed-IP list/removal calls preserve their full result,
normal WG and Ambient state and exact Stop on every input. Saved-map reads and hit writes are
interleaved in source order; neither erasure nor its observers assume a valid
trie, distinct node identifiers, live owners or successful bounded traversal. -/
theorem allowedips_family_access_erasure (call : AllowedIpsCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.AllowedIpsCall.erases call

/-- Explicit node-only and peer-list/hash contracts compose every retained
access prefix. The saved-map scan derives current stamps at its actual getDev
and transports them across earlier writes without adding source getters. -/
theorem allowedips_family_ambient_access_preserves (c : ProductAmbientContracts I) (r : ProductAllowedIpsContracts I) (call : AllowedIpsCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.AllowedIpsCall.preserves_product c r call

/-- Allocation geometry discharges the entire six-call family, including
malformed-node/owner and exhausted-walk failures after earlier accesses. This
is resolved-current-store access safety, not saved-reference ownership, trie
correctness or composition through the remaining insertion/lifecycle callers. -/
theorem allowedips_family_allocation_access_preserves (call : AllowedIpsCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.AllowedIpsCall.allocation call

/-- Four complete key-maintenance calls preserve the exact original result,
WG and Ambient state and Stop on all inputs. Reset reads its clock before its peer; expiration
retains saved scalar slots but resolves each key afresh; queued clearing ends
with the original peer put, including every earlier failed-access prefix. -/
theorem key_maintenance_family_access_erasure (call : KeyMaintenanceCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.KeyMaintenanceCall.erases call

/-- Maintenance composes explicit original index-removal and keypair-release
contracts with resident-access contracts. The scalar index frame is separate
from source-inspected internal access coverage. -/
theorem key_maintenance_family_ambient_access_preserves (c : ProductAmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (liftIndex (indexRemove owner)))))
    (hp : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now)))
    (call : KeyMaintenanceCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.KeyMaintenanceCall.preserves_product c hi hp call

/-- Concrete allocation geometry discharges the complete maintenance family.
These are resolved-store access prefixes, with no saved-slot ownership,
key-material non-use or successful outer clearing/lifecycle conclusion. -/
theorem key_maintenance_family_allocation_access_preserves (call : KeyMaintenanceCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.KeyMaintenanceCall.allocation call

/-- All five original expired callbacks and their dispatcher have unconditional
result/WG and Ambient state/Stop erasure. The strict retry comparison, fresh keepalive-reset
getter, caller-jiffies records and already-queued clear-work acquire/put remain
in source order; no own-timer-detachment premise is imposed. -/
theorem timer_callback_family_access_erasure (call : TimerCallbackCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.TimerCallbackCall.erases call

/-- Existing staging/socket/timer observations compose through explicit ambient
and scalar-work-queue contracts. Ordinary refusal and Stop retain their distinct
continuations; callbacks do not assume queue ownership or drain progress. -/
theorem timer_callback_family_ambient_access_preserves (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (q : ProductTimerQueueContracts I) (call : TimerCallbackCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.TimerCallbackCall.preserves_product c t q call

/-- Allocation geometry discharges every timer callback contract and retains
safe access prefixes on all original outcomes. This neither bounds retries nor
proves timer firing, reference credits, queue draining or whole-run lifecycle safety. -/
theorem timer_callback_family_allocation_access_preserves (call : TimerCallbackCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.TimerCallbackCall.allocation call

/-- Seven complete original inline-flush, timer-stop and peer-removal calls
retain their result, successful WG and Ambient state and exact Stop on every input. Queue
removal and pending-flag recomputation precede section entry; the original 4096-step drain,
placeholder order, early returns and both saved-ID passes remain unchanged. -/
theorem peer_removal_family_access_erasure (call : PeerRemovalCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.PeerRemovalCall.erases call

/-- Independent socket/index/release/allowed-IP and scalar queue/count contracts
compose the complete family. Saved lists contain raw IDs; their later callees
resolve current peers. No distinctness, pending-work, successful-drain or
reference-ownership premise replaces those accesses. -/
theorem peer_removal_family_ambient_access_preserves (c : ProductAmbientContracts I) (r : ProductPeerRemovalContracts I)
    (call : PeerRemovalCall) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.PeerRemovalCall.preserves_ambient_product c r call

/-- Concrete allocation geometry discharges every lower-call and bookkeeping
contract, retaining safe access prefixes after failures and the invariant on
normal completion. This is resolved-store safety, not reference-credit ownership,
eventual queue draining, device destruction or whole-run environment closure. -/
theorem peer_removal_family_allocation_access_preserves (call : PeerRemovalCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.PeerRemovalCall.allocation call

/-- Eight complete original socket/device controls retain their exact result, successful WG and
Ambient state and Stop on every input. Socket installation/freeing and saved peer-ID loops keep
source order; the up wrapper resets running after a negative open return, whereas a Stop skips
that later reset. Lifted socket helpers are separately source-inspected as free of resident
peer/keypair/packet accesses. -/
theorem device_control_family_access_erasure (call : DeviceControlCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.DeviceControlCall.erases call

/-- Explicit socket-scalar, TX, peer-removal and device-bookkeeping contracts
compose all device controls. Socket framing retains full resident stores and
allocation geometry; it does not substitute for internal access coverage.
No valid-list, distinctness, queue-progress or reference-credit premise is used. -/
theorem device_control_family_ambient_access_preserves (c : ProductAmbientContracts I) (r : ProductDeviceControlContracts I)
    (call : DeviceControlCall) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.DeviceControlCall.preserves_ambient_product c r call

/-- Concrete allocation geometry discharges all eight controls and keeps the
actual failed access prefixes. Timer, Netlink/environment and initialized composition
are supplied separately below;
reference affiliation is a stronger property, not a premise of this contract. -/
theorem device_control_family_allocation_access_preserves (call : DeviceControlCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.DeviceControlCall.allocation call

/-- Complete guarded create, destruction and deletion retain the original
result, successful WG and Ambient state and Stop for arbitrary inputs. Destruction records the
actual residual-store retirement at the final device drop, preserving all prior
accesses and failures. Creation has no resident-object accesses to omit. -/
theorem device_lifecycle_family_access_erasure (call : DeviceLifecycleCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.DeviceLifecycleCall.erases call

/-- Explicit device-control, scalar initialization, ratelimiter and retirement
contracts compose the lifecycle family for an ambient invariant. These contracts
are discharged concretely below; no queue-emptiness-to-store-emptiness or
reference-credit assumption replaces the actual final maps. -/
theorem device_lifecycle_family_ambient_access_preserves (c : ProductAmbientContracts I)
    (r : ProductDeviceLifecycleContracts I) (call : DeviceLifecycleCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.DeviceLifecycleCall.preserves_ambient_product c r call

/-- Concrete allocation identity safety covers all three original lifecycle
calls and their failed access prefixes. Successful creation registers a fresh
empty epoch without requiring the invariant at provisional setup. Netlink, timer
and initialized environment/Runner composition are supplied separately below. -/
theorem device_lifecycle_family_allocation_access_preserves (call : DeviceLifecycleCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.DeviceLifecycleCall.allocation call

/-- The final original device-store drop appends exactly the releases of its
actual resident maps, including both packet kinds with `(ifindex,id+1)` stamps.
This is logical store retirement, not a claim of individual kernel frees or
reference-credit ownership. Arbitrary incoming histories are retained exactly. -/
theorem device_retirement_actual_maps (w : WGWorld) (ambient : Ambient) (h : List Lifetimes.LifetimeEvent) :
    runWGPrefix Lifetimes.dropDevicePrefix w ambient h =
      (.ok (((), Lifetimes.deviceDropped w), ambient), h ++ Lifetimes.deviceRetirementEvents w) ∧
    (∀ i stamp, .peer (.release i stamp) ∈ Lifetimes.deviceRetirementEvents w ↔
      (Peers.snapshot w).slots i = some stamp) ∧
    (∀ i stamp, .keypair (.release i stamp) ∈ Lifetimes.deviceRetirementEvents w ↔
      Lifetimes.keypairResidents w i = some stamp) ∧
    (∀ i stamp, .packet (.release i stamp) ∈ Lifetimes.deviceRetirementEvents w ↔
      Lifetimes.packetResidents w i = some stamp) :=
  ⟨Lifetimes.dropDevicePrefix_run w ambient h, Lifetimes.deviceRetirementEvents_peer w,
    Lifetimes.deviceRetirementEvents_key w, Lifetimes.deviceRetirementEvents_packet w⟩

/-- Complete original add and insert retain every result, successful WG and Ambient state and
Stop on arbitrary inputs. Observations include each demanded saved peer-map
read and actual peer-list write, including second-allocation rollback. Node-only
leaves are separately inspected for resident-object access coverage. -/
theorem allowed_ip_insertion_family_access_erasure (call : AllowedIpsInsertCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.AllowedIpsInsertCall.erases call

/-- An ambient invariant explicitly permits the trie and its allocation-frontier
changes. The source-order peer observations compose without a bounded-address,
represented-tree, resident-target, successful-allocation or ownership premise. -/
theorem allowed_ip_insertion_family_ambient_access_preserves (c : ProductAmbientContracts I) (hc : ProductNodeAllocationStable I)
    (call : AllowedIpsInsertCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.AllowedIpsInsertCall.preserves_product c hc call

/-- Concrete allocation geometry discharges the node-allocation frame and
retains safe access prefixes after every original Stop. Normal negative returns
keep their actual mutations. This local result does not establish routing
correctness, Netlink/environment composition or initialized whole-run closure. -/
theorem allowed_ip_insertion_family_allocation_access_preserves (call : AllowedIpsInsertCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.AllowedIpsInsertCall.allocation call

/-- Original setPort, setAllowedip, setPeerCmd and complete wgSetDevice retain their exact
result, successful WG and Ambient state and Stop on arbitrary input WG and Ambient states and
attributes. Saved-ID loops, short-circuit attribute records and ordinary-return cleanup keep
source order. The keepalive setter observes the saved peer without a new getter. Device
configuration preserves generation-before-error, put-before-remove and every short-circuit
key-installation/zero-key record. -/
theorem configuration_family_access_erasure (call : ConfigurationCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.ConfigurationCall.erases call

/-- Explicit socket, trie-allocation, peer creation/removal, device configuration,
focused precomputation, index removal and TX contracts
compose the configuration family. A negative return preserves prior mutations
and reaches its original cleanup; a Stop retains the reached access prefix.
No valid-attributes, represented-tree, owner-affiliation or queue-progress
premise replaces a source access. -/
theorem configuration_family_ambient_access_preserves (c : ProductAmbientContracts I) (hs : ProductSocketControlStable I)
    (r : ProductConfigurationPeerContracts I) (d : ProductConfigurationDeviceContracts I) (call : ConfigurationCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.ConfigurationCall.preserves_ambient_product c hs r d call

/-- Concrete allocation geometry discharges all four configuration calls and
their failed access prefixes. Syscall tails and initialized whole-run composition
are supplied separately below. -/
theorem configuration_family_allocation_access_preserves (call : ConfigurationCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.ConfigurationCall.allocation call

/-- All seven original dump calls retain their exact typed result, successful
WG and Ambient state and Stop for arbitrary inputs and histories. Cursor reads are demanded at
original sites, the new cursor is acquired before the old cursor is put, and
receive pops its old chunk before running the next dump. -/
theorem dump_family_access_erasure (call : NetlinkDumpCall) : ErasesStatePrefix call.observed call.original :=
  Lifetimes.NetlinkDumpCall.erases call

/-- Explicit ambient reference contracts and socket-record stability compose
the whole dump family, including queued completion before done, malformed cursor
Stops, partial chunks and the original finite receive-loop exhaustion. No cursor
affiliation, list validity, reference credit or successful drain is assumed. -/
theorem dump_family_ambient_access_preserves (c : ProductAmbientContracts I) (stable : ProductDumpStable I) (call : NetlinkDumpCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) :=
  Lifetimes.NetlinkDumpCall.preserves_ambient_product c stable call

/-- Concrete AllocationInv discharges all seven calls and retains safe access
history on every Stop. The exact netlink mask retains all resident objects and
allocator geometry. This does not establish initialized enclosing Syscall/Env/
Runner closure or the reached entry invariant for every copied scheduling trial. -/
theorem dump_family_allocation_access_preserves (call : NetlinkDumpCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  Lifetimes.NetlinkDumpCall.allocation call

/-- The actual filter, scheduler, nested reschedule and receive-worker boundaries
retain every original result, successful World and Stop on arbitrary inputs.
Probe markers and focused lifetime events are proof-side observations only. -/
theorem scheduler_audit_family_erasure (call : BatchAuditCall) : ErasesPrefix call.observed call.original :=
  Lifetimes.BatchAuditCall.erases call

/-- From an allocation-valid projected entry, erasing probe markers gives the
existing committed lifetime observer exactly, including its failed history.
This correspondence does not require validity of old probe markers. -/
theorem scheduler_audit_committed_projection (call : BatchAuditCall) :
    ProjectsUnder (fun h w => AllocationInv h w.wg) AuditEvent.lifetime? call.observed call.committed :=
  Lifetimes.BatchAuditCall.projects call

/-- Every outcome retains safe committed accesses and valid saved trial entries.
Successful outcomes also retain the current allocation invariant. Each marker
keeps facts about its own saved World/history across subsequent mutations. -/
theorem scheduler_audit_prefix_preserves (call : BatchAuditCall) : PrefixPreserves AuditInv AuditSafe call.observed :=
  Lifetimes.BatchAuditCall.preserves call

/-- The original consistency filter has exactly one entry marker, even with no
candidates or on Stop. Its saved World and history precede the actual filter;
no speculative trial accesses are appended to committed lifetime history. -/
theorem scheduler_audit_filter_entry (w : World) (h : List AuditEvent) :
    runPrefix consistentFilterAudit w h =
      ((w.ambient.suspended.filterM Env.Activation.consistent).run w,
        h ++ [.probe ⟨w, lifetimeHistory h⟩]) :=
  Lifetimes.consistentFilterAudit_run w h

/-- Empty audit history and an allocation-valid local entry suffice for safe
committed accesses and every recorded filter entry's copied trials, including
failed prefixes. The exact filter equality retains candidate order, hidden-error
false decisions and the first non-hidden Stop; certification of all candidates
does not assert that unevaluated candidates ran. Enclosing initialized Env,
syscall and Runner composition is supplied separately below. -/
theorem scheduler_audit_reached_trials (call : BatchAuditCall) (w : World) (hi : AllocationInv [] w.wg) :
    AuditSafe (runPrefix call.observed w []).2 ∧
    ∀ p ∈ probeEntries (runPrefix call.observed w []).2,
      AllocationInv p.history p.world.wg ∧
      (p.world.ambient.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.ambient.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.ambient.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 :=
  Lifetimes.BatchAuditCall.from_allocation call w hi

/-- The current environment guard, deferred-worker and timer calls retain
every typed result, successful World and Stop on arbitrary inputs. Captured-map
lookups emit one read per present occurrence, none for absent slots; scan order,
short-circuit guards and original finite bounds remain unchanged. -/
theorem environment_deferred_family_erasure (call : EnvDeferredCall) : ErasesPrefix call.observed call.original :=
  Lifetimes.EnvDeferredCall.erases call

/-- Concrete allocation and saved-probe validity compose through actual worker
and timer dispatch. Every Stop retains safe committed accesses and valid saved
trial entries; only normal results assert the current invariant. No timer-detached,
queue-drain, distinct-ID, reference-credit or successful-callback premise is added. -/
theorem environment_deferred_family_preserves (call : EnvDeferredCall) : PrefixPreserves AuditInv AuditSafe call.observed :=
  Lifetimes.EnvDeferredCall.preserves call

/-- From a local allocation-valid entry, each recorded filter entry supplies
exact ordered copied-filter correspondence and safe isolated trial histories,
including failures. These speculative histories remain separate from committed
accesses. Enclosing syscall and initialized Runner composition are not supplied
by this local family. -/
theorem environment_deferred_reached_trials (call : EnvDeferredCall) (w : World) (hi : AllocationInv [] w.wg) :
    AuditSafe (runPrefix call.observed w []).2 ∧
    ∀ p ∈ probeEntries (runPrefix call.observed w []).2,
      AllocationInv p.history p.world.wg ∧
      (p.world.ambient.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.ambient.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.ambient.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 :=
  Lifetimes.EnvDeferredCall.from_allocation call w hi

/-- Fifteen original environment controls, observation, ingress and batch calls
retain their full typed result, successful World and exact Stop on arbitrary
inputs. Inline peer scans, multicast loopback, partial CQEs and the exact flood path
keep their original access and callback order. -/
theorem environment_remaining_family_erasure (call : EnvRemainingCall) : ErasesPrefix call.observed call.original :=
  Lifetimes.EnvRemainingCall.erases call

/-- Concrete current-store allocation and saved-probe validity compose through
the complete listed environment callers. Every Stop retains safe access history
and valid saved filter entries. No valid-packet, cursor-affiliation, distinct-ID,
reference-credit or successful-drain premise is introduced. -/
theorem environment_remaining_family_preserves (call : EnvRemainingCall) : PrefixPreserves AuditInv AuditSafe call.observed :=
  Lifetimes.EnvRemainingCall.preserves call

/-- Each actual reached consistency-filter entry has its own allocation-valid
World/history and exact ordered copied-filter result, including failed trials.
Speculative histories remain separate from committed lifetime accesses. This is
a local-entry theorem; initialized whole-Runner closure is supplied separately below. -/
theorem environment_remaining_reached_trials (call : EnvRemainingCall) (w : World) (hi : AllocationInv [] w.wg) :
    AuditSafe (runPrefix call.observed w []).2 ∧
    ∀ p ∈ probeEntries (runPrefix call.observed w []).2,
      AllocationInv p.history p.world.wg ∧
      (p.world.ambient.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.ambient.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.ambient.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 :=
  Lifetimes.EnvRemainingCall.from_allocation call w hi

/-- All typed dispatcher and complete syscall calls, plus the namespace holder
close, erase to their exact original result, successful World or Stop. No parser
or allocation-validity premise is required for source erasure. -/
theorem syscall_family_erasure (call : SyscallAuditCall) : ErasesPrefix call.observed call.original :=
  Lifetimes.SyscallAuditCall.erases call

/-- Concrete allocation identity and saved consistency-filter entries survive
all original syscall constructors, wrappers and postworkers. Stop retains the
safe reached history; no descriptor, ownership or drain premise is added. -/
theorem syscall_family_preserves (call : SyscallAuditCall) : PrefixPreserves AuditInv AuditSafe call.observed :=
  Lifetimes.SyscallAuditCall.preserves call

/-- Actual reached filter entries derive allocation validity from the syscall's
local entry, including postworker failures. The copied filter has exact order
and Stops; its speculative access histories stay separate from committed ones.
Initialized outer Runner composition is supplied separately below. -/
theorem syscall_reached_trials (call : SyscallAuditCall) (w : World) (hi : AllocationInv [] w.wg) :
    AuditSafe (runPrefix call.observed w []).2 ∧
    ∀ p ∈ probeEntries (runPrefix call.observed w []).2,
      AllocationInv p.history p.world.wg ∧
      (p.world.ambient.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.ambient.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.ambient.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 :=
  Lifetimes.SyscallAuditCall.from_allocation call w hi

/-! The initialized Runner exports discharge the caller obligations that remain
explicit in the preceding local contracts. They retain histories on Stop as well
as success, and treat consistency trials separately from committed accesses. -/

/-- The complete initialized observer preserves the original JSON or exact
indexed Stop for every typed Trace, both placeholder settings and arbitrary
incoming audit history. This is source erasure, separately from access safety. -/
theorem runner_audit_erasure (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (executeTraceAudit trace placeholders)
      (Runner.executeTrace trace placeholders) :=
  Lifetimes.executeTraceAudit_erases trace placeholders

/-- Starting from the original fixture, no committed peer, keypair or packet
read/write resolves an identity released earlier in that history. Every actual
saved filter entry is allocation-valid. This includes failed prefill, syscalls,
postworkers and end guards, with no parser, length, progress or success premise. -/
theorem runner_initialized_access_safety (trace : Runner.Trace) (placeholders : Bool) :
    AuditSafe (runPrefixOuter (executeTraceAudit trace placeholders) []).2 :=
  Lifetimes.executeTraceAudit_safe trace placeholders

/-- Actual initialized execution supplies each reached consistency-filter
entry's allocation invariant. Its copied filter has the original order and
early Stops, and each candidate's isolated access prefix is safe. Certifying
unevaluated candidates does not assert they ran or commit their observations. -/
theorem runner_initialized_reached_trials (trace : Runner.Trace) (placeholders : Bool) :
    ∀ p ∈ probeEntries (runPrefixOuter (executeTraceAudit trace placeholders) []).2,
      AllocationInv p.history p.world.wg ∧
      (p.world.ambient.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.ambient.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.ambient.suspended,
        LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 :=
  Lifetimes.executeTraceAudit_trials trace placeholders

end Leanux.Proofs.WG.LifetimeSafety
