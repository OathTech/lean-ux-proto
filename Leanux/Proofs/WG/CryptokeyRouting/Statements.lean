import Leanux.Proofs.WG.Packets.InitializedTransmit
import Leanux.Proofs.WG.Packets.NativeTransmitPreservation
import Leanux.Proofs.WG.Packets.TransmitStack
import Leanux.Proofs.WG.Lifetimes.TxCallSource
import Leanux.Proofs.WG.Lifetimes.BatchItemSource
import Leanux.Proofs.WG.Queues.PollSource
import Leanux.Proofs.WG.Queues.ObservePollSource
import Leanux.Proofs.WG.Packets.InitializedEntries
import Leanux.Proofs.WG.Packets.TxFront
import Leanux.Proofs.WG.Packets.PublicationRunner
import Leanux.Proofs.WG.Packets.PublicationEntries
import Leanux.Proofs.WG.Configuration.RoutingTraffic
import Leanux.Proofs.WG.Configuration.RoutingConfiguration
import Leanux.Proofs.WG.Configuration.RoutingDeferred
import Leanux.Proofs.WG.Packets.PublicationControls
import Leanux.Proofs.WG.Packets.PublicationTraffic
import Leanux.Proofs.WG.Packets.PublicationDump
import Leanux.Proofs.WG.Packets.PublicationOuter
import Leanux.Proofs.WG.Configuration.InitializedJoint
import Leanux.Proofs.WG.Configuration.RoutingPoll
import Leanux.Proofs.WG.Packets.PublicationHandshakeObserved
import Leanux.Proofs.WG.Packets.PublicationEncrypt
import Leanux.Proofs.WG.Packets.PublicationRemovalObserved
import Leanux.Proofs.WG.Origins.OwnerRunner
import Leanux.Proofs.WG.Packets.PublicationFrontierPrepare
import Leanux.Proofs.WG.Packets.PublicationFrontierLifecycle
import Leanux.Proofs.WG.Packets.PublicationStack
import Leanux.Proofs.WG.Origins.OwnerDeferred
import Leanux.Proofs.WG.Packets.PublicationConsumeHistory
import Leanux.Proofs.WG.Queues.JointRunner
import Leanux.Proofs.WG.Origins.CurrentRemaining
import Leanux.Proofs.WG.Origins.CurrentConfiguration
import Leanux.Proofs.WG.Origins.OwnerDeviceCreation
import Leanux.Proofs.WG.Origins.OwnerPeerConfiguration
import Leanux.Proofs.WG.Origins.OwnerCryptWorkers
import Leanux.Proofs.WG.Origins.OwnerEncrypt
import Leanux.Proofs.WG.Origins.OwnerTransmit
import Leanux.Proofs.WG.Origins.JointOwnerDevice
import Leanux.Proofs.WG.Queues.JointSyscallSet
import Leanux.Proofs.WG.Origins.OwnerReceive
import Leanux.Proofs.WG.Origins.OwnerDecrypt
import Leanux.Proofs.WG.Origins.CurrentDeferred
import Leanux.Proofs.WG.Origins.OwnerFocus
import Leanux.Proofs.WG.Queues.JointDevice
import Leanux.Proofs.WG.Origins.CurrentPollHistory
import Leanux.Proofs.WG.Origins.OwnerHistory
import Leanux.Proofs.WG.Packets.PublicationRetained
import Leanux.Proofs.WG.Queues.JointRemoval
import Leanux.Proofs.WG.Origins.CurrentWorkers
import Leanux.Proofs.WG.Origins.OwnerIndex
import Leanux.Proofs.WG.Origins.CurrentReceiveChecks
import Leanux.Proofs.WG.Origins.CurrentReceiveHistory
import Leanux.Proofs.WG.Origins.CurrentSensitive
import Leanux.Proofs.WG.Origins.CurrentRx
import Leanux.Proofs.WG.Origins.CurrentPoll
import Leanux.Proofs.WG.Packets.PublicationConsume
import Leanux.Proofs.WG.Queues.JointConfiguration
import Leanux.Proofs.WG.Origins.ConfiguredReceiveLeaves
import Leanux.Proofs.WG.Origins.ConfiguredReceive
import Leanux.Proofs.WG.Origins.CurrentDevice
import Leanux.Proofs.WG.Origins.CurrentHistory
import Leanux.Proofs.WG.Queues.JointPrimitives
import Leanux.Proofs.WG.Origins.CurrentIndex
import Leanux.Proofs.WG.Origins.CurrentPeerCreation
import Leanux.Proofs.WG.Origins.ConfiguredHandshake
import Leanux.Proofs.WG.Queues.PollAuthorization
import Leanux.Proofs.WG.Peers.AffiliationMaintenance
import Leanux.Proofs.WG.Origins.CurrentSession
import Leanux.Proofs.WG.Origins.CurrentPeerRetains
import Leanux.Proofs.WG.Packets.PublicationPrepare
import Leanux.Proofs.WG.Packets.PublicationIdentity
import Leanux.Proofs.WG.Packets.PublicationCurrent
import Leanux.Proofs.WG.Origins.CurrentMaintenance
import Leanux.Proofs.WG.Peers.ConfiguredAllowedIps
import Leanux.Proofs.WG.Peers.ConfiguredTimers
import Leanux.Proofs.WG.Origins.SupportRunner
import Leanux.Proofs.WG.Origins.SupportEnvironment
import Leanux.Proofs.WG.Origins.RetainingLifecycle
import Leanux.Proofs.WG.Queues.RxCompletionEnvironment
import Leanux.Proofs.WG.Queues.RxLinkEnvironment
import Leanux.Proofs.WG.Origins.IndexMaterial
import Leanux.Proofs.WG.Origins.SessionMaterial
import Leanux.Proofs.WG.Packets.RxOriginCuts
import Leanux.Proofs.WG.Packets.RoutingCuts
import Leanux.Proofs.WG.Packets.AffiliationCuts
import Leanux.Proofs.WG.Configuration.RunnerRouting
import Leanux.Proofs.WG.AllowedIps.RoutingDumpFrames
import Leanux.Proofs.WG.AllowedIps.RoutingEnvTimersFrames
import Leanux.Proofs.WG.AllowedIps.RoutingHandshakeReceiveFrames
import Leanux.Proofs.WG.AllowedIps.RoutingMaintenanceFrames
import Leanux.Proofs.WG.AllowedIps.RoutingRxFrames
import Leanux.Proofs.WG.Configuration.LifecycleCompletion
import Leanux.Proofs.WG.Configuration.DeviceCompletion
import Leanux.Proofs.WG.Configuration.PeerCommandCompletion
import Leanux.Proofs.WG.Configuration.ParserShape
import Leanux.Proofs.WG.Configuration.PeerUpdateCompletion
import Leanux.Proofs.WG.AllowedIps.RoutingAcquire
import Leanux.Proofs.WG.Configuration.PeerTailCompletion
import Leanux.Proofs.WG.AllowedIps.ConfigurationInputs
import Leanux.Proofs.WG.AllowedIps.ClearWalk
import Leanux.Proofs.WG.AllowedIps.RoutingHistory
import Leanux.Proofs.WG.AllowedIps.ContextRemoval
import Leanux.Proofs.WG.AllowedIps.RemovalStore
import Leanux.Proofs.WG.AllowedIps.RemovalChildStore
import Leanux.Proofs.WG.AllowedIps.RemovalDispatch
import Leanux.Proofs.WG.AllowedIps.RemovalPeer
import Leanux.Proofs.WG.AllowedIps.ArithmeticMirror
import Leanux.Proofs.WG.AllowedIps.Tree
import Leanux.Proofs.WG.AllowedIps.LookupMirror
import Leanux.Proofs.WG.AllowedIps.Insertion
import Leanux.Proofs.WG.AllowedIps.MutationMirror
import Leanux.Proofs.WG.AllowedIps.PlacementMirror
import Leanux.Proofs.WG.AllowedIps.ChildStore
import Leanux.Proofs.WG.AllowedIps.DeepChildStore
import Leanux.Proofs.WG.AllowedIps.ExactStore
import Leanux.Proofs.WG.AllowedIps.DeepGraft

/-!
# R3: prefix arithmetic, pure mutations and represented-tree operations

These statements connect the original arithmetic helpers to leading-bit
prefixes and prove longest-prefix lookup in a pure tree with local edge
conditions. Original node-store traversals terminate and refine this lookup
under an exact structural representation. Pure insertion preserves the local
invariants and implements canonical-prefix replacement. Original insertion
derives all structural cases from its total placement traversal. Every bounded-input
normal return is classified as success or one of two allocation refusals; successful
returns refine pure insertion and actual-root longest-prefix lookup. A supplied
opposite-family representation is preserved. Pure removal implements exact
entry filtering and preserves the structural invariants, with local compaction
laws under compression and distinct IDs. The original removal loop has an
all-input source equation; binary, root-tagged leaf/unary, nonroot unary and
leaf/parent-collapse iterations have total exact endpoints and complete store
effects. A represented forest and explicit target membership now derive every
local case and its separation, yielding total original-step execution, exact
retirement and both-family pure erasure. Explicit resident-only list coherence
then justifies the complete original saved-list removeByPeer loop, preserves
that coherence and removes exactly the target peer's entries. Original peer
creation and raw release preserve routing coherence, permitting orphan owners.
Finite normal create/insert/remove/release/clear histories from the original configured
fixture refine independent canonical flat-prefix updates and actual-root lookup.
Their input bounds and resident insertion targets are explicit. Whole local
setAllowedip/removal completions and the original acquired-peer configuration stage additionally
retain semantically valid completed prefixes on later Stops, using concrete
send/flush/cleanup routing frames that permit peer deletion. Actual lookup/create
contracts derive raw-slot residency through the complete public setPeerCmd
preflight, without a whole-command target-residency premise. Successful public
parseTrace supplies every configured peer's address shape, including malformed
entry alternatives. The complete original device configuration now composes
these cuts, including completed clear before remove-all cleanup. Entry routing
remains explicit in the local contracts. Optional-device routing now covers
actual guarded creation, down, destruction/deletion, absent whole commands and
all fixture/prefill modes. Concrete TX/Stack/RX, receive admission, NAPI, crypt
iterations, timer callbacks and device open/up/namespace exit preserve routing
through whole-call lifts, permitting peer deletion. Session creation, incoming
Noise/cookie handling and the concrete handshake receive iteration now have
original routing frames too. Complete activation runs, dispatch, scheduling and
nested rescheduling, deferred workers and both environment timer modes now
retain routing. Complete environment ingress/batch, control and stepped-dump
callers now retain routing too; environment deletion observes its actual lifecycle
completions. Complete syscall execution and the initialized Runner now retain
valid completed histories, including indexed Stops, and normal routing agreement
in the actual returned accumulator World. Address shape is explicit for typed
traces and follows from successful public parsing. Erasure is unconditional and
connects the full proof-side result to a literal source Runner whose JSON
projection is the original execution. Internal lookup witnesses, packet
authorization and identity/key affiliation remain separate.
Actual local parser output now discharges address shape for the setAllowedip
guards and its selected bounded insertion. Complete original free normally
clears both represented families and every resident list, preserving the other
fields and advancing sequence once. This is not a totality or physical-node
emptiness claim; orphan owners can still make the original traversal Stop.
-/

namespace Leanux.Proofs.WG.CryptokeyRouting

open Leanux
open Leanux.Proofs.WG.AllowedIps

/-- For bounded IPv4 or IPv6 addresses, the original `commonBits` returns
their maximal common-prefix length: every bounded CIDR is at most that
length exactly when the corresponding leading address bits agree. The
execution equation includes all of the mirror's branch records. -/
theorem commonBits_correct (n : WG.AipNode) (key width : Nat) (ambient : Ambient)
    (hw : width = 32 ∨ width = 128) (hn : n.bits < 2 ^ width)
    (hk : key < 2 ^ width) :
    (WG.commonBits (m := AmbientM) n key width).run ambient =
        .ok (common width n.bits key, commonRecords ambient width (n.bits ^^^ key)) ∧
      common width n.bits key ≤ width ∧
      ∀ cidr, cidr ≤ width →
        (cidr ≤ common width n.bits key ↔
          prefixBits width cidr n.bits = prefixBits width cidr key) := by
  exact ⟨commonBits_run n key width ambient hw, common_le _ _ _,
    fun _ hc => common_ge_iff hn hk hc⟩

/-- For bounded IPv4 or IPv6 addresses and a CIDR within the family width,
the original `prefixMatches` returns true exactly when the node and query
have equal leading prefix bits, with exactly its recorded Ambient effects. -/
theorem prefixMatches_correct (n : WG.AipNode) (key width : Nat) (ambient : Ambient)
    (hw : width = 32 ∨ width = 128) (hn : n.bits < 2 ^ width)
    (hk : key < 2 ^ width) (hc : n.cidr ≤ width) :
    (WG.prefixMatches (m := AmbientM) n key width).run ambient =
      .ok (decide (prefixBits width n.cidr n.bits = prefixBits width n.cidr key),
        commonRecords ambient width (n.bits ^^^ key)) :=
  prefixMatches_run n key width ambient hw hn hk hc

/-- Whenever the node has another address bit to inspect, the original
`choose` returns that next bit, either zero or one, as a pure action in
any monad admitted by the actual helper. The address width is arbitrary. -/
theorem choose_correct {m : Type → Type} [Monad m] [MonadLiftT AmbientM m]
    (n : WG.AipNode) (key : Nat) (hc : n.cidr < n.bitlen) :
    (WG.choose n key : m Nat) = pure (prefixBits n.bitlen (n.cidr + 1) key % 2) ∧
      prefixBits n.bitlen (n.cidr + 1) key % 2 < 2 := by
  constructor
  · simpa only [bit_eq_prefix_succ] using choose_run (m := m) n key hc
  · exact Nat.mod_lt _ (by decide)

/-- In the pure intermediate tree, lookup returns an owned prefix that
matches the query and is at least as long as every matching binding, or none
exactly when no binding matches. The premise contains only address bounds
and immediate-child conditions; establishing it from original mutations is
a separate, still-open refinement. -/
theorem pureTree_lookup_correct (t : Tree) (width key : Nat) (hv : t.Valid width) :
    Winner width key t.entries (t.lookup width key) :=
  Tree.lookup_spec hv key

/-- Local validity prevents duplicate canonical owned prefixes, including
different unmasked addresses that denote the same prefix. This is derived
for the pure tree without assuming global prefix uniqueness. -/
theorem pureTree_canonical_prefixes_unique (t : Tree) (width : Nat) (hv : t.Valid width) :
    (t.entries.map (Entry.prefixKey width)).Nodup :=
  Tree.prefixKeys_nodup hv

/-- A valid pure IPv4 or IPv6 tree has room within 130 traversal iterations
for a longest path and one empty-cursor check. The original traversal theorem
below uses this bound to rule out its explicit exhaustion error. -/
theorem pureTree_search_depth_bound (t : Tree) (width : Nat)
    (hw : width = 32 ∨ width = 128) (hv : t.Valid width) :
    t.height + 1 ≤ 130 := by
  have h := Tree.height_le hv
  rcases hw with rfl | rfl <;> omega

/-- The original traversal always returns normally on an exactly represented
valid IPv4 or IPv6 tree. It returns the longest matching owned prefix's node
ID, or none when no owned prefix matches, and preserves the native AipStore.
The representation premise describes the actual node map and backlinks;
establishing it from configuration mutations remains a separate obligation. -/
theorem original_findNode_lookup_correct (w : WG.AipStore) (ambient : Ambient)
    (width key : Nat) (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (t : Tree) (parent : WG.Slot)
    (hr : RepAt w.nodes width parent t) (hv : t.Valid width) :
    ∃ w' ambient', ((WG.findNode t.root width key).run w).run ambient =
        .ok (((t.lookup width key).map Entry.id, w'), ambient') ∧
      Winner width key t.entries (t.lookup width key) ∧ w' = w := by
  obtain ⟨w', ambient', he, hframe⟩ := findNode_run w ambient width key hw hk t parent hr hv
  exact ⟨w', ambient', he, Tree.lookup_spec hv key, hframe⟩

/-- Any successful execution of the original traversal on an exactly
represented valid IPv4 or IPv6 tree returns its longest matching owned
prefix's node ID, or none when no owned prefix matches. This theorem assumes
the structural representation at entry; it does not establish that mutations
produce it. It is the successful-run corollary of the total result above. -/
theorem original_findNode_successful_lookup_correct (w w' : WG.AipStore)
    (ambient ambient' : Ambient)
    (width key : Nat) (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (t : Tree) (parent : WG.Slot)
    (hr : RepAt w.nodes width parent t) (hv : t.Valid width) (result : Option Nat)
    (hreturn : ((WG.findNode t.root width key).run w).run ambient =
      .ok ((result, w'), ambient')) :
    result = (t.lookup width key).map Entry.id ∧
      Winner width key t.entries (t.lookup width key) ∧ w' = w := by
  have h := findNode_refines w w' ambient ambient' width key hw hk t parent hr hv result hreturn
  exact ⟨h.1, Tree.lookup_spec hv key, h.2⟩

/-- Pure Patricia insertion replaces the owner of exactly the requested
canonical prefix, retaining unmasked addresses and old node identifiers on
overwrite. Lookup afterward chooses the longest match in that updated flat
binding list. This intermediate-algorithm theorem is complemented by the
original insertion dispatch and allocation-refusal theorems below; complete
configuration-history agreement remains a separate obligation. -/
theorem pureTree_insert_lookup_correct (t : Tree) (width fresh addr cidr peer key : Nat)
    (hv : t.Valid width) (ha : addr < 2 ^ width) (hc : cidr ≤ width) :
    let result := t.insertFresh width fresh addr cidr peer
    result.binding.peer = peer ∧
      result.binding.prefixKey width = (cidr, prefixBits width cidr addr) ∧
      Winner width key
        (result.binding :: t.entries.filter
          (fun e => e.prefixKey width != (cidr, prefixBits width cidr addr)))
        (result.tree.lookup width key) := by
  exact ⟨Tree.insertFresh_peer t width fresh addr cidr peer,
    Tree.insertFresh_prefixKey t width fresh addr cidr peer,
    Tree.insertFresh_lookup_spec hv ha hc fresh peer key⟩

/-- The same pure insertion preserves local validity and Patricia compression.
From unique old node identifiers below the fresh frontier, the result keeps
unique identifiers below the advanced frontier and adds exactly zero, one or
two consecutive identifiers, including any ownerless intermediate node. -/
theorem pureTree_insert_preserves_structure (t : Tree) (width fresh addr cidr peer : Nat)
    (hv : t.Valid width) (ha : addr < 2 ^ width) (hc : cidr ≤ width)
    (hcomp : t.Compressed) (hn : t.nodeIds.Nodup)
    (hf : ∀ id ∈ t.nodeIds, id < fresh) :
    let result := t.insertFresh width fresh addr cidr peer
    result.tree.Valid width ∧ result.tree.Compressed ∧ result.allocations ≤ 2 ∧
      result.tree.nodeIds.Nodup ∧
      result.tree.nodeIds.Perm (List.range' fresh result.allocations ++ t.nodeIds) ∧
      ∀ id ∈ result.tree.nodeIds, id < fresh + result.allocations := by
  exact ⟨Tree.insertFresh_valid hv ha hc fresh peer,
    Tree.insertFresh_compressed hcomp width fresh addr cidr peer,
    Tree.insertFresh_allocations t width fresh addr cidr peer,
    Tree.insertFresh_nodeIds_nodup hn hf width addr cidr peer,
    Tree.insertFresh_nodeIds_perm t width fresh addr cidr peer,
    Tree.insertFresh_nodeIds_bounded hf width addr cidr peer⟩

/-- On an empty selected root, the original `add` either refuses allocation
without changing WGWorld or installs precisely the pure insertion's tree.
Whole-store freshness protects every represented node of the opposite family;
the target peer must exist. This classifies normal executions, without
asserting that missing or malformed allocation records complete normally. -/
theorem original_add_empty_root_correct (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d v4 = none)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hb : NodesBelow d) (other : Tree)
    (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (result : Int)
    (hr : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((result, w'), ambient')) :
    let installed := emptyInstalled d v4 addr cidr pid p
    let tree := (Tree.empty.insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (result = -ENOMEM ∧ w' = w) ∨
      (result = 0 ∧ w' = { w with dev := some installed } ∧
        NodesBelow installed ∧ rootValue installed v4 = tree.root ∧
        RepAt installed.nodes (rootWidth v4) (rootSlot v4) tree ∧ tree.Valid (rootWidth v4) ∧
        rootValue installed (!v4) = rootValue d (!v4) ∧
        RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) := by
  apply case_add_empty_root_correct <;> assumption

/-- The original `insert` increments the table sequence on both normal
outcomes. Success into an empty selected root agrees with pure insertion;
allocation refusal preserves the device apart from that sequence increment.
The whole WGWorld equation frames unrelated WG state. The opposite root's value
and any supplied opposite-family representation survive either outcome.
An existing caller linkage between them is preserved, not established here.
As in the original wrapper,
family 4 selects IPv4 and every other value selects IPv6. General insertion
history, owner liveness, and packet admission are not asserted here. -/
theorem original_insert_empty_root_correct (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (family addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d (family == 4) = none)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hb : NodesBelow d) (other : Tree)
    (ho : RepAt d.nodes (rootWidth (!(family == 4))) (rootSlot (!(family == 4))) other)
    (result : Int) (hr : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((result, w'), ambient')) :
    let v4 := family == 4
    let tree := (Tree.empty.insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    ∃ d', w' = { w with dev := some d' } ∧
      d'.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧ NodesBelow d' ∧
      rootValue d' (!v4) = rootValue d (!v4) ∧
      RepAt d'.nodes (rootWidth (!v4)) (rootSlot (!v4)) other ∧
      ((result = -ENOMEM ∧ d' = bumpSeq d) ∨
        (result = 0 ∧ d' = emptyInstalled (bumpSeq d) v4 addr cidr pid p ∧
          rootValue d' v4 = tree.root ∧ RepAt d'.nodes (rootWidth v4) (rootSlot v4) tree ∧
          tree.Valid (rootWidth v4))) := by
  rcases insert_empty_exact w w' ambient ambient' d hd family addr cidr pid p hp he hc result hr with hf | hs
  · exact ⟨bumpSeq d, hf.2, rfl, hb, rfl, ho, .inl ⟨hf.1, rfl⟩⟩
  · refine ⟨emptyInstalled (bumpSeq d) (family == 4) addr cidr pid p, hs.2,
      emptyInstalled_seq (bumpSeq d) (family == 4) addr cidr pid p,
      emptyInstalled_below (bumpSeq d) hb (family == 4) addr cidr pid p,
      emptyInstalled_other_root (bumpSeq d) (family == 4) addr cidr pid p,
      emptyInstalled_other_rep (bumpSeq d) hb (family == 4) addr cidr pid p other ho,
      .inr ⟨hs.1, rfl, emptyInstalled_root (bumpSeq d) (family == 4) addr cidr pid p,
        emptyInstalled_rep (bumpSeq d) (family == 4) addr cidr pid p,
        Tree.insertFresh_valid (by trivial) ha hc d.nextNode pid⟩⟩

/-- The original placement loop terminates on an exactly represented valid
IPv4 or IPv6 tree. Its result has a context whose ancestors strictly cover
the requested prefix and choose the requested branch, ending at an exact
node or the first stopped subtree. Exact nodes include ownerless nodes.
The exact flag agrees with zero allocations in the existing pure insertion;
the theorem does not yet refine nonempty original mutation or history. -/
theorem original_nodePlacement_correct (w : WG.AipStore) (ambient : Ambient)
    (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (t : Tree) (base : WG.Slot)
    (hr : RepAt w.nodes width base t) (hv : t.Valid width) :
    ∃ result w' ambient', ((WG.nodePlacement t.root key cidr width).run w).run ambient =
      .ok ((result, w'), ambient') ∧
      w' = w ∧ PlacementWitness t width key cidr result ∧
      ∀ fresh peer, result.2 = true ↔
        (t.insertFresh width fresh key cidr peer).allocations = 0 := by
  obtain ⟨result, w', ambient', he, hf, hp⟩ :=
    nodePlacement_run w ambient width key cidr hw hk hc t base hr hv
  exact ⟨result, w', ambient', he, hf, hp, hp.allocations⟩

/-- A nonexact original placement identifies a structurally graftable focus.
Pure insertion of any fresh node identifiers at that focus, rebuilt through
the context, is exactly the existing recursive `insertFresh` result. This
links the original traversal to the pure mutation's stopped case without
assuming an insertion-history or peer-list invariant. -/
theorem original_nodePlacement_stopped (w w' : WG.AipStore) (ambient ambient' : Ambient)
    (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (t : Tree) (base : WG.Slot)
    (hr : RepAt w.nodes width base t) (hv : t.Valid width) (parent : Option Nat)
    (hreturn : ((WG.nodePlacement t.root key cidr width).run w).run ambient =
      .ok (((parent, false), w'), ambient')) :
    w' = w ∧ ∃ (c : Context) (u : Tree), t = c.plug u ∧ c.Follows width key cidr ∧
      parent = c.lastParent none ∧ Graftable width key cidr u ∧
      ∀ fresh peer, t.insertFresh width fresh key cidr peer =
        let localResult := graft width fresh key cidr peer u
        { localResult with tree := c.plug localResult.tree } := by
  obtain ⟨hf, hp⟩ := nodePlacement_refines w w' ambient ambient' width key cidr hw hk hc t base hr hv
    (parent, false) hreturn
  exact ⟨hf, hp.stopped rfl hv hk⟩

/-- If the requested path ends at a known empty focus, the original placement
loop completes with precisely its enclosing parent and a false exact flag.
This traversal fact supplies the missing-child case for future mutation
refinement; it does not assert that the subsequent allocation completes. -/
theorem original_nodePlacement_empty_focus (w : WG.AipStore) (ambient : Ambient)
    (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (c : Context) (base : WG.Slot)
    (hr : RepAt w.nodes width base (c.plug .empty))
    (hv : (c.plug .empty).Valid width) (hf : c.Follows width key cidr) :
    ∃ w' ambient', ((WG.nodePlacement (c.plug .empty).root key cidr width).run w).run ambient =
      .ok (((c.lastParent none, false), w'), ambient') ∧ w' = w := by
  obtain ⟨result, w', ambient', he, hp⟩ :=
    (Leanux.Proofs.Framing.total_iff_run_ambient _ _ _).mp
      (nodePlacement_empty_focus_wp w width key cidr hw hk hc c base hr hv hf) w ambient rfl
  rcases hp with ⟨rfl, hframe⟩
  exact ⟨w', ambient', he, hframe⟩

/-- On a represented root whose requested immediate child is empty, original
`add` either refuses allocation without a WGWorld change or installs exactly
the existing pure insertion result. The exact installed state includes
the new backlink, parent slot update, and peer-list append. Whole-store freshness and explicit
parent/sibling separation support the representation; no peer-list coherence
or general insertion-history premise is assumed or concluded. Both root
values and the sequence counter are preserved, as is any supplied
opposite-family representation. Record errors remain errors. -/
theorem original_add_empty_child_correct (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (v4 : Bool) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : side < 2) (hbelow : NodesBelow d)
    (hparent : n.id ∉ sibling.nodeIds)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (Tree.fork n side .empty sibling))
    (hv : (Tree.fork n side .empty sibling).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4) (hlt : n.cidr < cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (hbit : bit (rootWidth v4) n.cidr addr = side)
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (result : Int)
    (hreturn : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((result, w'), ambient')) :
    let installed := gapInstalled d v4 n side sibling addr cidr pid p
    let inserted := (Tree.fork n side .empty sibling).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    (result = -ENOMEM ∧ w' = w) ∨
      (result = 0 ∧ w' = { w with dev := some installed } ∧ NodesBelow installed ∧
        rootValue installed v4 = inserted.tree.root ∧
        RepAt installed.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
        inserted.tree.Valid (rootWidth v4) ∧ installed.nextNode = d.nextNode + 1 ∧
        installed.peerAllowedips.seq = d.peerAllowedips.seq ∧
        (∀ family, rootValue installed family = rootValue d family) ∧
        RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) := by
  have outcome := (Leanux.Proofs.Framing.hoare_iff_run_ambient _ _ _).mp
    (add_root_gap_wp w d hd v4 n side sibling addr cidr pid p hp hroot hb hbelow hr hv ha hc hlt hm hbit)
    w ambient result w' ambient' rfl hreturn
  rcases outcome with hf | hs
  · exact .inl hf
  have shape := gap_insertFresh n side sibling (rootWidth v4) d.nextNode addr cidr pid hb hlt hm hbit
  have hn := (gap_rep_parts hb hr).1
  refine .inr ⟨hs.1, hs.2, gapInstalled_below d v4 n side sibling addr cidr pid p hbelow
    (hbelow n.id _ hn), ?_, ?_, Tree.insertFresh_valid hv ha hc d.nextNode pid,
    rfl, rfl, (fun family => gapInstalled_roots d v4 family n side sibling addr cidr pid p),
    gapInstalled_other_rep d v4 n side sibling addr cidr pid p hb hbelow hr other ho⟩
  · simpa only [shape, Tree.fork_root] using
      (gapInstalled_roots d v4 v4 n side sibling addr cidr pid p).trans hroot
  · simpa only [shape] using gapInstalled_rep d v4 n side sibling addr cidr pid p hb hbelow hparent hr

/-- After successful original insertion into an immediate empty child, original
lookup from the resulting selected root terminates and returns a longest
matching binding in the independently updated flat list. This composes the
mutation representation with the previously proved original traversal. -/
theorem original_add_empty_child_lookup (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (v4 : Bool) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : side < 2) (hbelow : NodesBelow d)
    (hparent : n.id ∉ sibling.nodeIds)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (Tree.fork n side .empty sibling))
    (hv : (Tree.fork n side .empty sibling).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4) (hlt : n.cidr < cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (hbit : bit (rootWidth v4) n.cidr addr = side) (key : Nat) (hk : key < 2 ^ rootWidth v4)
    (hreturn : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((0, w'), ambient')) :
    let old := Tree.fork n side .empty sibling
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ d' final finalAmbient, w'.dev = some d' ∧
      ((WG.liftAip (WG.findNode (rootValue d' v4) (rootWidth v4) key)).run w').run ambient' =
        .ok (((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final), finalAmbient) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: old.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final = w' := by
  have outcome := original_add_empty_child_correct w w' ambient ambient' d hd v4 n side sibling addr cidr pid p
    hp hroot hb hbelow hparent hr hv ha hc hlt hm hbit .empty trivial 0 hreturn
  rcases outcome with hf | hs
  · simp [ENOMEM] at hf
  obtain ⟨_, hkernel, _, hroot', hrep, hvalid, _⟩ := hs
  have hdev : w'.dev = some (gapInstalled d v4 n side sibling addr cidr pid p) := by
    rw [hkernel]
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨finalAmbient, he⟩ := findNode_lift_run w' ambient'
    (gapInstalled d v4 n side sibling addr cidr pid p) hdev (rootWidth v4) key hw hk
    ((Tree.fork n side .empty sibling).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (rootSlot v4) hrep hvalid
  refine ⟨_, w', finalAmbient, hdev, ?_,
    Tree.insertFresh_lookup_spec hv ha hc d.nextNode pid key, rfl⟩
  simpa only [hroot', Tree.lookupId] using he

/-- Original `add` into an empty child at any represented depth either
refuses allocation without a WGWorld change or installs the existing pure
insertion result. The actual selected root, structural representation, local
validity and duplicate-free node identifiers are retained. Premises explicitly
supply the requested path, initial root linkage and whole-store freshness.
Both root values, the sequence, and any supplied opposite-family representation
are framed. Separate dispatch, coherence and finite-call history contracts below
cover those additional boundaries; whole device-command composition is supplied
separately below, together with lifecycle and initialized Runner composition.
The initialized packet-path contracts are exported separately below. -/
theorem original_add_context_empty_child_correct (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (v4 : Bool) (c : Context) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (Tree.fork n side .empty sibling)).root)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hnodup : (c.plug (Tree.fork n side .empty sibling)).nodeIds.Nodup)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork n side .empty sibling)))
    (hv : (c.plug (Tree.fork n side .empty sibling)).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hlt : n.cidr < cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (hbit : bit (rootWidth v4) n.cidr addr = side)
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (result : Int)
    (hreturn : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((result, w'), ambient')) :
    let installed := gapInstalledAt d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p
    let inserted := (c.plug (Tree.fork n side .empty sibling)).insertFresh
      (rootWidth v4) d.nextNode addr cidr pid
    (result = -ENOMEM ∧ w' = w) ∨
      (result = 0 ∧ w' = { w with dev := some installed } ∧ NodesBelow installed ∧
        rootValue installed v4 = inserted.tree.root ∧
        RepAt installed.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
        inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧
        installed.nextNode = d.nextNode + 1 ∧ installed.peerAllowedips.seq = d.peerAllowedips.seq ∧
        (∀ family, rootValue installed family = rootValue d family) ∧
        RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) := by
  apply case_add_context_empty_child_correct <;> assumption

/-- After successful original empty-child insertion at any represented depth,
original lookup starts at the actual resulting selected root, terminates, and
returns a longest matching binding in the independently updated flat list.
This is one mutation case with explicit structural premises, not a general
configuration-history or packet-admission theorem. -/
theorem original_add_context_empty_child_lookup (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (v4 : Bool) (c : Context) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (Tree.fork n side .empty sibling)).root)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hnodup : (c.plug (Tree.fork n side .empty sibling)).nodeIds.Nodup)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork n side .empty sibling)))
    (hv : (c.plug (Tree.fork n side .empty sibling)).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hlt : n.cidr < cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (hbit : bit (rootWidth v4) n.cidr addr = side) (key : Nat) (hk : key < 2 ^ rootWidth v4)
    (hreturn : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((0, w'), ambient')) :
    let old := c.plug (Tree.fork n side .empty sibling)
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ d' final finalAmbient, w'.dev = some d' ∧
      ((WG.liftAip (WG.findNode (rootValue d' v4) (rootWidth v4) key)).run w').run ambient' =
        .ok (((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final), finalAmbient) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: old.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final = w' := by
  have outcome := original_add_context_empty_child_correct w w' ambient ambient' d hd v4 c n side sibling addr cidr pid p
    hp hroot hb hbelow hnodup hr hv ha hc hf hlt hm hbit .empty trivial 0 hreturn
  rcases outcome with hfail | hs
  · simp [ENOMEM] at hfail
  obtain ⟨_, hkernel, _, hroot', hrep, hvalid, _⟩ := hs
  have hdev : w'.dev = some (gapInstalledAt d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p) := by
    rw [hkernel]
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨finalAmbient, he⟩ := findNode_lift_run w' ambient'
    (gapInstalledAt d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p) hdev (rootWidth v4) key hw hk
    ((c.plug (Tree.fork n side .empty sibling)).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (rootSlot v4) hrep hvalid
  refine ⟨_, w', finalAmbient, hdev, ?_,
    Tree.insertFresh_lookup_spec hv ha hc d.nextNode pid key, rfl⟩
  simpa only [hroot', Tree.lookupId] using he

/-- The original configuration insertion wrapper for an empty child at any
represented depth increments the sequence once on either normal outcome.
Success retains the actual root linkage, pure insertion representation, local
validity and duplicate-free node identifiers; refusal leaves only the sequence
increment. Both root values and a supplied opposite-family representation are
preserved. This does not claim coverage of other insertion cases or histories. -/
theorem original_insert_context_empty_child_correct (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (family : Nat) (c : Context) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d (family == 4) = (c.plug (Tree.fork n side .empty sibling)).root)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hnodup : (c.plug (Tree.fork n side .empty sibling)).nodeIds.Nodup)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4))
      (c.plug (Tree.fork n side .empty sibling)))
    (hv : (c.plug (Tree.fork n side .empty sibling)).Valid (rootWidth (family == 4)))
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hf : c.Follows (rootWidth (family == 4)) addr cidr) (hlt : n.cidr < cidr)
    (hm : prefixBits (rootWidth (family == 4)) n.cidr n.addr =
      prefixBits (rootWidth (family == 4)) n.cidr addr)
    (hbit : bit (rootWidth (family == 4)) n.cidr addr = side)
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!(family == 4))) (rootSlot (!(family == 4))) other)
    (result : Int) (hreturn : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((result, w'), ambient')) :
    let v4 := family == 4
    let inserted := (c.plug (Tree.fork n side .empty sibling)).insertFresh
      (rootWidth v4) d.nextNode addr cidr pid
    ∃ d', w' = { w with dev := some d' } ∧ d'.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧
      NodesBelow d' ∧ (∀ f, rootValue d' f = rootValue d f) ∧
      RepAt d'.nodes (rootWidth (!v4)) (rootSlot (!v4)) other ∧
      ((result = -ENOMEM ∧ d' = bumpSeq d) ∨
        (result = 0 ∧ d' = gapInstalledAt (bumpSeq d) v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p ∧
          rootValue d' v4 = inserted.tree.root ∧
          RepAt d'.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
          inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧ d'.nextNode = d.nextNode + 1)) := by
  rw [insert_run_bump w ambient d hd family addr cidr pid] at hreturn
  have outcome := original_add_context_empty_child_correct
    { w with dev := some (bumpSeq d) } w' ambient ambient' (bumpSeq d) rfl (family == 4)
    c n side sibling addr cidr pid p hp hroot hb hbelow hnodup hr hv ha hc hf hlt hm hbit other ho result hreturn
  rcases outcome with hfail | hs
  · refine ⟨bumpSeq d, hfail.2, rfl, hbelow, ?_, ho, .inl ⟨hfail.1, rfl⟩⟩
    intro f
    cases f <;> rfl
  · obtain ⟨hret, hk, hbounded, hroot', hrep, hvalid, hnodup', hnext, hseq, hroots, hother⟩ := hs
    refine ⟨_, hk, hseq, hbounded, ?_, hother,
      .inr ⟨hret, rfl, hroot', hrep, hvalid, hnodup', hnext⟩⟩
    intro f
    exact (hroots f).trans (by cases f <;> rfl)

/-- Original list deletion completes for a present device. Its exact endpoint
is the source's fold over saved peer values, and every resident peer list is
filtered pointwise. Resident identities and all allocation counters remain
unchanged. This endpoint theorem does not claim internal-access coverage. -/
theorem original_listDel_correct (w : WGWorld) (ambient : Ambient) (d : WG.Device) (hd : w.dev = some d) (id : Nat) :
    ∃ w' ambient', ((WG.listDel id).run w).run ambient = .ok (((), w'), ambient') ∧
      w' = { w with dev := some (unlisted d id) } ∧
      (∀ pid : Nat, (unlisted d id).peers[pid]? = (d.peers[pid]?).map (unlist id)) ∧
      (∀ pid : Nat, ((unlisted d id).peers[pid]?).map WG.Peer.internalId =
        (d.peers[pid]?).map WG.Peer.internalId) ∧
      (unlisted d id).nextPeer = d.nextPeer ∧ (unlisted d id).nextNode = d.nextNode ∧
      (unlisted d id).nextKeypairId = d.nextKeypairId ∧ (unlisted d id).nextSkb = d.nextSkb := by
  obtain ⟨result, w', ambient', hr, _, hk⟩ := (Leanux.Proofs.Framing.total_iff_run_ambient _ _ _).mp
    (listDel_wp w d hd id) w ambient rfl
  exact ⟨w', ambient', hr, hk, unlisted_get d id, unlisted_identity d id, rfl, rfl, rfl, rfl⟩

/-- Original exact-prefix insertion terminates at any represented depth and
refines the same pure insertion used for lookup correctness. It preserves the
old node's identifier, unmasked address and structural fields, filters every
peer list, and appends the ID once to the filtered target list. Previous
ownership and coherent peer lists are not prerequisites. Root linkage,
duplicate-free represented IDs and local validity are explicit premises;
configuration histories and packet admission are separate obligations. -/
theorem original_add_context_exact_correct (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (v4 : Bool) (c : Context) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (.node n l r)).root)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (.node n l r)))
    (hv : (c.plug (.node n l r)).Valid (rootWidth v4))
    (hnodup : (c.plug (.node n l r)).nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hn : n.cidr = cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) :
    let installed := exactInstalled d n.id (encode (rootWidth v4) (c.slot (rootSlot v4)) n l r) pid p
    let inserted := (c.plug (.node n l r)).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ w' ambient', ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((0, w'), ambient') ∧
      w' = { w with dev := some installed } ∧
      rootValue installed v4 = inserted.tree.root ∧
      RepAt installed.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds = (c.plug (.node n l r)).nodeIds ∧
      inserted.tree.nodeIds.Nodup ∧ inserted.allocations = 0 ∧
      installed.nextNode = d.nextNode ∧ installed.peerAllowedips.seq = d.peerAllowedips.seq ∧
      (∀ f, rootValue installed f = rootValue d f) ∧
      RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other ∧
      installed.peers[pid]? = some { p with allowedipsList := WG.listRemove p.allowedipsList n.id ++ [n.id] } ∧
      (∀ q : Nat, pid ≠ q → installed.peers[q]? = (d.peers[q]?).map (unlist n.id)) ∧
      (∀ q : Nat, (installed.peers[q]?).map WG.Peer.internalId = (d.peers[q]?).map WG.Peer.internalId) ∧
      (NodesBelow d → NodesBelow installed) := by
  apply case_add_context_exact_correct <;> assumption

/-- After original exact-prefix insertion, lookup from the actual resulting
root terminates and satisfies the independent canonical-prefix replacement
specification. The inserted binding retains the old stored address and ID. -/
theorem original_add_context_exact_lookup (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (v4 : Bool) (c : Context) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (.node n l r)).root)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (.node n l r)))
    (hv : (c.plug (.node n l r)).Valid (rootWidth v4))
    (hnodup : (c.plug (.node n l r)).nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hn : n.cidr = cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (key : Nat) (hk : key < 2 ^ rootWidth v4) :
    let old := c.plug (.node n l r)
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ w' ambient' d' final finalAmbient,
      ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((0, w'), ambient') ∧
      w'.dev = some d' ∧
      ((WG.liftAip (WG.findNode (rootValue d' v4) (rootWidth v4) key)).run w').run ambient' =
        .ok (((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final), finalAmbient) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: old.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final = w' := by
  obtain ⟨w', ambient', hrun, hkernel, hroot', hrep, hvalid, _⟩ :=
    original_add_context_exact_correct w ambient d hd v4 c n l r addr cidr pid p hp hroot hr hv hnodup
      ha hc hf hn hm .empty trivial
  let installed := exactInstalled d n.id (encode (rootWidth v4) (c.slot (rootSlot v4)) n l r) pid p
  have hdev : w'.dev = some installed := by rw [hkernel]
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨finalAmbient, he⟩ := findNode_lift_run w' ambient' installed hdev (rootWidth v4) key hw hk
    ((c.plug (.node n l r)).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (rootSlot v4) hrep hvalid
  refine ⟨w', ambient', installed, w', finalAmbient, hrun, hdev, ?_, Tree.insertFresh_lookup_spec hv ha hc d.nextNode pid key, rfl⟩
  change rootValue installed v4 = _ at hroot'
  rw [hroot']
  simpa only [Tree.lookupId] using he

/-- The original family wrapper increments the sequence exactly once, then
completes the exact-prefix update without allocating a node. The endpoint is
the same owner replacement and peer-list movement used by the add theorem. -/
theorem original_insert_context_exact_correct (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (family : Nat) (c : Context) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d (family == 4) = (c.plug (.node n l r)).root)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) (c.plug (.node n l r)))
    (hv : (c.plug (.node n l r)).Valid (rootWidth (family == 4)))
    (hnodup : (c.plug (.node n l r)).nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hf : c.Follows (rootWidth (family == 4)) addr cidr) (hn : n.cidr = cidr)
    (hm : prefixBits (rootWidth (family == 4)) n.cidr n.addr = prefixBits (rootWidth (family == 4)) n.cidr addr) :
    let v4 := family == 4
    let installed := exactInstalled (bumpSeq d) n.id (encode (rootWidth v4) (c.slot (rootSlot v4)) n l r) pid p
    let inserted := (c.plug (.node n l r)).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ w' ambient', ((WG.insert family addr cidr pid).run w).run ambient = .ok ((0, w'), ambient') ∧
      w' = { w with dev := some installed } ∧
      installed.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧ installed.nextNode = d.nextNode ∧
      rootValue installed v4 = inserted.tree.root ∧
      RepAt installed.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup := by
  obtain ⟨w', ambient', hrun, hkernel, hroot', hrep, hvalid, _, hnodup', _⟩ :=
    original_add_context_exact_correct { w with dev := some (bumpSeq d) } ambient
      (bumpSeq d) rfl (family == 4) c n l r addr cidr pid p hp hroot hr hv hnodup ha hc hf hn hm .empty trivial
  refine ⟨w', ambient', ?_, hkernel, rfl, rfl, hroot', hrep, hvalid, hnodup'⟩
  rw [insert_run_bump w ambient d hd family addr cidr pid]
  exact hrun

/-- Every normal return of original add at a nonempty selected root is one of:
first allocation refusal, second allocation refusal with source rollback, or
installation of the source-shaped one-node or two-node graft. The represented
input and actual root link justify traversal; the separate success theorem proves
that either successful endpoint represents the pure inserted tree. A missing or
rejected choice record may Stop and is not a normal allocation refusal. -/
theorem original_add_root_graft_endpoints (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hv : (Tree.node n l r).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr =
      prefixBits (rootWidth v4) n.cidr addr)) (result : Int)
    (hreturn : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((result, w'), ambient')) :
    (result = -ENOMEM ∧ w' = w) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) n.addr addr) ≠ cidr ∧
        w' = { w with dev := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w' = { w with dev := some (graftInstalled d v4 n.id
        (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p) }) := by
  apply case_add_root_graft_endpoints <;> assumption

/-- The rollback endpoint consumes one node identifier, restores node lookups
under whole-store freshness, and removes the allocated identifier from every
resident peer list. It preserves roots, sequence and every supplied tree
representation. No peer-list freshness or ownership is assumed, so structural
Device/TreeMap equality with the initial state is not asserted. -/
theorem original_root_graft_rollback_effects (d : WG.Device) (width addr cidr pid : Nat)
    (p : WG.Peer) (hp : d.peers[pid]? = some p) (hb : NodesBelow d)
    (family : Nat) (base : WG.Slot) (t : Tree) (hr : RepAt d.nodes family base t) :
    let rolled := graftRolledBack d width addr cidr pid p
    rolled.nextNode = d.nextNode + 1 ∧ rolled.peerAllowedips.seq = d.peerAllowedips.seq ∧
      (∀ f, rootValue rolled f = rootValue d f) ∧
      (∀ id : Nat, rolled.nodes[id]? = d.nodes[id]?) ∧
      (∀ q : Nat, rolled.peers[q]? = (d.peers[q]?).map (unlist d.nextNode)) ∧
      NodesBelow rolled ∧ RepAt rolled.nodes family base t := by
  refine ⟨?_, ?_, ?_, graftRolledBack_nodes d width addr cidr pid p hb,
    graftRolledBack_peer d width addr cidr pid p hp,
    graftRolledBack_below d width addr cidr pid p hb,
    graftRolledBack_rep d width addr cidr pid p hb t family base hr⟩
  · simp only [graftRolledBack, unlisted, graftListed, allocated]
  · simp only [graftRolledBack, unlisted, graftListed, allocated]
  · intro f
    simp only [graftRolledBack, unlisted, graftListed, allocated, rootValue]

/-- The original family wrapper increments the sequence before grafting. Every
normal endpoint retains that increment, including either allocation refusal.
Success endpoints are exact source updates. The separate success theorem gives
pure-tree refinement; the later initialized contracts supply configuration
history composition. -/
theorem original_insert_root_graft_endpoints (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (family : Nat) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d (family == 4) = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) (.node n l r))
    (hv : (Tree.node n l r).Valid (rootWidth (family == 4)))
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth (family == 4)) n.cidr n.addr =
      prefixBits (rootWidth (family == 4)) n.cidr addr)) (result : Int)
    (hreturn : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((result, w'), ambient')) :
    let v4 := family == 4
    ∃ d', w' = { w with dev := some d' } ∧ d'.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧
      ((result = -ENOMEM ∧ d' = bumpSeq d) ∨
        (result = -ENOMEM ∧ min cidr (common (rootWidth v4) n.addr addr) ≠ cidr ∧
          d' = graftRolledBack (bumpSeq d) (rootWidth v4) addr cidr pid p) ∨
        (result = 0 ∧ d' = graftInstalled (bumpSeq d) v4 n.id
          (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p)) := by
  rw [insert_run_bump w ambient d hd family addr cidr pid] at hreturn
  have outcome := original_add_root_graft_endpoints
    { w with dev := some (bumpSeq d) } w' ambient ambient' (bumpSeq d) rfl
    (family == 4) n l r addr cidr pid p hp hroot hb hr hv ha hc hstop result hreturn
  rcases outcome with hf | hf | hs
  · exact ⟨bumpSeq d, hf.2, rfl, .inl ⟨hf.1, rfl⟩⟩
  · exact ⟨_, hf.2.2, rfl, .inr (.inl ⟨hf.1, hf.2.1, rfl⟩)⟩
  · exact ⟨_, hs.2, (graftInstalled_metadata (bumpSeq d) (family == 4) n.id
      (encode (rootWidth (family == 4)) (rootSlot (family == 4)) n l r) addr cidr pid p).2.2.2,
      .inr (.inr ⟨hs.1, rfl⟩)⟩

/-- A successful original add stopped before a nonempty selected root represents
exactly the existing pure insertion result, for IPv4 or IPv6. Its actual root
link, local validity, duplicate-free node identifiers, whole-store allocation
bound and a supplied opposite-family representation are preserved. Compression
is preserved when present initially. Owners may be absent from the peer store;
only the target peer must be resident. This is one insertion case, not a general
configuration-history or packet-admission theorem. -/
theorem original_add_root_graft_correct (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup)
    (hv : (Tree.node n l r).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr =
      prefixBits (rootWidth v4) n.cidr addr))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other)
    (hreturn : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((0, w'), ambient')) :
    let inserted := (Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    let installed := graftInstalled d v4 n.id (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p
    w' = { w with dev := some installed } ∧ NodesBelow installed ∧
      rootValue installed v4 = inserted.tree.root ∧
      RepAt installed.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧
      ((Tree.node n l r).Compressed → inserted.tree.Compressed) ∧
      installed.nextNode = d.nextNode + inserted.allocations ∧
      rootValue installed (!v4) = rootValue d (!v4) ∧
      installed.peerAllowedips.seq = d.peerAllowedips.seq ∧
      RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other := by
  apply case_add_root_graft_correct <;> assumption

/-- Following a successful original selected-root graft, original findNode starts
at the actual resulting device root, terminates, and returns a longest-prefix
winner in the independently updated flat binding list. The result retains raw
owner labels and does not assert their lifetime or packet-admission properties. -/
theorem original_add_root_graft_lookup (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup)
    (hv : (Tree.node n l r).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr =
      prefixBits (rootWidth v4) n.cidr addr)) (key : Nat) (hk : key < 2 ^ rootWidth v4)
    (hreturn : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((0, w'), ambient')) :
    let old := Tree.node n l r
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ d' final finalAmbient, w'.dev = some d' ∧
      ((WG.liftAip (WG.findNode (rootValue d' v4) (rootWidth v4) key)).run w').run ambient' =
        .ok (((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final), finalAmbient) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: old.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final = w' := by
  obtain ⟨hkernel, _, hroot', hrep, hvalid, _⟩ := original_add_root_graft_correct
    w w' ambient ambient' d hd v4 n l r addr cidr pid p hp hroot hb hr hn hv ha hc hstop .empty trivial hreturn
  have hdev : w'.dev = some (graftInstalled d v4 n.id
      (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p) := by rw [hkernel]
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨finalAmbient, he⟩ := findNode_lift_run w' ambient' _ hdev (rootWidth v4) key hw hk
    ((Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (rootSlot v4) hrep hvalid
  refine ⟨_, w', finalAmbient, hdev, ?_, Tree.insertFresh_lookup_spec hv ha hc d.nextNode pid key, rfl⟩
  simpa only [hroot', Tree.lookupId] using he

/-- A successful original configuration insert that grafts before the nonempty
selected root increments the sequence once, implements pure insertion with its
exact allocation count, and preserves a supplied opposite-family representation.
The premise is an actual successful original run. Both normal allocation refusals
are classified separately by the endpoint theorem. Rejected or missing records
may Stop and are outside these normal-return contracts. -/
theorem original_insert_root_graft_correct (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (family : Nat) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d (family == 4) = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup)
    (hv : (Tree.node n l r).Valid (rootWidth (family == 4)))
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth (family == 4)) n.cidr n.addr =
      prefixBits (rootWidth (family == 4)) n.cidr addr))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!(family == 4))) (rootSlot (!(family == 4))) other)
    (hreturn : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((0, w'), ambient')) :
    let v4 := family == 4
    let inserted := (Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ d', w' = { w with dev := some d' } ∧
      d'.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧ NodesBelow d' ∧
      rootValue d' v4 = inserted.tree.root ∧
      RepAt d'.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧
      ((Tree.node n l r).Compressed → inserted.tree.Compressed) ∧
      d'.nextNode = d.nextNode + inserted.allocations ∧
      rootValue d' (!v4) = rootValue d (!v4) ∧
      RepAt d'.nodes (rootWidth (!v4)) (rootSlot (!v4)) other := by
  rw [insert_run_bump w ambient d hd family addr cidr pid] at hreturn
  obtain ⟨hk, hb', hroot', hr', hv', hn', hcomp, hnext, hotherRoot, hseq, hother⟩ :=
    original_add_root_graft_correct
      { w with dev := some (bumpSeq d) } w' ambient ambient' (bumpSeq d) rfl
      (family == 4) n l r addr cidr pid p hp hroot hb hr hn hv ha hc hstop other ho hreturn
  exact ⟨_, hk, hseq, hb', hroot', hr', hv', hn', hcomp, hnext, hotherRoot, hother⟩

/-- Every normal return of original add whose placement stops at a nonempty
child below an arbitrary represented path has the exact source endpoint: first
allocation refusal, second refusal with frontier advance and all-peer filtering,
or the installed child graft. Missing/rejected records can Stop and are outside
this normal-return classification. Existing node owners need not be resident;
the requested target peer is resident, and no peer-list coherence is assumed. -/
theorem original_add_context_graft_endpoints (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (v4 : Bool) (c : Context) (parent : NodeData) (side : Nat) (sibling : Tree)
    (n : NodeData) (l r : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (Tree.fork parent side (.node n l r) sibling)).root)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork parent side (.node n l r) sibling)))
    (hv : (c.plug (Tree.fork parent side (.node n l r) sibling)).Valid (rootWidth v4))
    (hn : (c.plug (Tree.fork parent side (.node n l r) sibling)).nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hlt : parent.cidr < cidr)
    (hm : prefixBits (rootWidth v4) parent.cidr parent.addr = prefixBits (rootWidth v4) parent.cidr addr)
    (hbit : bit (rootWidth v4) parent.cidr addr = side)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr))
    (ret : Int) (hreturn : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((ret, w'), ambient')) :
    (ret = -ENOMEM ∧ w' = w) ∨
      (ret = -ENOMEM ∧ min cidr (common (rootWidth v4) n.addr addr) ≠ cidr ∧
        w' = { w with dev := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (ret = 0 ∧ w' = { w with dev := some (contextGraftInstalled d v4
        (c.slot (rootSlot v4)) parent side sibling n l r addr cidr pid p) }) := by
  apply case_add_context_graft_endpoints <;> assumption

/-- A successful original nonempty child graft at arbitrary depth implements
the existing pure insertion, with exact allocation count, both root values,
whole-store freshness and a supplied opposite-family representation preserved.
Validity and distinct node identifiers are structural input premises; orphan
owner labels are permitted. Complete configuration histories are supplied
by separate composition contracts below. -/
theorem original_add_context_graft_correct (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (v4 : Bool) (c : Context) (parent : NodeData) (side : Nat) (sibling : Tree)
    (n : NodeData) (l r : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (Tree.fork parent side (.node n l r) sibling)).root)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork parent side (.node n l r) sibling)))
    (hv : (c.plug (Tree.fork parent side (.node n l r) sibling)).Valid (rootWidth v4))
    (hn : (c.plug (Tree.fork parent side (.node n l r) sibling)).nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hlt : parent.cidr < cidr)
    (hm : prefixBits (rootWidth v4) parent.cidr parent.addr = prefixBits (rootWidth v4) parent.cidr addr)
    (hbit : bit (rootWidth v4) parent.cidr addr = side)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other)
    (hreturn : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((0, w'), ambient')) :
    let old := c.plug (Tree.fork parent side (.node n l r) sibling)
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    let installed := contextGraftInstalled d v4 (c.slot (rootSlot v4)) parent side sibling n l r addr cidr pid p
    w' = { w with dev := some installed } ∧ NodesBelow installed ∧
      rootValue installed v4 = inserted.tree.root ∧
      RepAt installed.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧
      (old.Compressed → inserted.tree.Compressed) ∧
      installed.nextNode = d.nextNode + inserted.allocations ∧
      rootValue installed (!v4) = rootValue d (!v4) ∧
      installed.peerAllowedips.seq = d.peerAllowedips.seq ∧
      RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other := by
  apply case_add_context_graft_correct <;> assumption

/-- After an actual successful deep child graft, original findNode from the
resulting device root terminates with a longest-prefix winner for the independently
updated flat bindings. This is raw owner-label routing, not owner lifetime or
packet-delivery authorization. -/
theorem original_add_context_graft_lookup (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (v4 : Bool) (c : Context) (parent : NodeData) (side : Nat) (sibling : Tree)
    (n : NodeData) (l r : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (Tree.fork parent side (.node n l r) sibling)).root)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork parent side (.node n l r) sibling)))
    (hv : (c.plug (Tree.fork parent side (.node n l r) sibling)).Valid (rootWidth v4))
    (hn : (c.plug (Tree.fork parent side (.node n l r) sibling)).nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hlt : parent.cidr < cidr)
    (hm : prefixBits (rootWidth v4) parent.cidr parent.addr = prefixBits (rootWidth v4) parent.cidr addr)
    (hbit : bit (rootWidth v4) parent.cidr addr = side)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr))
    (key : Nat) (hk : key < 2 ^ rootWidth v4)
    (hreturn : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((0, w'), ambient')) :
    let old := c.plug (Tree.fork parent side (.node n l r) sibling)
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ d' final finalAmbient, w'.dev = some d' ∧
      ((WG.liftAip (WG.findNode (rootValue d' v4) (rootWidth v4) key)).run w').run ambient' =
        .ok (((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final), finalAmbient) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: old.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final = w' := by
  obtain ⟨hkernel, _, hroot', hrep, hvalid, _⟩ := original_add_context_graft_correct
    w w' ambient ambient' d hd v4 c parent side sibling n l r addr cidr pid p hp hroot hb hbelow hr hv hn ha hc hf hlt hm hbit hstop .empty trivial hreturn
  have hdev : w'.dev = some (contextGraftInstalled d v4
      (c.slot (rootSlot v4)) parent side sibling n l r addr cidr pid p) := by rw [hkernel]
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨finalAmbient, he⟩ := findNode_lift_run w' ambient' _ hdev (rootWidth v4) key hw hk
    ((c.plug (Tree.fork parent side (.node n l r) sibling)).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (rootSlot v4) hrep hvalid
  refine ⟨_, w', finalAmbient, hdev, ?_, Tree.insertFresh_lookup_spec hv ha hc d.nextNode pid key, rfl⟩
  simpa only [hroot', Tree.lookupId] using he

/-- Original insert below an arbitrary represented path has the same successful
graft refinement and advances the allowed-IP sequence once. The run premise is
original normal success; records that Stop are not classified as allocation refusals. -/
theorem original_insert_context_graft_correct (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (family : Nat) (c : Context) (parent : NodeData) (side : Nat) (sibling : Tree)
    (n : NodeData) (l r : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p)
    (hroot : rootValue d (family == 4) = (c.plug (Tree.fork parent side (.node n l r) sibling)).root)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) (c.plug (Tree.fork parent side (.node n l r) sibling)))
    (hv : (c.plug (Tree.fork parent side (.node n l r) sibling)).Valid (rootWidth (family == 4)))
    (hn : (c.plug (Tree.fork parent side (.node n l r) sibling)).nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hf : c.Follows (rootWidth (family == 4)) addr cidr) (hlt : parent.cidr < cidr)
    (hm : prefixBits (rootWidth (family == 4)) parent.cidr parent.addr = prefixBits (rootWidth (family == 4)) parent.cidr addr)
    (hbit : bit (rootWidth (family == 4)) parent.cidr addr = side)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth (family == 4)) n.cidr n.addr = prefixBits (rootWidth (family == 4)) n.cidr addr))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!(family == 4))) (rootSlot (!(family == 4))) other)
    (hreturn : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((0, w'), ambient')) :
    let v4 := family == 4
    let old := c.plug (Tree.fork parent side (.node n l r) sibling)
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ d', w' = { w with dev := some d' } ∧
      d'.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧ NodesBelow d' ∧
      rootValue d' v4 = inserted.tree.root ∧
      RepAt d'.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧
      (old.Compressed → inserted.tree.Compressed) ∧
      d'.nextNode = d.nextNode + inserted.allocations ∧
      rootValue d' (!v4) = rootValue d (!v4) ∧
      RepAt d'.nodes (rootWidth (!v4)) (rootSlot (!v4)) other := by
  rw [insert_run_bump w ambient d hd family addr cidr pid] at hreturn
  obtain ⟨hk, hb', hroot', hr', hv', hn', hcomp, hnext, hotherRoot, hseq, hother⟩ :=
    original_add_context_graft_correct
      { w with dev := some (bumpSeq d) } w' ambient ambient' (bumpSeq d) rfl
      (family == 4) c parent side sibling n l r addr cidr pid p hp hroot hb hbelow hr hv hn ha hc hf hlt hm hbit hstop other ho hreturn
  exact ⟨_, hk, hseq, hb', hroot', hr', hv', hn', hcomp, hnext, hotherRoot, hother⟩

/-- Every normal original add return on a represented IPv4/IPv6 tree is
classified without caller-supplied placement/path premises. First refusal leaves
WGWorld unchanged; second refusal retains the exact rollback device, one
consumed node identifier and peer-list filtering. Success supplies the common
structural pure-insertion consequences in Inserted, not a unified exact Device
update. Old owner labels may be orphaned; the requested target peer is resident.
Missing/rejected records may Stop and are outside this normal-return claim. -/
theorem original_add_all_cases (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (v4 : Bool) (t other : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d v4 = t.root)
    (hbelow : NodesBelow d) (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (hv : t.Valid (rootWidth v4)) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (ret : Int)
    (hrun : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((ret, w'), ambient')) :
    AddOutcome w w' d v4 t other addr cidr pid p ret := by
  apply add_outcome <;> assumption

/-- Either normal allocator refusal preserves every node lookup and both
root values. Its frontier/peer-map effects are exactly unchanged values or one
consumed identifier with all-peer filtering of that identifier. No peer-list
freshness, structural TreeMap equality, or full-World rollback is asserted. -/
theorem original_add_allocation_refusal (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (v4 : Bool) (t : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d v4 = t.root)
    (hbelow : NodesBelow d) (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (hv : t.Valid (rootWidth v4)) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hrun : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient = .ok ((-ENOMEM, w'), ambient')) :
    ∃ out, w' = { w with dev := some out } ∧ NodesBelow out ∧
      out.peerAllowedips.seq = d.peerAllowedips.seq ∧
      (∀ f, rootValue out f = rootValue d f) ∧
      (∀ id : Nat, out.nodes[id]? = d.nodes[id]?) ∧
      ((out.nextNode = d.nextNode ∧ ∀ q : Nat, out.peers[q]? = d.peers[q]?) ∨
        (out.nextNode = d.nextNode + 1 ∧
          (t.insertFresh (rootWidth v4) d.nextNode addr cidr pid).allocations = 2 ∧
          ∀ q : Nat, out.peers[q]? = (d.peers[q]?).map (unlist d.nextNode))) := by
  apply add_refusal <;> assumption

/-- Original insert advances the sequence before add and retains that
advance in every normal branch. The outcome classifier derives all placement
cases from the represented input and preserves the distinction between first
refusal and second-allocation rollback. Family 4 selects IPv4; other family
values follow the original IPv6 arm. Record Stops remain possible. -/
theorem original_insert_all_cases (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (family : Nat) (t other : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d (family == 4) = t.root)
    (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) t)
    (hv : t.Valid (rootWidth (family == 4))) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (ho : RepAt d.nodes (rootWidth (!(family == 4))) (rootSlot (!(family == 4))) other)
    (ret : Int) (hrun : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((ret, w'), ambient')) :
    AddOutcome { w with dev := some (bumpSeq d) } w' (bumpSeq d) (family == 4)
      t other addr cidr pid p ret := by
  apply insert_outcome <;> assumption

/-- Any actual original insert return of zero represents the one existing
pure insertion algorithm, with exact allocation count, sequence increment,
validity, distinct node identifiers and conditional compression. The actual
selected root is linked to that tree; the opposite root value and any supplied
opposite-family RepAt are preserved. The latter relation does not itself assert
that the supplied tree was linked to the opposite root. No configuration-history,
peer-list coherence, old-owner residency or packet-path premise is inferred. -/
theorem original_insert_success (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (family : Nat) (t other : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d (family == 4) = t.root)
    (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) t)
    (hv : t.Valid (rootWidth (family == 4))) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (ho : RepAt d.nodes (rootWidth (!(family == 4))) (rootSlot (!(family == 4))) other)
    (hrun : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((0, w'), ambient')) :
    let inserted := t.insertFresh (rootWidth (family == 4)) d.nextNode addr cidr pid
    ∃ out, w' = { w with dev := some out } ∧
      out.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧
      Inserted (bumpSeq d) out (family == 4) t other addr cidr pid ∧
      inserted.tree.Valid (rootWidth (family == 4)) ∧ inserted.tree.nodeIds.Nodup ∧
      (t.Compressed → inserted.tree.Compressed) := by
  apply insert_success <;> assumption

/-- After any successful original insert on a represented tree, original
findNode from the resulting device's actual selected root terminates and returns
a longest-prefix winner for independently updated canonical flat bindings.
All insertion cases are derived internally. Owners remain raw peer labels;
this is neither owner-lifetime safety nor packet-path authorization. -/
theorem original_insert_longest_prefix (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (family : Nat) (t : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d (family == 4) = t.root)
    (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) t)
    (hv : t.Valid (rootWidth (family == 4))) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (key : Nat) (hk : key < 2 ^ rootWidth (family == 4))
    (hrun : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((0, w'), ambient')) :
    let v4 := family == 4
    let inserted := t.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ out final finalAmbient, w'.dev = some out ∧
      ((WG.liftAip (WG.findNode (rootValue out v4) (rootWidth v4) key)).run w').run ambient' =
        .ok (((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final), finalAmbient) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: t.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final = w' := by
  apply insert_lookup <;> assumption

/-- Pure removal filters exactly the owned entries with the requested node ID,
retaining order and multiplicity. On a valid tree its lookup is a longest-prefix
winner for that independently filtered list. This is not yet an original
removeByPeer execution or peer-owner history theorem. -/
theorem pure_removal_entries_and_lookup (t : Tree) (id width key : Nat)
    (hv : t.Valid width) :
    (t.eraseId id).entries = t.entries.filter (fun e => e.id != id) ∧
      Winner width key (t.entries.filter (fun e => e.id != id))
        ((t.eraseId id).lookup width key) :=
  ⟨Tree.eraseId_entries t id, Tree.eraseId_lookup_spec hv id key⟩

/-- Pure removal preserves local prefix validity and yields a compressed tree.
Its node-ID list is a subsequence of the input, so uniqueness and every input ID
bound are preserved. No input compression, owner residency or fresh allocation
premise is required here. -/
theorem pure_removal_structure (t : Tree) (id width : Nat)
    (hv : t.Valid width) (hn : t.nodeIds.Nodup) :
    (t.eraseId id).Valid width ∧ (t.eraseId id).Compressed ∧
      (t.eraseId id).nodeIds.Sublist t.nodeIds ∧ (t.eraseId id).nodeIds.Nodup ∧
      ∀ frontier, (∀ j ∈ t.nodeIds, j < frontier) →
        ∀ j ∈ (t.eraseId id).nodeIds, j < frontier :=
  ⟨Tree.eraseId_valid hv id, Tree.eraseId_compressed t id,
    Tree.eraseId_nodeIds t id, Tree.eraseId_nodup hn id,
    fun _ hb => Tree.eraseId_bounded hb id⟩

/-- An absent identifier leaves a compressed input exactly unchanged.
Compression is essential: arbitrary malformed ownerless unary nodes are
normalized by the pure operation. -/
theorem pure_removal_absent (t : Tree) (id : Nat) (hc : t.Compressed)
    (hi : id ∉ t.nodeIds) : t.eraseId id = t :=
  Tree.eraseId_absent hc hi

/-- On a compressed tree with distinct node identifiers, one erasure removes
at most two IDs. The whole result is empty only for an empty input or a targeted
leaf. A binary target retains its node ID after its ownership is cleared.
These are pure structural laws, not original deallocation-event counts. -/
theorem pure_removal_compaction_bound (t : Tree) (id : Nat)
    (hc : t.Compressed) (hn : t.nodeIds.Nodup) :
    t.nodeIds.length ≤ (t.eraseId id).nodeIds.length + 2 ∧
      (t.eraseId id = .empty ↔ t = .empty ∨
        ∃ n, t = .node n .empty .empty ∧ n.id = id) :=
  ⟨Tree.eraseId_retired_le_two hc hn id, Tree.eraseId_empty_iff hc hn id⟩

/-- A binary or unary target is changed only at its focus: ownership is
cleared and a sole child is promoted. Every outer ancestor and sibling keeps
its exact pure data. Context ID separation is derived from whole-tree Nodup. -/
theorem pure_removal_nonleaf_context (c : Context) (n : NodeData) (l r : Tree)
    (hc : (c.plug (.node n l r)).Compressed)
    (hn : (c.plug (.node n l r)).nodeIds.Nodup)
    (hchild : l.root.isSome ∨ r.root.isSome) :
    (c.plug (.node n l r)).eraseId n.id =
      c.plug (Tree.compact {n with peer := none} l r) :=
  c.eraseId_nonleaf n l r hc hn hchild

/-- A leaf's owned parent remains, with that child removed; an ownerless
parent is replaced by its nonempty sibling. No further ancestor is compacted.
This equation supplies the local shape for later source refinement, without
assuming coherent peer lists or resident old owner labels. -/
theorem pure_removal_leaf_context (c : Context) (parent n : NodeData)
    (side : Nat) (sibling : Tree)
    (hc : (c.plug (Tree.fork parent side (.node n .empty .empty) sibling)).Compressed)
    (hn : (c.plug (Tree.fork parent side (.node n .empty .empty) sibling)).nodeIds.Nodup) :
    (c.plug (Tree.fork parent side (.node n .empty .empty) sibling)).eraseId n.id =
      c.plug (if parent.peer = none then sibling else Tree.fork parent side .empty sibling) :=
  c.eraseId_leaf_parent parent n side sibling hc hn

/-- The original saved-list loop is definitionally the proof-side step loop.
This is an all-input equation, including Stops, and retains both continues. -/
theorem original_removal_source_equation (pid : Nat) :
    removeByPeerWithStep pid = WG.removeByPeer pid := removeByPeerWithStep_eq pid

/-- One original loop iteration with two nonempty child slots terminates,
filters every peer list and clears only the target owner. Child residency is
unnecessary in this arm; no saved-list coherence is inferred. -/
theorem original_removal_binary_step (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (id left right : Nat) (n : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hbits : n.bit = #[some left, some right]) :
    ∃ w' ambient', ((removeStep id).run w).run ambient = .ok ((.yield (), w'), ambient') ∧
      w' = { w with dev := some (removalCleared (unlisted d id) id n) } := by
  obtain ⟨result, w', ambient', he, hx, hk⟩ := (Leanux.Proofs.Framing.total_iff_run_ambient _ _ _).mp
    (removeStep_binary_wp w d hd id left right n hn hbits) w ambient rfl
  subst result
  exact ⟨w', ambient', he, hk⟩

/-- A leaf whose saved parent tag selects a device root terminates with that
root cleared and the target freed. The input root need not point at the target;
this raw endpoint is not a whole-tree selection or configuration-history claim. -/
theorem original_removal_root_leaf_step (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (v4 : Bool) (id : Nat) (n : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hbits : n.bit = #[none, none])
    (hparent : n.parent = rootSlot v4) :
    ∃ w' ambient', ((removeStep id).run w).run ambient = .ok ((.yield (), w'), ambient') ∧
      w' = { w with dev := some (removalRootLeaf (unlisted d id) v4 id n) } := by
  obtain ⟨result, w', ambient', he, hx, hk⟩ := (Leanux.Proofs.Framing.total_iff_run_ambient _ _ _).mp
    (removeStep_root_leaf_wp w d hd v4 id n hn hbits hparent) w ambient rfl
  subst result
  exact ⟨w', ambient', he, hk⟩

/-- A root-tagged unary target terminates when its distinct child is resident.
The exact endpoint promotes that child and changes only its backlink. Owners
remain raw labels, including any orphan labels. -/
theorem original_removal_root_unary_step (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (v4 left : Bool) (id child : Nat) (n cn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hc : d.nodes[child]? = some cn) (hne : id ≠ child)
    (hbits : n.bit = if left then #[some child, none] else #[none, some child])
    (hparent : n.parent = rootSlot v4) :
    ∃ w' ambient', ((removeStep id).run w).run ambient = .ok ((.yield (), w'), ambient') ∧
      w' = { w with dev := some (removalRootUnary (unlisted d id) v4 id n child cn) } := by
  obtain ⟨result, w', ambient', he, hx, hk⟩ := (Leanux.Proofs.Framing.total_iff_run_ambient _ _ _).mp
    (removeStep_root_unary_wp w d hd v4 left id child n cn hn hc hne hbits hparent) w ambient rfl
  subst result
  exact ⟨w', ambient', he, hk⟩

/-- Pointwise equations describe the entire resulting node map, including
unrelated resident nodes, the retired target and the promoted child's backlink. -/
theorem local_removal_node_store (d : WG.Device) (v4 : Bool) (id child : Nat)
    (n cn : WG.AipNode) (q : Nat) :
    (removalCleared d id n).nodes[q]? =
      (if id = q then some {n with peer := none} else d.nodes[q]?) ∧
    (removalRootLeaf d v4 id n).nodes[q]? =
      (if id = q then none else d.nodes[q]?) ∧
    (removalRootUnary d v4 id n child cn).nodes[q]? =
      (if id = q then none else if child = q then
        some {cn with parent := rootSlot v4} else d.nodes[q]?) :=
  ⟨removalCleared_node .., removalRootLeaf_node .., removalRootUnary_node ..⟩

/-- Both root-tagged endpoints retain the frontier, opposite root and sequence
and implement pointwise filtering of every resident peer's allowed-IP list. -/
theorem local_removal_root_metadata (d : WG.Device) (v4 : Bool) (id child : Nat)
    (n cn : WG.AipNode) :
    let leaf := removalRootLeaf (unlisted d id) v4 id n
    let unary := removalRootUnary (unlisted d id) v4 id n child cn
    (leaf.nextNode = d.nextNode ∧ rootValue leaf v4 = none ∧
      rootValue leaf (!v4) = rootValue d (!v4) ∧
      leaf.peerAllowedips.seq = d.peerAllowedips.seq ∧
      ∀ q : Nat, leaf.peers[q]? = (d.peers[q]?).map (unlist id)) ∧
    (unary.nextNode = d.nextNode ∧ rootValue unary v4 = some child ∧
      rootValue unary (!v4) = rootValue d (!v4) ∧
      unary.peerAllowedips.seq = d.peerAllowedips.seq ∧
      ∀ q : Nat, unary.peers[q]? = (d.peers[q]?).map (unlist id)) :=
  ⟨removalRootLeaf_metadata .., removalRootUnary_metadata ..⟩

/-- Binary owner clearing represents pure ID erasure under compression and
unique IDs. Neither old-owner residency nor peer-list coherence is required. -/
theorem local_removal_binary_representation (d : WG.Device) (width : Nat)
    (base : WG.Slot) (n : NodeData) (l r : Tree)
    (hr : RepAt d.nodes width base (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup) (hc : (Tree.node n l r).Compressed)
    (hl : l.root.isSome) (hh : r.root.isSome) :
    RepAt (removalCleared d n.id (encode width base n l r)).nodes width base
      ((Tree.node n l r).eraseId n.id) := by
  rw [Tree.eraseId_binary hc hn hl hh]
  exact removalCleared_rep d width base n l r hr hn

/-- The root-unary endpoint represents its promoted subtree, with separation
of the retired parent and child descendants derived from tree uniqueness.
This structural transport is separate from selection of the original root. -/
theorem local_removal_unary_representation (d : WG.Device) (v4 : Bool) (n c : NodeData)
    (l r : Tree) (left : Bool)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4)
      (if left then .node n (.node c l r) .empty else .node n .empty (.node c l r)))
    (hn : (if left then Tree.node n (.node c l r) .empty
      else Tree.node n .empty (.node c l r)).nodeIds.Nodup) :
    let t := Tree.node c l r
    let old := encode (rootWidth v4) (rootSlot v4) n
      (if left then t else .empty) (if left then .empty else t)
    let child := encode (rootWidth v4) (.child n.id (if left then 0 else 1)) c l r
    RepAt (removalRootUnary d v4 n.id old c.id child).nodes
      (rootWidth v4) (rootSlot v4) t :=
  removalRootUnary_rep d v4 n c l r left hr hn

/-- The leaf/ownerless-parent prefix reaches the exact post-target-free
continuation. This equation keeps later missing-sibling/grandparent Stops;
no successful-tail premise or failed-prefix World is assumed. -/
theorem original_removal_collapse_continuation (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (id parent side : Nat) (n pn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hip : id ≠ parent) (hb : side ≤ 1) (howner : pn.peer = none)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = .child parent side)
    (sibling : Option Nat) (hs : pn.bit[1-side]? = some sibling) :
    ((removeNodeBody id).run w).run ambient =
      ((removeParentTail parent sibling).run
        { w with dev := some (removalLeafDetached d id n parent side pn) }).run
          (removalRecords ambient removalCollapseRecords) :=
  removeNodeBody_leaf_collapse_run w ambient d hd id parent side n pn hn hp hip hb howner hbits hparent sibling hs

/-- Original nonroot unary removal is total under resident, distinct input
snapshots and a valid parent-slot index. The raw endpoint does not require
parent linkage, parent array length, owner residency or list coherence. -/
theorem original_removal_child_unary_step (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (left : Bool) (id parent side child : Nat) (n pn cn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hc : d.nodes[child]? = some cn) (hip : id ≠ parent) (hic : id ≠ child)
    (hcp : child ≠ parent) (hb : side ≤ 1)
    (hbits : n.bit = if left then #[some child, none] else #[none, some child])
    (hparent : n.parent = .child parent side) :
    ∃ w' ambient', ((removeStep id).run w).run ambient = .ok ((.yield (), w'), ambient') ∧
      w' = { w with dev := some (removalChildUnary (unlisted d id) id n parent side pn child cn) } := by
  obtain ⟨result, w', ambient', he, hx, hk⟩ := (Leanux.Proofs.Framing.total_iff_run_ambient _ _ _).mp
    (removeStep_child_unary_wp w d hd left id parent side child n pn cn hn hp hc hip hic hcp hb hbits hparent) w ambient rfl
  subst result
  exact ⟨w', ambient', he, hk⟩

/-- The leaf's owned parent is reread after detachment and retained. Its
raw owner label need not resolve to a resident peer. Every list is filtered
before the target getter; both device roots remain unchanged. -/
theorem original_removal_child_leaf_step (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (id parent side : Nat) (n pn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hip : id ≠ parent) (hb : side ≤ 1) (howner : pn.peer.isSome)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = .child parent side) :
    ∃ w' ambient', ((removeStep id).run w).run ambient = .ok ((.yield (), w'), ambient') ∧
      w' = { w with dev := some (removalLeafDetached (unlisted d id) id n parent side pn) } := by
  obtain ⟨result, w', ambient', he, hx, hk⟩ := (Leanux.Proofs.Framing.total_iff_run_ambient _ _ _).mp
    (removeStep_child_leaf_owned_wp w d hd id parent side n pn hn hp hip hb howner hbits hparent) w ambient rfl
  subst result
  exact ⟨w', ambient', he, hk⟩

/-- An ownerless parent with a root tag is collapsed after target retirement.
Both sibling-present and sibling-absent paths are included. The tag does not
assert that the input root points to the parent. -/
theorem original_removal_collapse_root_step (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (id parent side : Nat) (n pn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hip : id ≠ parent) (hb : side ≤ 1) (howner : pn.peer = none)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = .child parent side)
    (v4 : Bool) (hbase : pn.parent = rootSlot v4) (sibling : Option (Nat × WG.AipNode))
    (hbit : pn.bit[1-side]? = some (sibling.map Prod.fst))
    (hs : ∀ c cn, sibling = some (c, cn) → d.nodes[c]? = some cn ∧ c ≠ id ∧ c ≠ parent) :
    ∃ w' ambient', ((removeStep id).run w).run ambient = .ok ((.yield (), w'), ambient') ∧
      w' = { w with dev := some (removalCollapseRoot (unlisted d id) id n parent side pn v4 sibling) } := by
  obtain ⟨result, w', ambient', he, hx, hk⟩ := (Leanux.Proofs.Framing.total_iff_run_ambient _ _ _).mp
    (removeStep_leaf_collapse_root_wp w d hd id parent side n pn hn hp hip hb howner hbits hparent
      v4 hbase sibling hbit hs) w ambient rfl
  subst result
  exact ⟨w', ambient', he, hk⟩

/-- Collapse below a resident grandparent retains the actual reread/update
order and the original array write. Input separation prevents intervening
writes/frees from invalidating supplied snapshots; no final effect is a premise. -/
theorem original_removal_collapse_child_step (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (id parent side grand gside : Nat) (n pn gn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hp : d.nodes[parent]? = some pn)
    (hg : d.nodes[grand]? = some gn) (hip : id ≠ parent) (hig : id ≠ grand)
    (hpg : parent ≠ grand) (hb : side ≤ 1) (hgb : gside ≤ 1) (howner : pn.peer = none)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = .child parent side)
    (hbase : pn.parent = .child grand gside) (sibling : Option (Nat × WG.AipNode))
    (hbit : pn.bit[1-side]? = some (sibling.map Prod.fst))
    (hs : ∀ c cn, sibling = some (c, cn) →
      d.nodes[c]? = some cn ∧ c ≠ id ∧ c ≠ parent ∧ c ≠ grand) :
    ∃ w' ambient', ((removeStep id).run w).run ambient = .ok ((.yield (), w'), ambient') ∧
      w' = { w with dev := some (removalCollapseChild (unlisted d id) id n parent side pn grand gside gn sibling) } := by
  obtain ⟨result, w', ambient', he, hx, hk⟩ := (Leanux.Proofs.Framing.total_iff_run_ambient _ _ _).mp
    (removeStep_leaf_collapse_child_wp w d hd id parent side grand gside n pn gn hn hp hg hip hig hpg
      hb hgb howner hbits hparent hbase sibling hbit hs) w ambient rfl
  subst result
  exact ⟨w', ambient', he, hk⟩

/-- Exact pointwise node effects for retained-parent arms. Conditional order
matches source writes even for aliased arguments to these endpoint functions. -/
theorem nonroot_removal_node_store (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (child : Nat) (cn : WG.AipNode) (q : Nat) :
    (removalChildUnary d id n parent side pn child cn).nodes[q]? =
      (if id = q then none else if parent = q then
        some { pn with bit := pn.bit.set! side (some child) } else if child = q then
        some { cn with parent := .child parent side } else d.nodes[q]?) ∧
    (removalLeafDetached d id n parent side pn).nodes[q]? =
      (if id = q then none else if parent = q then
        some { pn with bit := pn.bit.set! side none } else d.nodes[q]?) :=
  ⟨removalChildUnary_node .., removalLeafDetached_node ..⟩

/-- Whole-store equations retain the parent-free, grandparent-write and
sibling-write priorities. The execution contracts above supply the separation
under which both target and parent are retired. -/
theorem collapse_removal_node_store (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (v4 : Bool) (grand gside : Nat) (gn : WG.AipNode)
    (sibling : Option (Nat × WG.AipNode)) (q : Nat) :
    (removalCollapseRoot d id n parent side pn v4 sibling).nodes[q]? =
      (if parent = q then none else
        match sibling with
        | none => if id = q then none else d.nodes[q]?
        | some (c, cn) => if c = q then some { cn with parent := rootSlot v4 }
            else if id = q then none else d.nodes[q]?) ∧
    (removalCollapseChild d id n parent side pn grand gside gn sibling).nodes[q]? =
      (if parent = q then none else if grand = q then
        some { gn with bit := gn.bit.set! gside (sibling.map Prod.fst) } else
        match sibling with
        | none => if id = q then none else d.nodes[q]?
        | some (c, cn) => if c = q then some { cn with parent := .child grand gside }
            else if id = q then none else d.nodes[q]?) :=
  ⟨removalCollapseRoot_node .., removalCollapseChild_node ..⟩

/-- Retained-parent endpoints preserve both family roots, the allocation
frontier and sequence, and filter every peer list at the target ID. -/
theorem nonroot_removal_metadata (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (child : Nat) (cn : WG.AipNode) :
    (let out := removalChildUnary (unlisted d id) id n parent side pn child cn
     RemovalMetadata d out id ∧ ∀ v4, rootValue out v4 = rootValue d v4) ∧
    (let out := removalLeafDetached (unlisted d id) id n parent side pn
     RemovalMetadata d out id ∧ ∀ v4, rootValue out v4 = rootValue d v4) :=
  ⟨removalChildUnary_metadata .., removalLeafDetached_metadata ..⟩

/-- Root collapse changes only its selected root; child collapse preserves
both roots. Neither allocates nor increments sequence, and list filtering is
exact. The enclosing peer-removal loop's increment remains separate. -/
theorem collapse_removal_metadata (d : WG.Device) (id : Nat) (n : WG.AipNode)
    (parent side : Nat) (pn : WG.AipNode) (v4 : Bool) (grand gside : Nat) (gn : WG.AipNode)
    (sibling : Option (Nat × WG.AipNode)) :
    (let out := removalCollapseRoot (unlisted d id) id n parent side pn v4 sibling
     RemovalMetadata d out id ∧ rootValue out v4 = sibling.map Prod.fst ∧
       rootValue out (!v4) = rootValue d (!v4)) ∧
    (let out := removalCollapseChild (unlisted d id) id n parent side pn grand gside gn sibling
     RemovalMetadata d out id ∧ ∀ v4, rootValue out v4 = rootValue d v4) :=
  ⟨removalCollapseRoot_metadata .., removalCollapseChild_metadata ..⟩

/-- One iteration factored from original removeByPeer completes for every
represented target ID. Forest representation, compression and distinct IDs
derive all seven source cases, including actual roots and parent links.
The full WGWorld endpoint represents eraseId in both families, filters every
resident peer list, preserves sequence/frontier and other fields, erases all
retired represented IDs, and frames nodes outside the original forest. No
owner residency, saved-list coherence or absent-target no-op is assumed. -/
theorem original_removeStep_forest_total (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (t4 t6 : Tree) (id : Nat) (hf : ForestRep d t4 t6)
    (hn4 : t4.nodeIds.Nodup) (hn6 : t6.nodeIds.Nodup)
    (hc4 : t4.Compressed) (hc6 : t6.Compressed)
    (hi : id ∈ t4.nodeIds ++ t6.nodeIds) :
    ∃ out w' ambient', ((removeStep id).run w).run ambient = .ok ((.yield (), w'), ambient') ∧
      w' = {w with dev := some out} ∧ RemovedForest d out t4 t6 id :=
  remove_forest_total w ambient d hd t4 t6 id hf hn4 hn6 hc4 hc6 hi

/-- Every returned original step has the same represented endpoint. With
valid input prefixes, both resulting trees remain valid, compressed and
duplicate-free; their IDs are sublists and their ordered entries are exactly
filtered by the target ID. This concerns one iteration, not the enclosing
loop's sequence increment or a history of peer removals. -/
theorem original_removeStep_forest_properties (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (t4 t6 : Tree) (id : Nat) (hf : ForestRep d t4 t6)
    (hn4 : t4.nodeIds.Nodup) (hn6 : t6.nodeIds.Nodup)
    (hc4 : t4.Compressed) (hc6 : t6.Compressed)
    (hv4 : t4.Valid 32) (hv6 : t6.Valid 128)
    (hi : id ∈ t4.nodeIds ++ t6.nodeIds) (result : ForInStep PUnit)
    (hrun : ((removeStep id).run w).run ambient = .ok ((result, w'), ambient')) :
    result = .yield () ∧ (∃ out, w' = {w with dev := some out} ∧ RemovedForest d out t4 t6 id) ∧
      (t4.eraseId id).Valid 32 ∧ (t6.eraseId id).Valid 128 ∧
      (t4.eraseId id).Compressed ∧ (t6.eraseId id).Compressed ∧
      (t4.eraseId id).nodeIds.Nodup ∧ (t6.eraseId id).nodeIds.Nodup ∧
      (t4.eraseId id).nodeIds.Sublist t4.nodeIds ∧ (t6.eraseId id).nodeIds.Sublist t6.nodeIds ∧
      (t4.eraseId id).entries = t4.entries.filter (fun e => e.id != id) ∧
      (t6.eraseId id).entries = t6.entries.filter (fun e => e.id != id) := by
  have he := remove_forest_endpoint w w' ambient ambient' d hd t4 t6 id hf hn4 hn6 hc4 hc6 hi result hrun
  exact ⟨he.1, he.2, Tree.eraseId_valid hv4 id, Tree.eraseId_valid hv6 id,
    Tree.eraseId_compressed t4 id, Tree.eraseId_compressed t6 id,
    Tree.eraseId_nodup hn4 id, Tree.eraseId_nodup hn6 id,
    Tree.eraseId_nodeIds t4 id, Tree.eraseId_nodeIds t6 id,
    Tree.eraseId_entries t4 id, Tree.eraseId_entries t6 id⟩

/-- After the original target-removal step, original findNode at the actual
selected family root completes with the longest-prefix winner among exactly
the surviving entries. The query is bounded to its family width. Returned
owners remain raw labels; this theorem makes no packet authorization claim. -/
theorem original_removeStep_then_findNode (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (t4 t6 : Tree) (id : Nat) (hf : ForestRep d t4 t6)
    (hn4 : t4.nodeIds.Nodup) (hn6 : t6.nodeIds.Nodup)
    (hc4 : t4.Compressed) (hc6 : t6.Compressed)
    (hv4 : t4.Valid 32) (hv6 : t6.Valid 128)
    (hi : id ∈ t4.nodeIds ++ t6.nodeIds) (v4 : Bool) (key : Nat)
    (hk : key < 2 ^ rootWidth v4) :
    let t := if v4 then t4 else t6
    ∃ out after afterAmbient queryAfter queryAmbient, ((removeStep id).run w).run ambient = .ok ((.yield (), after), afterAmbient) ∧
      after = {w with dev := some out} ∧ RemovedForest d out t4 t6 id ∧
      ((WG.liftAip (WG.findNode (rootValue out v4) (rootWidth v4) key)).run after).run afterAmbient =
        .ok (((t.eraseId id).lookupId (rootWidth v4) key, queryAfter), queryAmbient) ∧
      queryAfter = after ∧
      Winner (rootWidth v4) key (t.entries.filter (fun e => e.id != id))
        ((t.eraseId id).lookup (rootWidth v4) key) := by
  obtain ⟨out, after, afterAmbient, hrun, ha, hs⟩ := remove_forest_total w ambient d hd t4 t6 id hf hn4 hn6 hc4 hc6 hi
  have hd' : after.dev = some out := by rw [ha]
  obtain ⟨queryAfter, queryAmbient, hquery, hframe, hwinner⟩ := hs.findNode after afterAmbient hd' hv4 hv6 v4 key hk
  exact ⟨out, after, afterAmbient, queryAfter, queryAmbient, hrun, ha, hs, hquery, hframe, hwinner⟩

/-- Complete original peer removal is total from represented compressed
forests and explicitly coherent resident lists. The saved target list supplies
owned membership for every original iteration; no owner-residency condition is
imposed on other entries. The result includes exact sequence/list effects,
both-family erasure, retired-ID absence, complete framing and preserved
coherence. This does not establish coherence from initialized histories. -/
theorem original_removeByPeer_forest_total (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (t4 t6 : Tree) (hf : ForestRep d t4 t6)
    (hn4 : t4.nodeIds.Nodup) (hn6 : t6.nodeIds.Nodup)
    (hc4 : t4.Compressed) (hc6 : t6.Compressed) (hl : ResidentLists d t4 t6) :
    ∃ out w' ambient', ((WG.removeByPeer pid).run w).run ambient = .ok (((), w'), ambient') ∧
      w' = {w with dev := some out} ∧ RemovedPeer d out t4 t6 pid p.allowedipsList :=
  removeByPeer_total w ambient d hd pid p hp t4 t6 hf hn4 hn6 hc4 hc6 hl

/-- The normal endpoint has an empty target list, no target-owned entries,
and exactly one sequence increment iff the saved list was nonempty. All peer
lists are filtered at the saved IDs while other peer fields are preserved.
Valid inputs retain validity, compression, distinct IDs and frontier bounds;
the outcome contract also includes outside-node and retired-node equations. -/
theorem original_removeByPeer_forest_properties (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (t4 t6 : Tree) (hf : ForestRep d t4 t6)
    (hn4 : t4.nodeIds.Nodup) (hn6 : t6.nodeIds.Nodup)
    (hc4 : t4.Compressed) (hc6 : t6.Compressed)
    (hv4 : t4.Valid 32) (hv6 : t6.Valid 128) (hl : ResidentLists d t4 t6)
    (hr : ((WG.removeByPeer pid).run w).run ambient = .ok (((), w'), ambient')) :
    let ids := p.allowedipsList
    ∃ out, w' = {w with dev := some out} ∧ RemovedPeer d out t4 t6 pid ids ∧
      out.peerAllowedips.seq = d.peerAllowedips.seq + (if ids.isEmpty then 0 else 1) ∧
      out.nextNode = d.nextNode ∧ (NodesBelow d → NodesBelow out) ∧
      out.peers[pid]? = some {p with allowedipsList := []} ∧
      (∀ q : Nat, out.peers[q]? = (d.peers[q]?).map (unlistIds ids)) ∧
      (∀ e ∈ (t4.eraseIds ids).entries ++ (t6.eraseIds ids).entries, e.peer ≠ pid) ∧
      (t4.eraseIds ids).Valid 32 ∧ (t6.eraseIds ids).Valid 128 ∧
      (t4.eraseIds ids).Compressed ∧ (t6.eraseIds ids).Compressed ∧
      (t4.eraseIds ids).nodeIds.Nodup ∧ (t6.eraseIds ids).nodeIds.Nodup ∧
      (t4.eraseIds ids).nodeIds.Sublist t4.nodeIds ∧ (t6.eraseIds ids).nodeIds.Sublist t6.nodeIds := by
  obtain ⟨out, hk, hs⟩ := removeByPeer_endpoint w w' ambient ambient' d hd pid p hp t4 t6 hf hn4 hn6 hc4 hc6 hl hr
  exact ⟨out, hk, hs, hs.seq, hs.nextNode, hs.below, hs.target_empty hp, hs.peers,
    hs.no_target_entry, Tree.eraseIds_valid _ _ hv4, Tree.eraseIds_valid _ _ hv6,
    Tree.eraseIds_compressed _ _ hc4, Tree.eraseIds_compressed _ _ hc6,
    (Tree.eraseIds_nodeIds _ _).nodup hn4, (Tree.eraseIds_nodeIds _ _).nodup hn6,
    Tree.eraseIds_nodeIds _ _, Tree.eraseIds_nodeIds _ _⟩

/-- Complete original removal followed by original findNode at its actual
family root returns the longest-prefix winner after filtering exactly the
target peer's entries. Input list coherence and bounded query/valid prefixes
are explicit; returned raw owner labels do not imply packet authorization. -/
theorem original_removeByPeer_then_findNode (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (t4 t6 : Tree) (hf : ForestRep d t4 t6)
    (hn4 : t4.nodeIds.Nodup) (hn6 : t6.nodeIds.Nodup)
    (hc4 : t4.Compressed) (hc6 : t6.Compressed)
    (hv4 : t4.Valid 32) (hv6 : t6.Valid 128) (hl : ResidentLists d t4 t6)
    (v4 : Bool) (key : Nat) (hk : key < 2 ^ rootWidth v4) :
    let t := if v4 then t4 else t6
    ∃ out after afterAmbient queryAfter queryAmbient, ((WG.removeByPeer pid).run w).run ambient = .ok (((), after), afterAmbient) ∧
      after = {w with dev := some out} ∧ RemovedPeer d out t4 t6 pid p.allowedipsList ∧
      ((WG.liftAip (WG.findNode (rootValue out v4) (rootWidth v4) key)).run after).run afterAmbient =
        .ok (((t.eraseIds p.allowedipsList).lookupId (rootWidth v4) key, queryAfter), queryAmbient) ∧
      queryAfter = after ∧
      Winner (rootWidth v4) key (t.entries.filter (fun e => e.peer != pid))
        ((t.eraseIds p.allowedipsList).lookup (rootWidth v4) key) := by
  obtain ⟨out, after, afterAmbient, hrun, ha, hs⟩ := removeByPeer_total w ambient d hd pid p hp t4 t6 hf hn4 hn6 hc4 hc6 hl
  have hd' : after.dev = some out := by rw [ha]
  obtain ⟨queryAfter, queryAmbient, hquery, hframe, hwinner⟩ := hs.findNode hf hl hp after afterAmbient hd' hv4 hv6 v4 key hk
  exact ⟨out, after, afterAmbient, queryAfter, queryAmbient, hrun, ha, hs, hquery, hframe, hwinner⟩

/-- Every bounded-input normal return of original insert preserves the combined
routing invariant through its actual success or allocation-refusal endpoint.
Input lists are explicitly coherent; raw owner labels are bounded by nextPeer,
not assumed resident. The complete WGWorld endpoint and sequence increment are
retained. Record Stops and initialized configuration histories are not covered
by a normal-return premise. Family selection is the original family == 4 test. -/
theorem original_insert_routing_preserved (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (family addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (ret : Int) (hr : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((ret, w'), ambient')) :
    ∃ out, w' = {w with dev := some out} ∧
      InsertRoutingOutcome d out (family == 4) t4 t6 addr cidr pid ret :=
  insert_routing_outcome w w' ambient ambient' d hd family addr cidr pid p hp t4 t6 hi ha hc ret hr

/-- Successful insertion exposes the exact raw peer-map effect: replacement
filters every list before target append, while fresh allocation only appends to
the target. Coherent input and frontier bounds derive fresh-ID absence and hence
the normalized move-to-tail equation. Both represented families retain validity,
compression, distinct IDs, list coherence and node/peer/owner frontier bounds. -/
theorem original_insert_coherent_peer_maps (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (family addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hr : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((0, w'), ambient')) :
    let v4 := family == 4
    let inserted := (selectedTree v4 t4 t6).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ out, w' = {w with dev := some out} ∧
      InsertRoutingOutcome d out v4 t4 t6 addr cidr pid 0 ∧
      RoutingInvariant out (insertedTree4 d v4 t4 addr cidr pid) (insertedTree6 d v4 t6 addr cidr pid) ∧
      InsertionPeers d out inserted.allocations inserted.binding.id pid ∧
      (∀ q : Nat, out.peers[q]? = (d.peers[q]?).map (insertionPeer 0 inserted.binding.id pid q)) :=
  insert_routing_success w w' ambient ambient' d hd family addr cidr pid p hp t4 t6 hi ha hc hr

/-- Either original normal allocation refusal preserves coherent node and peer
contents pointwise and both old trees. The wrapper still increments sequence;
partial graft rollback consumes one node ID. The frame preserves every other
Device field. This is not transactional rollback or a statement about a World
returned by a Stop, which the original monad does not provide. -/
theorem original_insert_refusal_coherent (w w' : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (family addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hr : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((-ENOMEM, w'), ambient')) :
    ∃ out, w' = {w with dev := some out} ∧ InsertionFrame d out ∧ InsertRefused d out t4 t6 :=
  insert_routing_refusal w w' ambient ambient' d hd family addr cidr pid p hp t4 t6 hi ha hc hr

/-- Complete original peer removal is total from the combined routing invariant
and a resident target. Its precise saved-list erasure contract additionally
preserves all routing/frontier conditions, including bounds on orphan raw owners.
The input invariant is explicit; the finite initialized history contracts below
derive it for their listed calls, without enclosing configuration closure. -/
theorem original_removeByPeer_routing_preserved (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6) :
    ∃ out w' ambient', ((WG.removeByPeer pid).run w).run ambient = .ok (((), w'), ambient') ∧
      w' = {w with dev := some out} ∧ RemovedPeer d out t4 t6 pid p.allowedipsList ∧
      RoutingInvariant out (t4.eraseIds p.allowedipsList) (t6.eraseIds p.allowedipsList) :=
  removeByPeer_routing_total w ambient d hd pid p hp t4 t6 hi

/-- Actual peer creation either normally refuses with ENOMEM and preserves the
routing projection, or returns the old peer frontier and installs an empty list
at that slot while advancing the frontier. Device/list absence remains explicit.
Initializer Stops have no returned World and are not converted to refusals. -/
theorem original_peerCreate_routing_effects (w v : WGWorld) (ambient ambient' : Ambient) (key : WG.Key) (psk : Option WG.Key)
    (result : Except Int WG.PeerId) (hr : ((WG.peerCreate key psk).run w).run ambient = .ok ((result, v), ambient')) :
    match result with
    | .error err => err = -ENOMEM ∧ routingView v = routingView w
    | .ok pid => ∃ s, routingView w = some s ∧ pid = s.peerFrontier ∧
        routingView v = some s.allocate :=
  peerCreate_routing w v ambient ambient' key psk result hr

/-- Original normal peer creation preserves both represented families, resident
list coherence and node/peer/raw-owner frontier bounds. The owner bound makes a
fresh empty peer list coherent even when older raw owners are no longer resident. -/
theorem original_peerCreate_routing_preserved (w v : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6)
    (key : WG.Key) (psk : Option WG.Key) (result : Except Int WG.PeerId)
    (hr : ((WG.peerCreate key psk).run w).run ambient = .ok ((result, v), ambient')) :
    ∃ out, v.dev = some out ∧ RoutingInvariant out t4 t6 :=
  peerCreate_routing_preserved w v ambient ambient' d hd hi key psk result hr

/-- A normal raw peerPut preserves the routing invariant and both trees, even
when it deletes a peer and leaves its raw owner labels in the trie. This is not
a reference-credit or authorization theorem, and assumes no positive refcount. -/
theorem original_peerPut_routing_preserved (w v : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6)
    (peer : Option WG.PeerId) (hr : ((WG.peerPut peer).run w).run ambient = .ok (((), v), ambient')) :
    ∃ out, v.dev = some out ∧ RoutingInvariant out t4 t6 :=
  peerPut_routing_preserved w v ambient ambient' d hd hi peer hr

/-- Finite actual normal create/insert/removeByPeer/peerPut/free calls from the
original configured fixture refine an independent pair of canonical flat-prefix
tables. Actual returns determine success/refusal effects. Only insertion's
reached input bounds and target residency are supplied; coherence and agreement
are derived at every step. This does not cover enclosing Netlink or Runner calls. -/
theorem original_initialized_routing_history (w v : WGWorld) (ambient finalAmbient : Ambient) (calls : List RoutingCall)
    (history : RoutingHistory w ambient calls v finalAmbient)
    (hstart : Leanux.Proofs.Framing.wgStoreView w = Leanux.Proofs.Framing.wgStoreView (Runner.initialWG true false)) :
    ∃ out t4 t6, v.dev = some out ∧ RoutingInvariant out t4 t6 ∧
      FlatAgree 32 t4 (flatHistory calls ([], [])).1 ∧
      FlatAgree 128 t6 (flatHistory calls ([], [])).2 := history.initialized hstart

/-- Bounded IPv4/IPv6 findNode at the actual reached root returns a longest
matching canonical prefix justified by the finite call history. Any returned
node has that raw owner in the actual store. No owner-residency, packet identity
authorization, enclosing configuration history or failed-World claim follows. -/
theorem original_initialized_history_findNode (w v : WGWorld) (ambient finalAmbient : Ambient) (calls : List RoutingCall)
    (history : RoutingHistory w ambient calls v finalAmbient)
    (hstart : Leanux.Proofs.Framing.wgStoreView w = Leanux.Proofs.Framing.wgStoreView (Runner.initialWG true false))
    (v4 : Bool) (key : Nat) (hk : key < 2 ^ rootWidth v4) :
    ∃ (d : WG.Device) (answer : Option Entry) (finish : WGWorld) (finishAmbient : Ambient), v.dev = some d ∧
      ((WG.liftAip (WG.findNode (rootValue d v4) (rootWidth v4) key)).run v).run finalAmbient =
        .ok ((answer.map Entry.id, finish), finishAmbient) ∧
      Leanux.Proofs.Framing.wgStoreView finish = Leanux.Proofs.Framing.wgStoreView v ∧
      FlatWinner (rootWidth v4) key (selectedFlat v4 (flatHistory calls ([], [])))
        (answer.map (canonical (rootWidth v4))) ∧
      ∀ e ∈ answer, ∃ n, d.nodes[e.id]? = some n ∧ n.peer = some e.peer :=
  history.findNode hstart v4 key hk

/-- The actual pinned private parser supplies the address/length relation. A
normal setAllowedip call either rejects without store-view mutation or reaches an
actual bounded IPv4/IPv6 insertion after its original guards. Malformed/missing
fields and AF overrides retain the source behavior; no parser-fidelity premise
or enclosing parser/Runner closure is assumed. -/
theorem parsed_setAllowedip_bounded_call (j : Lean.Json) (what : String) (ip : WG.AllowedIpAttrs)
    (hp : parseAllowedIp j what = .ok (.attrs ip)) (pid : WG.PeerId)
    (w v : WGWorld) (ambient ambient' : Ambient) (ret : Int) (hr : ((WG.setAllowedip pid ip).run w).run ambient = .ok ((ret, v), ambient')) :
    AddressShape ip ∧ AllowedipOutcome (Leanux.Proofs.Framing.wgStoreView w) pid ip ret v ambient' :=
  ⟨parseAllowedIp_shape j what (.attrs ip) hp, parsed_setAllowedip_outcome j what ip hp pid w v ambient ambient' ret hr⟩

/-- Parsed local allowed-IP attributes compose with the actual normal insertion
contract. Resident target and entry routing/flat agreement remain explicit;
rejection preserves the seven-field WG store view, while negative insertion returns keep their actual
sequence/frontier effects. This is not whole Netlink/configuration closure. -/
theorem parsed_setAllowedip_routing_preserved (j : Lean.Json) (what : String)
    (ip : WG.AllowedIpAttrs) (hparse : parseAllowedIp j what = .ok (.attrs ip))
    (pid : WG.PeerId) (w v : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (xs : FlatTable × FlatTable) (he4 : FlatAgree 32 t4 xs.1) (he6 : FlatAgree 128 t6 xs.2)
    (ret : Int) (hr : ((WG.setAllowedip pid ip).run w).run ambient = .ok ((ret, v), ambient')) :
    (ret = -EINVAL ∧ Leanux.Proofs.Framing.wgStoreView v = Leanux.Proofs.Framing.wgStoreView w) ∨
      ∃ v4 out u4 u6, ip.family.getD 0 = (if v4 then WG.AF_INET else WG.AF_INET6) ∧
        v.dev = some out ∧ RoutingInvariant out u4 u6 ∧
        FlatAgree 32 u4 ((RoutingCall.insert v4 (ip.addr.getD 0) (ip.cidr.getD 0) pid ret).flat xs).1 ∧
        FlatAgree 128 u6 ((RoutingCall.insert v4 (ip.addr.getD 0) (ip.cidr.getD 0) pid ret).flat xs).2 :=
  setAllowedip_routing pid ip (parseAllowedIp_shape j what (.attrs ip) hparse)
    w v ambient ambient' d hd hi hp he4 he6 ret hr

/-- Original rootRemovePeerLists has an all-input source equation. From the
represented subtree and resident-list ownership, a normal return removes every
represented ID from every resident list and preserves all other store-view/device
and complete peer fields. No owner residency, fuel sufficiency or totality is
asserted; complete normal WG.free and its history rule are stated separately. -/
theorem original_rootRemove_lists_normal (w v : WGWorld) (ambient ambient' : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (ho : ListsOwned d) (root : WG.NodeId) (t : Tree) (width : Nat) (parent : WG.Slot)
    (hroot : t.root = some root) (hrep : RepAt d.nodes width parent t)
    (hr : ((WG.rootRemovePeerLists root).run w).run ambient = .ok (((), v), ambient')) :
    rootRemoveSource root = WG.rootRemovePeerLists root ∧ clearListView v = clearListView w ∧
      ∃ out, v.dev = some out ∧ out.nodes = d.nodes ∧
        ∀ (pid : WG.PeerId) (p : WG.Peer), out.peers[pid]? = some p →
          ∀ id ∈ t.nodeIds, id ∉ p.allowedipsList :=
  ⟨rootRemoveSource_eq root, (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
      (rootRemove_clearListView root) w ambient () v ambient' hr,
    rootRemove_lists w v ambient ambient' d hd ho root hroot hrep hr⟩

/-- A normal return of the complete original free empties both represented
families and every resident allowed-IP list. The WG store-view endpoint retains
complete peer records except those lists, increments sequence once, preserves
all allocation frontiers and other Device fields, and only deletes node entries.
Raw orphan owners remain permitted inputs: totality, physical-node emptiness
and a returned failed World are not claimed. -/
theorem original_free_routing_endpoint (w v : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6)
    (hr : (WG.free.run w).run ambient = .ok (((), v), ambient')) :
    ∃ out, Leanux.Proofs.Framing.wgStoreView v = {Leanux.Proofs.Framing.wgStoreView w with dev := some out} ∧ Cleared d out ∧
      RoutingInvariant out .empty .empty := by
  obtain ⟨out, hout, hc⟩ := free_endpoint w v ambient ambient' d hd t4 t6 hi hr
  exact ⟨out, hout, hc, Cleared.routing hi hc⟩

/-- After a normal original clear, original findNode at either actual family
root returns no binding. This follows from the derived empty represented forest;
it does not require every unreachable physical node to have been retired. -/
theorem original_free_then_findNode (w v : WGWorld) (ambient ambient' : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (t4 t6 : Tree) (hi : RoutingInvariant d t4 t6)
    (hr : (WG.free.run w).run ambient = .ok (((), v), ambient'))
    (v4 : Bool) (key : Nat) (hk : key < 2 ^ rootWidth v4) :
    ∃ out finish finishAmbient, Leanux.Proofs.Framing.wgStoreView v = {Leanux.Proofs.Framing.wgStoreView w with dev := some out} ∧ Cleared d out ∧
      ((WG.liftAip (WG.findNode (rootValue out v4) (rootWidth v4) key)).run v).run ambient' =
        .ok ((none, finish), finishAmbient) ∧
      Leanux.Proofs.Framing.wgStoreView finish = Leanux.Proofs.Framing.wgStoreView v := by
  obtain ⟨out, hout, hc⟩ := free_endpoint w v ambient ambient' d hd t4 t6 hi hr
  have hi' := Cleared.routing hi hc
  have hd' : v.dev = some out := congrArg Leanux.Proofs.Framing.WGStoreView.dev hout
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨finishAmbient, hrun⟩ := findNode_lift_run v ambient' out hd' (rootWidth v4) key hw hk
    (selectedTree v4 .empty .empty) (rootSlot v4) (hi'.selected_rep v4) (hi'.selected_valid v4)
  refine ⟨out, v, finishAmbient, hout, hc, ?_, rfl⟩
  simpa [hi'.selected_root v4, selectedTree, Tree.lookupId, Tree.lookup] using hrun

/-- Original raw release and staged-send helpers retain nodes, table/frontiers
and surviving resident lists, permitting peer deletion and raw orphan owners.
These are normal-return frames, not reference-affiliation or totality claims. -/
theorem original_routing_silent_frames (pid : WG.PeerId) (peer : Option WG.PeerId) :
    RetainsRoutingCall (WG.peerPut peer) ∧
    RetainsRoutingCall (WG.sendStagedPackets pid) ∧
    RetainsRoutingCall (WG.sendKeepalive pid) :=
  ⟨peerPut_retainsRouting peer, sendStagedPackets_routing pid, sendKeepalive_routing pid⟩

/-- The whole setAllowedip observer and actual original peer-configuration tail
cut erase exactly for every input, including malformed attributes and Stops.
Only normally completed whole attribute calls emit events; their exact signed
returns and before/after views are retained. This statement has no routing,
address-shape, target-residency or normal-return premise. -/
theorem routing_completion_source_erasure (pid : WG.PeerId) (ip : WG.AllowedIpAttrs)
    (a : WG.PeerAttrs) (peer : Option WG.PeerId) :
    Logged.ErasesStatePrefix (completedAllowedip pid ip) (WG.setAllowedip pid ip) ∧
    Logged.ErasesStatePrefix (Configuration.peerConfigTailObserved a peer pid)
      (Configuration.peerConfigTailSource a peer pid) :=
  ⟨completedAllowedip_erases pid ip, Configuration.peerConfigTailObserved_erases a peer pid⟩

/-- Actual whole-call completion derives semantic flat agreement and preserves
the insertion target from its exact source outcomes. Exactly return zero updates
the flat table; guard rejections and allocation refusals retain the table and
all actual source effects. A Stop preserves the prior safe journal without a
failed World or a completion event. Entry shape/routing/residency are explicit. -/
theorem setAllowedip_completion_routing (initial : FlatTable × FlatTable)
    (pid : WG.PeerId) (ip : WG.AllowedIpAttrs) (shape : AddressShape ip) :
    Logged.StatePrefixPreserves (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (completedAllowedip pid ip) :=
  completedAllowedip_preserves initial pid ip shape

/-- The actual allowed-IP loop, early cleanup and complete remaining peer tail
preserve a semantically valid completed-call prefix even on Stop. Normal returns
also derive current routing/flat agreement from that prefix. Target residency
is maintained only while inserting; concrete send/release frames permit later
peer deletion. Local address shape and entry routing/residency remain premises;
this is not enclosing setPeerCmd, parser, Netlink or Runner closure. -/
theorem original_peerConfigTail_routing_prefix (initial : FlatTable × FlatTable)
    (a : WG.PeerAttrs) (shape : Configuration.PeerAddressShape a)
    (peer : Option WG.PeerId) (pid : WG.PeerId) :
    Logged.StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (Configuration.peerConfigTailObserved a peer pid) (fun _ h w _ => CompletionState initial h w) :=
  Configuration.peerConfigTailObserved_spec initial a shape peer pid

/-- Removal, peer death/removal and the complete acquired-peer update stage
have exact original erasure for all inputs. The journal records the nested
removeByPeer normal cut before later peer cleanup or flushing can Stop; it does
not label that cut as completion of whole peer-object removal. -/
theorem original_peer_update_completion_erasure (pid : WG.PeerId) (peer : Option WG.PeerId)
    (a : WG.PeerAttrs) (flags : UInt32) (psk : Option WG.Key) :
    Logged.ErasesStatePrefix (completedRemovePeer pid) (WG.removeByPeer pid) ∧
    Logged.ErasesStatePrefix (Configuration.peerMakeDeadObserved pid) (WG.peerMakeDead pid) ∧
    Logged.ErasesStatePrefix (Configuration.peerRemoveObserved peer) (WG.peerRemove peer) ∧
    Logged.ErasesStatePrefix (Configuration.peerConfigUpdateObserved a peer flags psk pid)
      (Configuration.peerConfigUpdateSource a peer flags psk pid) :=
  ⟨completedRemovePeer_erases pid, Configuration.peerMakeDeadObserved_erases pid,
    Configuration.peerRemoveObserved_erases peer,
    Configuration.peerConfigUpdateObserved_erases a peer flags psk pid⟩

/-- Completed routing removal derives its flat owner filtering and target
residency from the original normal call. Peer-object removal may subsequently
delete peers or Stop during flushing; its earlier completed routing prefix
remains safe, and only normal returns carry reached routing/flat agreement. -/
theorem original_peer_removal_routing_prefix (initial : FlatTable × FlatTable)
    (pid : WG.PeerId) (peer : Option WG.PeerId) :
    Logged.StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (completedRemovePeer pid) (fun _ h w _ => CompletionTarget initial pid h w) ∧
    Logged.StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (Configuration.peerRemoveObserved peer) (fun _ h w _ => CompletionState initial h w) :=
  ⟨completedRemovePeer_spec initial pid, Configuration.peerRemoveObserved_spec initial peer⟩

/-- The actual acquired-peer update stage covers REMOVE_ME, preshared-key and
endpoint changes, REPLACE_ALLOWEDIPS and the complete allowed-IP/send tail.
Its explicit local routing/target/shape inputs derive safe completed prefixes
on every outcome and routing/flat agreement on normal returns. No drain-success,
reference-credit or affiliation premise is imposed. The public preflight/acquire
composition of setPeerCmd remains outside this stage theorem. -/
theorem original_peer_update_routing_prefix (initial : FlatTable × FlatTable)
    (a : WG.PeerAttrs) (shape : Configuration.PeerAddressShape a)
    (peer : Option WG.PeerId) (flags : UInt32) (psk : Option WG.Key) (pid : WG.PeerId) :
    Logged.StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (Configuration.peerConfigUpdateObserved a peer flags psk pid) (fun _ h w _ => CompletionState initial h w) :=
  Configuration.peerConfigUpdateObserved_spec initial a shape peer flags psk pid

/-- Actual public-key-table lookup and peer creation establish the returned
raw-slot residency. Lookup preserves the routing view; creation/refusal preserves
flat agreement while retaining its actual allocator effects. No public-key/peer
identity affiliation or full setPeerCmd composition is asserted. -/
theorem original_configuration_acquisition_routing (initial : FlatTable × FlatTable)
    (key : WG.Key) (psk : Option WG.Key) :
    Logged.StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix (WG.pubkeyLookup key)) (fun x h w _ => CompletionAcquired initial x h w) ∧
    Logged.StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix (WG.peerCreate key psk)) (fun x h w _ => CompletionCreated initial x h w) :=
  ⟨pubkeyLookup_completion initial key, peerCreate_completion initial key psk⟩

/-- The complete public peer-command observer erases to the original call for
all attributes and Worlds, preserving every ordinary return and Stop. Nested
routing completion events remain at their actual primitive boundaries. -/
theorem original_setPeerCmd_completion_erasure (a : WG.PeerAttrs) :
    Logged.ErasesStatePrefix (Configuration.setPeerCmdObserved a) (WG.setPeerCmd a) :=
  Configuration.setPeerCmdObserved_erases a

/-- From routed entry and local address shape, the complete original command
preserves semantically valid completed prefixes on every outcome and derives
reached routing/flat agreement on normal returns. Actual lookup/create outcomes
supply residency; no target-residency, credit, affiliation or progress premise
is imposed on this whole-command contract. -/
theorem original_setPeerCmd_routing_prefix (initial : FlatTable × FlatTable)
    (a : WG.PeerAttrs) (shape : Configuration.PeerAddressShape a) :
    Logged.StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (Configuration.setPeerCmdObserved a) (fun _ h w _ => CompletionState initial h w) :=
  Configuration.setPeerCmdObserved_spec initial a shape

/-- Successful public parsing derives address shape for every actual wgSet
peer attribute, so its whole peer-command contract needs no extra shape premise.
Malformed entries remain legal alternatives. This links parsed commands to the
local contract; it is not execution of the enclosing configuration or Runner. -/
theorem parsed_trace_peer_commands_routing (j : Lean.Json) (trace : Runner.Trace)
    (hparse : Runner.parseTrace j = .ok trace) (initial : FlatTable × FlatTable) :
    Configuration.TraceAddressShape trace ∧
      ∀ attrs, Runner.Operation.wgSet attrs ∈ trace.ops →
        ∀ peer, WG.PeerEntry.attrs peer ∈ attrs.peers.getD [] →
          Logged.StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
            (Configuration.setPeerCmdObserved peer) (fun _ h w _ => CompletionState initial h w) := by
  have hs := Configuration.parseTrace_shape j trace hparse
  refine ⟨hs, ?_⟩
  intro attrs hop peer hp
  exact Configuration.setPeerCmdObserved_spec initial peer (hs (.wgSet attrs) hop peer hp)

/-- All-input device observers preserve the original returns and Stops. The
clear marker occurs after WG.free normally completes, before either remove-all
loop; no event represents a failed primitive's unavailable World. -/
theorem original_device_configuration_completion_erasure (a : WG.DeviceAttrs) :
    Logged.ErasesStatePrefix completedFree WG.free ∧
    Logged.ErasesStatePrefix Configuration.peerRemoveAllObserved WG.peerRemoveAll ∧
    Logged.ErasesStatePrefix (Configuration.wgSetDeviceObserved a) (WG.wgSetDevice a) :=
  ⟨completedFree_erases, Configuration.peerRemoveAllObserved_erases,
    Configuration.wgSetDeviceObserved_erases a⟩

/-- From routed entry, clear and remove-all normally leave the journal's flat
tables empty; this does not assert physical node-store emptiness or totality.
The complete original device configuration retains valid completed prefixes on
Stop and derives reached routing/flat agreement on normal returns, including
ordinary negative results. Only local address shape is added: no target-residency,
saved-list validity, drain, credit or identity-affiliation premise is needed. -/
theorem original_device_configuration_routing_prefix (initial : FlatTable × FlatTable)
    (a : WG.DeviceAttrs) (shape : Configuration.DeviceAddressShape a) :
    Logged.StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      completedFree (fun _ h w _ => CompletionEmpty initial h w) ∧
    Logged.StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      Configuration.peerRemoveAllObserved (fun _ h w _ => CompletionEmpty initial h w) ∧
    Logged.StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
      (Configuration.wgSetDeviceObserved a) (fun _ h w _ => CompletionState initial h w) :=
  ⟨completedFree_empty_spec initial, Configuration.peerRemoveAllObserved_empty_spec initial,
    Configuration.wgSetDeviceObserved_spec initial a shape⟩

/-- Actual successful public parsing discharges address shape for every wgSet
operation's complete device-command contract. Malformed entries retain their
original error paths. Routed entry remains explicit; this is not enclosing
Runner execution, device lifecycle closure or packet authorization. -/
theorem parsed_trace_device_configuration_routing (j : Lean.Json) (trace : Runner.Trace)
    (hparse : Runner.parseTrace j = .ok trace) (initial : FlatTable × FlatTable) :
    Configuration.TraceAddressShape trace ∧
      ∀ attrs, Runner.Operation.wgSet attrs ∈ trace.ops →
        Logged.StatePrefixEnsures (fun h w _ => CompletionState initial h w) (CompletionSafe initial)
          (Configuration.wgSetDeviceObserved attrs) (fun _ h w _ => CompletionState initial h w) := by
  have hs := Configuration.parseTrace_shape j trace hparse
  refine ⟨hs, ?_⟩
  intro attrs hop
  exact Configuration.wgSetDeviceObserved_spec initial attrs (hs (.wgSet attrs) hop)

/-- Original optional-device lifecycle observers erase unconditionally,
including absent-device errors, arbitrary fixture rows and failed teardown.
Creation and down run as exact original lifts; no synthetic reset event is used. -/
theorem original_optional_lifecycle_erasure (a : WG.DeviceAttrs) (p : WG.PeerAttrs) :
    Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) WG.wgCreate) WG.wgCreate ∧
    Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) WG.wgDown) WG.wgDown ∧
    Logged.ErasesStatePrefix Configuration.wgDestructObserved WG.wgDestruct ∧
    Logged.ErasesStatePrefix Configuration.wgDeleteObserved WG.wgDelete ∧
    Logged.ErasesStatePrefix (Configuration.setPeerCmdObserved p) (WG.setPeerCmd p) ∧
    Logged.ErasesStatePrefix (Configuration.wgSetDeviceObserved a) (WG.wgSetDevice a) :=
  ⟨Logged.erasesStatePrefix_lift _, Logged.erasesStatePrefix_lift _,
    Configuration.wgDestructObserved_erases, Configuration.wgDeleteObserved_erases,
    Configuration.setPeerCmdObserved_erases p, Configuration.wgSetDeviceObserved_erases a⟩

/-- The optional state represents absence by empty flat tables and present
routing by the existing structural invariant. Actual guarded creation, down,
destruction/deletion and complete configuration preserve it on normal return,
while all Stops retain semantically safe completed prefixes. Absent whole peer
and device commands preserve exactly their entry histories on every outcome;
this does not extend direct invalid allowed-IP completions to absent devices.
Only local address shape is required, with no fixture-authenticity, resident-owner,
credit, drain or successful-execution premise. Runner and packet closure remain separate. -/
theorem original_optional_lifecycle_routing_prefix (initial : FlatTable × FlatTable)
    (a : WG.DeviceAttrs) (p : WG.PeerAttrs)
    (ha : Configuration.DeviceAddressShape a) (hp : Configuration.PeerAddressShape p) :
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix WG.wgCreate) ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix WG.wgDown) ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      Configuration.wgDestructObserved ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      Configuration.wgDeleteObserved ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Configuration.setPeerCmdObserved p) ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Configuration.wgSetDeviceObserved a) ∧
    (∀ h0, Logged.StatePrefixPreserves (fun h w _ => h = h0 ∧ routingView w = none) (fun h => h = h0)
      (Configuration.setPeerCmdObserved p)) ∧
    (∀ h0, Logged.StatePrefixPreserves (fun h w _ => h = h0 ∧ routingView w = none) (fun h => h = h0)
      (Configuration.wgSetDeviceObserved a)) :=
  ⟨wgCreate_global_completion initial, global_completion_lift_wg initial _ wgDown_routing,
    Configuration.wgDestructObserved_global initial, Configuration.wgDeleteObserved_global initial,
    Configuration.setPeerCmdObserved_global initial p hp, Configuration.wgSetDeviceObserved_global initial a ha,
    fun h => Configuration.setPeerCmdObserved_absent h p,
    fun h => Configuration.wgSetDeviceObserved_absent h a⟩

/-- The actual Runner fixture initializes optional routing for every typed
trace, including bare and nonnetwork modes. The original store-view premise
retains its scope; seccomp prefill is subsystem-local and needs no WG frame. -/
theorem original_optional_routing_initialization (trace : Runner.Trace) (w : World)
    (hw : Framing.wgStoreView w.wg =
      Framing.wgStoreView (Runner.initialWG trace.net trace.bare)) :
    GlobalCompletionState ([], []) [] w.wg :=
  Configuration.global_initial trace w hw

/-- Complete original TX calls preserve the routing table, node/peer frontiers
and each surviving resident list on every normal return, including ordinary
errors. Peer deletion is permitted. Arbitrary encryption and rescheduling
callbacks require their own routing frames; the checksum and Stack callbacks
are also discharged concretely. This is not destination authorization. -/
theorem original_tx_routing_frames (family addr : Nat) (packets : List WG.Packet) (mtu : Nat)
    (pid : WG.PeerId) (item : List WG.SkbId) (bytes : List UInt8)
    (checksum : WG.Packet → Leanux.M WG.Packet) (softirq : Leanux.M Unit) (need : Leanux.M Bool)
    (hc : ∀ pkt, ProductRetainsRoutingCall (checksum pkt))
    (hs : ProductRetainsRoutingCall softirq) (hn : ProductRetainsRoutingCall need) :
    RetainsRoutingCall (WG.wgXmit family addr packets mtu) ∧
    RetainsRoutingCall (WG.createDataDone pid item) ∧
    RetainsRoutingCall (WG.txStep pid) ∧ ProductRetainsRoutingCall (WG.txIter pid need) ∧
    ProductRetainsRoutingCall (WG.encryptStep checksum softirq) ∧
    ProductRetainsRoutingCall (WG.encryptIter checksum softirq need) ∧
    ProductRetainsRoutingCall (Env.deliverInner bytes) ∧
    (∀ pkt, ProductRetainsRoutingCall (Env.checksumHelp pkt)) :=
  ⟨wgXmit_routing family addr packets mtu, createDataDone_routing pid item,
    txStep_routing pid, txIter_routing pid need hn,
    encryptStep_routing checksum softirq hc hs, encryptIter_routing checksum softirq need hc hs hn,
    deliverInner_routing bytes, actualChecksum_routing⟩

/-- Complete original receive completion/poll and decrypt iteration retain
routing data and surviving lists. Generic GRO, IRQ, softirq and rescheduling
callbacks have explicit frames; the actual Stack callback is proved separately
in the conjunction. No live-owner, credit, affiliation, valid-packet, successful
execution or drain premise is imposed. No authorization or delivery conclusion
follows from this routing frame. -/
theorem original_rx_routing_frames (pid : WG.PeerId) (budget : Nat)
    (pkt : WG.RxPacket) (endpoint : WG.Endpoint)
    (callback : List (List UInt8) → Leanux.M Unit) (softirq irq : Leanux.M Unit) (need : Leanux.M Bool)
    (hc : ∀ xs, ProductRetainsRoutingCall (callback xs))
    (hs : ProductRetainsRoutingCall softirq) (hi : ProductRetainsRoutingCall irq) (hn : ProductRetainsRoutingCall need) :
    RetainsRoutingCall (WG.consumeDataDone pid pkt endpoint) ∧
    ProductRetainsRoutingCall (WG.rxPoll pid budget callback) ∧
    ProductRetainsRoutingCall (WG.rxPoll pid budget (fun xs => xs.forM Env.deliverInner)) ∧
    ProductRetainsRoutingCall (WG.decryptStep softirq irq) ∧
    ProductRetainsRoutingCall (WG.decryptIter softirq irq need) :=
  ⟨consumeDataDone_routing pid pkt endpoint, rxPoll_routing pid budget callback hc,
    actualRxPoll_routing pid budget, decryptStep_routing softirq irq hs hi,
    decryptIter_routing softirq irq need hs hi hn⟩

/-- Whole-call traffic lifts erase to the actual original computations. They
leave completion history unchanged on every outcome, preserve optional global
routing/flat agreement on normal return and retain the earlier safe history on
Stop. There is no returned failed World, packet authorization, or enclosing
scheduler/Runner claim. -/
theorem original_traffic_routing_completion (initial : FlatTable × FlatTable)
    (family addr : Nat) (packets : List WG.Packet) (mtu : Nat)
    (pid : WG.PeerId) (budget : Nat) (pkt : WG.RxPacket) (endpoint : WG.Endpoint) :
    (Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) (WG.wgXmit family addr packets mtu))
        (WG.wgXmit family addr packets mtu) ∧
      Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
        (Logged.liftWGPrefix (WG.wgXmit family addr packets mtu))) ∧
    (Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) (WG.txStep pid)) (WG.txStep pid) ∧
      Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
        (Logged.liftWGPrefix (WG.txStep pid))) ∧
    (Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) (WG.consumeDataDone pid pkt endpoint))
        (WG.consumeDataDone pid pkt endpoint) ∧
      Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
        (Logged.liftWGPrefix (WG.consumeDataDone pid pkt endpoint))) ∧
    (Logged.ErasesPrefix (Logged.liftPrefix (Event := RoutingCompletion)
        (WG.rxPoll pid budget (fun xs => xs.forM Env.deliverInner)))
        (WG.rxPoll pid budget (fun xs => xs.forM Env.deliverInner)) ∧
      Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
        (Logged.liftPrefix (WG.rxPoll pid budget (fun xs => xs.forM Env.deliverInner)))) := by
  have liftNative {α : Type} (a : WG.M α) (ha : RetainsRoutingCall a) :
      Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) a) a ∧
        Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w)
          (CompletionSafe initial) (Logged.liftWGPrefix a) :=
    ⟨Logged.erasesStatePrefix_lift a, global_completion_lift_wg initial a ha⟩
  have liftProduct {α : Type} (a : Leanux.M α) (ha : ProductRetainsRoutingCall a) :
      Logged.ErasesPrefix (Logged.liftPrefix (Event := RoutingCompletion) a) a ∧
        Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg)
          (CompletionSafe initial) (Logged.liftPrefix a) :=
    ⟨Logged.erasesPrefix_lift a, global_completion_lift World.wg initial a ha⟩
  exact ⟨liftNative _ (wgXmit_routing family addr packets mtu), liftNative _ (txStep_routing pid),
    liftNative _ (consumeDataDone_routing pid pkt endpoint), liftProduct _ (actualRxPoll_routing pid budget)⟩

/-- Original receive admission, including keypair refusal and EPIPE/ENOSPC
cleanup, preserves the routing table/frontiers and every surviving resident
list on normal return. This requires no input residency, affiliation, credit or
packet-validity premise. Its whole-call lift erases on all inputs and retains
safe prior completion history on Stop, without a returned failed World. -/
theorem original_receive_admission_routing (initial : FlatTable × FlatTable)
    (msg : List UInt8) (src : WG.SkbSource) (ds : Nat) (id : WG.SkbId) :
    Framing.SameView routingView (WG.enqueuePerDeviceAndPeerRx id) ∧
    RetainsRoutingCall (WG.consumeData msg src ds) ∧
    RetainsRoutingCall (WG.packetReceive msg src) ∧
    RetainsRoutingCall (WG.wgReceive msg src) ∧
    Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) (WG.wgReceive msg src))
      (WG.wgReceive msg src) ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix (WG.wgReceive msg src)) :=
  ⟨enqueuePerDeviceAndPeerRx_routing id, consumeData_routing msg src ds,
    packetReceive_routing msg src, wgReceive_routing msg src,
    Logged.erasesStatePrefix_lift _, global_completion_lift_wg initial _ (wgReceive_routing msg src)⟩

/-- Both actual direct poll callers, IRQ-exit placement and crypt iterations
now have concrete routing frames: checksum, Stack, softirq, IRQ and rescheduling
callbacks are discharged. Original pending-map scans, ambiguity choices and
Stops remain. No saved-list or progress premise is imposed. This local caller
closure is not a complete activation/scheduler or packet-authorization theorem. -/
theorem original_concrete_napi_routing (initial : FlatTable × FlatTable) (pid : WG.PeerId) :
    ProductRetainsRoutingCall Env.napiSoftirq ∧ ProductRetainsRoutingCall Env.pollScheduledInline ∧
    ProductRetainsRoutingCall Env.napiIrqExit ∧
    ProductRetainsRoutingCall (WG.encryptStep Env.checksumHelp Env.napiSoftirq) ∧
    ProductRetainsRoutingCall (WG.encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) ∧
    ProductRetainsRoutingCall (WG.decryptStep Env.napiSoftirq Env.napiIrqExit) ∧
    ProductRetainsRoutingCall (WG.decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) ∧
    ProductRetainsRoutingCall (WG.txIter pid (Env.condResched .txWorker)) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix Env.napiSoftirq) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix Env.pollScheduledInline) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix Env.napiIrqExit) :=
  ⟨napiSoftirq_routing, pollScheduledInline_routing, napiIrqExit_routing,
    actualEncryptStep_routing, actualEncryptIter_routing, actualDecryptStep_routing,
    actualDecryptIter_routing, actualTxIter_routing pid,
    global_completion_lift World.wg initial _ napiSoftirq_routing,
    global_completion_lift World.wg initial _ pollScheduledInline_routing,
    global_completion_lift World.wg initial _ napiIrqExit_routing⟩

/-- Every original timer callback and device open/up/namespace-exit preserves
routing on normal return, including ordinary negative errors. Peer deletion is
allowed, and subsequent cached writes are justified by actual source getters.
Whole-call lifts retain the existing journal and optional routing state; no
resident-owner, reference-credit, saved-list, successful-drain or fixture premise
is needed. Timer scheduling is composed separately below; enclosing Runner
execution remains separate. -/
theorem original_timer_device_routing (initial : FlatTable × FlatTable)
    (pid : WG.PeerId) (timer : WG.PeerTimer) :
    RetainsRoutingCall (WG.timerCallback pid timer) ∧
    RetainsRoutingCall WG.wgOpen ∧ RetainsRoutingCall WG.wgUp ∧
    Framing.SameView routingView WG.netnsPreExit ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix (WG.timerCallback pid timer)) ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix WG.wgOpen) ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix WG.wgUp) ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix WG.netnsPreExit) :=
  ⟨timerCallback_routing pid timer, wgOpen_routing, wgUp_routing, netnsPreExit_routing,
    global_completion_lift_wg initial _ (timerCallback_routing pid timer),
    global_completion_lift_wg initial _ wgOpen_routing, global_completion_lift_wg initial _ wgUp_routing,
    global_completion_same_wg initial _ netnsPreExit_routing⟩

/-- Original session creation and response sending preserve the complete routing
view on normal return. Actual getter facts justify peer setters; keypair/index
updates do not require resident owners, affiliation or a successful-session
premise. Original refusal and Stop paths remain unchanged. -/
theorem original_session_routing_frames (pid : WG.PeerId) (peerWord : Option WG.PeerId) (kp : WG.KeypairId)
    (initiator : Bool) (ck : List UInt8) :
    Framing.SameView routingView (WG.keypairCreate peerWord) ∧
    Framing.SameView routingView (WG.addNewKeypair pid kp) ∧
    Framing.SameView routingView (WG.deriveKeys kp initiator ck) ∧
    Framing.SameView routingView (WG.beginSession pid) ∧
    Framing.SameView routingView (WG.createResponse pid) ∧
    Framing.SameView routingView (WG.timersSessionDerived pid) ∧
    Framing.SameView routingView (WG.sendHandshakeResponse pid) :=
  ⟨keypairCreate_routing peerWord, addNewKeypair_routing pid kp, deriveKeys_routing kp initiator ck,
    beginSession_routing pid, createResponse_routing pid,
    timersSessionDerived_routing pid, sendHandshakeResponse_routing pid⟩

/-- Complete original incoming Noise/cookie and handshake receive calls retain
routing and every surviving peer list on normal return. Releases may retire a
peer, so equality of resident stores is not claimed. The actual receive-worker
iteration discharges condResched concretely. There is no input residency,
affiliation, credit, valid-packet, saved-list or successful-drain premise. -/
theorem original_handshake_receive_routing_frames (msg : List UInt8) (src : WG.SkbSource) :
    RetainsRoutingCall (WG.consumeInitiation msg) ∧
    RetainsRoutingCall (WG.consumeResponse msg) ∧
    RetainsRoutingCall (WG.cookieMessageConsume msg) ∧
    RetainsRoutingCall (WG.receiveHandshakePacket msg src) ∧
    RetainsRoutingCall WG.receiveStep ∧
    ProductRetainsRoutingCall (workerIter .receiveWorker none (Leanux.liftWG WG.receiveStep) (Env.condResched .receiveWorker)) :=
  ⟨consumeInitiation_routing msg, consumeResponse_routing msg, cookieMessageConsume_routing msg,
    receiveHandshakePacket_routing msg src, receiveStep_routing, actualReceiveIter_routing⟩

/-- Silent whole-call handshake lifts erase exactly to the originals on every
input. Normal returns preserve optional routing/flat agreement; every outcome
leaves the completion journal unchanged, retaining prior history safety on Stop
without a failed World. Scheduler composition is supplied below; no packet
authorization or Runner closure follows from these local caller contracts. -/
theorem original_handshake_routing_completion (initial : FlatTable × FlatTable)
    (msg : List UInt8) (src : WG.SkbSource) :
    (Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) (WG.consumeInitiation msg))
        (WG.consumeInitiation msg) ∧
      Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
        (Logged.liftWGPrefix (WG.consumeInitiation msg))) ∧
    (Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) (WG.consumeResponse msg))
        (WG.consumeResponse msg) ∧
      Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
        (Logged.liftWGPrefix (WG.consumeResponse msg))) ∧
    (Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) (WG.cookieMessageConsume msg))
        (WG.cookieMessageConsume msg) ∧
      Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
        (Logged.liftWGPrefix (WG.cookieMessageConsume msg))) ∧
    (Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) (WG.receiveHandshakePacket msg src))
        (WG.receiveHandshakePacket msg src) ∧
      Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
        (Logged.liftWGPrefix (WG.receiveHandshakePacket msg src))) ∧
    (Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) WG.receiveStep) WG.receiveStep ∧
      Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
        (Logged.liftWGPrefix WG.receiveStep)) ∧
    (Logged.ErasesPrefix (Logged.liftPrefix (Event := RoutingCompletion)
        (workerIter .receiveWorker none (Leanux.liftWG WG.receiveStep) (Env.condResched .receiveWorker)))
        (workerIter .receiveWorker none (Leanux.liftWG WG.receiveStep) (Env.condResched .receiveWorker)) ∧
      Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
        (Logged.liftPrefix (workerIter .receiveWorker none (Leanux.liftWG WG.receiveStep) (Env.condResched .receiveWorker)))) := by
  have liftNative {α : Type} (a : WG.M α) (ha : RetainsRoutingCall a) :
      Logged.ErasesStatePrefix (Logged.liftWGPrefix (E := RoutingCompletion) a) a ∧
        Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w)
          (CompletionSafe initial) (Logged.liftWGPrefix a) :=
    ⟨Logged.erasesStatePrefix_lift a, global_completion_lift_wg initial a ha⟩
  have liftProduct {α : Type} (a : Leanux.M α) (ha : ProductRetainsRoutingCall a) :
      Logged.ErasesPrefix (Logged.liftPrefix (Event := RoutingCompletion) a) a ∧
        Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg)
          (CompletionSafe initial) (Logged.liftPrefix a) :=
    ⟨Logged.erasesPrefix_lift a, global_completion_lift World.wg initial a ha⟩
  exact ⟨liftNative _ (consumeInitiation_routing msg), liftNative _ (consumeResponse_routing msg),
    liftNative _ (cookieMessageConsume_routing msg), liftNative _ (receiveHandshakePacket_routing msg src),
    liftNative _ receiveStep_routing, liftProduct _ actualReceiveIter_routing⟩

/-- The actual pre-encryption helper, all activation iterations and complete
scheduler retain routing on normal return from arbitrary Worlds. Exact source
scheduler erasure supplies this frame, including copied consistency trials and
their original Stops; there is no successful-trial or entry-invariant premise.
Silent whole-call lifts preserve optional routing on normal return and retain
prior safe completion histories on Stop, without a failed World. -/
theorem original_scheduler_routing (initial : FlatTable × FlatTable)
    (pid : WG.PeerId) (a : Activation) (worker : Worker) (stack : Option Worker) :
    ProductRetainsRoutingCall (Env.cryptAhead pid) ∧
    ProductRetainsRoutingCall (Env.Activation.iter a) ∧
    ProductRetainsRoutingCall (Env.Activation.run a) ∧
    ProductRetainsRoutingCall (Env.dispatch worker) ∧
    ProductRetainsRoutingCall (Env.schedule stack) ∧
    ProductRetainsRoutingCall (Env.nestedResched worker) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix (Env.Activation.run a)) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix (Env.dispatch worker)) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix (Env.schedule stack)) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix (Env.nestedResched worker)) :=
  ⟨cryptAhead_routing pid, activationIter_routing a, activationRun_routing a,
    dispatch_routing worker, schedule_routing stack, nestedResched_routing worker,
    global_completion_lift World.wg initial _ (activationRun_routing a),
    global_completion_lift World.wg initial _ (dispatch_routing worker),
    global_completion_lift World.wg initial _ (schedule_routing stack),
    global_completion_lift World.wg initial _ (nestedResched_routing worker)⟩

/-- Actual deferred crypt/send/clear workers and transmit completion retain
routing and surviving peer lists. Queue membership supplies no residency premise;
the original fresh getters justify setters or Stop. The existing bounded drain
contract is included without a drain-success assumption. Whole-call lifts keep
the journal unchanged on every outcome and optional state only on normal return. -/
theorem original_environment_worker_routing (initial : FlatTable × FlatTable)
    (what : String) (queues : List Bool) (upTo : Option WG.PeerId) :
    Framing.SameView (fun w : World => routingView w.wg) (Env.requireDrained what queues) ∧
    ProductRetainsRoutingCall Env.runCryptWorkers ∧
    ProductRetainsRoutingCall Env.runOneSendWorker ∧
    ProductRetainsRoutingCall Env.runOneClearWorker ∧
    ProductRetainsRoutingCall Env.runSendWorkers ∧
    ProductRetainsRoutingCall Env.afterXmit ∧
    RetainsRoutingCall (WG.drainHandshakeSendWq upTo) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix Env.runCryptWorkers) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix Env.runSendWorkers) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix Env.afterXmit) :=
  ⟨requireDrained_routing what queues, runCryptWorkers_routing, runOneSendWorker_routing,
    runOneClearWorker_routing, runSendWorkers_routing, afterXmit_routing,
    drainHandshakeSendWq_routing upTo,
    global_completion_lift World.wg initial _ runCryptWorkers_routing,
    global_completion_lift World.wg initial _ runSendWorkers_routing,
    global_completion_lift World.wg initial _ afterXmit_routing⟩

/-- Recorded timer dispatch, the original placeholder pass and enclosing idle/
advance calls retain routing on normal return. All concrete timer callbacks are
discharged; no due-entry residency, saved-list validity or progress assumption is
added. Whole-call lifts retain prior safe history on Stop, with no failed World,
packet authorization or initialized enclosing Runner claim. -/
theorem original_environment_timer_routing (initial : FlatTable × FlatTable)
    (worker : Worker) (pid : WG.PeerId) (timer : WG.PeerTimer) (jHi : UInt64) (ticks : Nat) :
    ProductRetainsRoutingCall (Env.runTimerSection worker (Leanux.liftWG (WG.timerCallback pid timer))) ∧
    ProductRetainsRoutingCall (Env.runTimers jHi) ∧
    ProductRetainsRoutingCall (Env.runTimersPlaceholder jHi) ∧
    ProductRetainsRoutingCall Env.idleTimers ∧
    Framing.SameView (fun w : World => routingView w.wg) (Env.advance ticks) ∧
    ProductRetainsRoutingCall Env.afterAdvance ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix (Env.runTimers jHi)) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix (Env.runTimersPlaceholder jHi)) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix Env.idleTimers) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix Env.afterAdvance) :=
  ⟨runTimerSection_routing worker _ (timerCallback_routing pid timer).liftWG,
    runTimers_routing jHi, runTimersPlaceholder_routing jHi,
    idleTimers_routing, advance_routing ticks, afterAdvance_routing,
    global_completion_lift World.wg initial _ (runTimers_routing jHi),
    global_completion_lift World.wg initial _ (runTimersPlaceholder_routing jHi),
    global_completion_lift World.wg initial _ idleTimers_routing,
    global_completion_lift World.wg initial _ afterAdvance_routing⟩

/-- Complete original receive-worker, ingress/flood and batch calls retain
routing on normal return from arbitrary Worlds. Concrete nested rescheduling and
inline NET_RX polling are included. Saved lists, queue capacity and finite bounds
add no successful-drain, residency, credit or packet-validity premise. Silent
lifts preserve optional state normally and prior safe journals on Stop. -/
theorem original_environment_traffic_routing (initial : FlatTable × FlatTable)
    (family port count tos dest addr : Nat) (msg : List UInt8) (ll : Bool)
    (messages : List (List UInt8)) (items : List Env.BatchItem) :
    ProductRetainsRoutingCall (WG.handshakeReceiveWorker (Env.nestedResched .receiveWorker)) ∧
    Framing.SameView (fun w : World => routingView w.wg) (Env.xmitMulticastLoop family addr) ∧
    ProductRetainsRoutingCall (Env.inject family port msg tos ll dest) ∧
    ProductRetainsRoutingCall (Env.flood count port family messages) ∧
    ProductRetainsRoutingCall Env.afterBatch ∧ ProductRetainsRoutingCall (Env.batch items) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix (WG.handshakeReceiveWorker (Env.nestedResched .receiveWorker))) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix (Env.inject family port msg tos ll dest)) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix (Env.flood count port family messages)) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix (Env.batch items)) :=
  ⟨handshakeReceiveWorker_routing, xmitMulticastLoop_routing family addr,
    inject_routing family port msg tos ll dest, flood_routing count port family messages,
    afterBatch_routing, batch_routing items,
    global_completion_lift World.wg initial _ handshakeReceiveWorker_routing,
    global_completion_lift World.wg initial _ (inject_routing family port msg tos ll dest),
    global_completion_lift World.wg initial _ (flood_routing count port family messages),
    global_completion_lift World.wg initial _ (batch_routing items)⟩

/-- Original environment controls retain routing normally, including the actual
MTU conversion and namespace worker. Environment deletion instead observes the
real lifecycle completions after its idle/pending-dump guards; erasure is
unconditional and semantic prefix preservation starts from optional routing/flat
agreement. Stops retain safe completed history without a returned World. -/
theorem original_environment_controls_completion (initial : FlatTable × FlatTable)
    (mtu family : Nat) :
    Framing.SameView (fun w : World => routingView w.wg) Env.requireIdleDevice ∧
    ProductRetainsRoutingCall Env.wgUp ∧ ProductRetainsRoutingCall Env.wgDown ∧
    Framing.SameView (fun w : World => routingView w.wg) (Env.setMtu mtu) ∧
    Framing.SameView (fun w : World => routingView w.wg) Env.routeIntoWg0 ∧
    Framing.SameView (fun w : World => routingView w.wg) (Env.wgDeladdr family) ∧
    Framing.SameView (fun w : World => routingView w.wg) (Env.wgDelroute family false 0 0 0 0 0) ∧
    ProductRetainsRoutingCall Env.observe ∧ ProductRetainsRoutingCall Env.netnsCleanup ∧
    Logged.ErasesPrefix envWgDeleteObserved Env.wgDelete ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      envWgDeleteObserved ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix Env.observe) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Logged.liftPrefix Env.netnsCleanup) :=
  ⟨requireIdleDevice_routing, envWgUp_routing, envWgDown_routing,
    envSetMtu_routing mtu, routeIntoWg0_routing, wgDeladdr_routing family,
    wgDelroute_routing family, observe_routing, netnsCleanup_routing,
    envWgDeleteObserved_erases, envWgDeleteObserved_global initial,
    global_completion_lift World.wg initial _ observe_routing,
    global_completion_lift World.wg initial _ netnsCleanup_routing⟩

/-- Original stepped dump start/chunk/receive/completion and whole wgGetDevice
retain routing on normal return. Cursor releases may retire resident peers;
no cursor validity, owner affiliation, residency or successful-drain assumption
is added. Silent lifts leave the journal unchanged on every outcome, preserve
optional state only normally, and retain prior history safety on Stop. This is
a local frame; initialized syscall/Runner composition is supplied below,
while packet authorization remains separate. -/
theorem original_dump_routing (initial : FlatTable × FlatTable) (fd : Nat) (seq : UInt32)
    (ref : WG.DeviceRef) (ctx : WG.DumpCtx) (skb : WG.NlSkb) :
    RetainsRoutingCall (WG.wgGetDeviceDone ctx) ∧
    RetainsRoutingCall (WG.wgGetDeviceDump ctx seq skb) ∧
    RetainsRoutingCall (WG.netlinkDump fd) ∧
    RetainsRoutingCall (WG.netlinkDumpStart fd ref) ∧
    RetainsRoutingCall (WG.netlinkRecvmsg fd) ∧
    RetainsRoutingCall (WG.wgGetDevice ref) ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix (WG.netlinkDump fd)) ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix (WG.netlinkDumpStart fd ref)) ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix (WG.netlinkRecvmsg fd)) ∧
    Logged.StatePrefixPreserves (fun h w _ => GlobalCompletionState initial h w) (CompletionSafe initial)
      (Logged.liftWGPrefix (WG.wgGetDevice ref)) :=
  ⟨wgGetDeviceDone_routing ctx, wgGetDeviceDump_routing ctx seq skb,
    netlinkDump_routing fd, netlinkDumpStart_routing fd ref,
    netlinkRecvmsg_routing fd, wgGetDevice_routing ref,
    global_completion_lift_wg initial _ (netlinkDump_routing fd),
    global_completion_lift_wg initial _ (netlinkDumpStart_routing fd ref),
    global_completion_lift_wg initial _ (netlinkRecvmsg_routing fd),
    global_completion_lift_wg initial _ (wgGetDevice_routing ref)⟩

/-- Every typed syscall/trace and both Runner flags retain exact execution,
without address-shape assumptions. The full observed Json × World erases to a
literal original-call source Runner; projecting its JSON gives executeTrace. -/
theorem original_routing_runner_erasure (call : Syscall) (trace : Runner.Trace)
    (placeholders : Bool) :
    Logged.ErasesPrefix (Configuration.dispatchObserved call) (dispatch call) ∧
    Logged.ErasesPrefix (Configuration.syscallObserved call) (syscall call) ∧
    Logged.ErasesOuter (Configuration.executeTraceObserved trace placeholders)
      (Configuration.sourceRunner trace placeholders) ∧
    (Configuration.sourceRunner trace placeholders).map Prod.fst =
      Runner.executeTrace trace placeholders :=
  ⟨Configuration.dispatchObserved_erases call, Configuration.syscallObserved_erases call,
    Configuration.executeTraceObserved_erases trace placeholders,
    Configuration.sourceRunner_json trace placeholders⟩

/-- Complete original dispatch and syscall suffixes preserve optional routing
and safe completed prefixes from explicit entry agreement and address shape.
Ordinary negative returns keep their actual cleanup; Stops retain history only. -/
theorem original_syscall_routing_prefix (initial : FlatTable × FlatTable) (call : Syscall)
    (shape : Configuration.SyscallAddressShape call) :
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Configuration.dispatchObserved call) ∧
    Logged.PrefixPreserves (fun h w => GlobalCompletionState initial h w.wg) (CompletionSafe initial)
      (Configuration.syscallObserved call) :=
  ⟨Configuration.dispatchObserved_global initial call shape,
    Configuration.syscallObserved_global initial call shape⟩

/-- Successful public parsing supplies the shape needed for initialized safe
completion history on every outcome and routing agreement in the actual normal
final World. The source connection includes that World, not merely its JSON
projection. This supplies neither earlier executed lookup certificates nor
packet authorization, raw-owner residency, key affiliation or trial packets. -/
theorem parsed_initialized_routing_execution (json : Lean.Json) (trace : Runner.Trace)
    (parsed : Runner.parseTrace json = .ok trace) (placeholders : Bool) :
    Logged.ErasesOuter (Configuration.executeTraceObserved trace placeholders)
      (Configuration.sourceRunner trace placeholders) ∧
    (Configuration.sourceRunner trace placeholders).map Prod.fst =
      Runner.executeTrace trace placeholders ∧
    CompletionSafe ([], [])
      (Logged.runPrefixOuter (Configuration.executeTraceObserved trace placeholders) []).2 ∧
    ∀ out, (Logged.runPrefixOuter (Configuration.executeTraceObserved trace placeholders) []).1 = .ok out →
      GlobalCompletionState ([], [])
        (Logged.runPrefixOuter (Configuration.executeTraceObserved trace placeholders) []).2 out.2.wg :=
  ⟨Configuration.executeTraceObserved_erases trace placeholders,
    Configuration.sourceRunner_json trace placeholders,
    Configuration.parsed_executeTraceObserved_routing json trace parsed placeholders⟩


open Std.Do Leanux.WG

/-- The original complete index lookup preserves the small nullable affiliation
invariant and successful handshake lookup returns its actual owner. The source
factor retains every original Stop and the fresh owner store-back, including
owner/target aliasing. Snapshot facts are derived from a separate actual helper
run; neither those facts nor Inv assert initialized reachability or stamp uniqueness. -/
theorem original_nullable_index_affiliation (kinds : List IndexKind) (index : Nat) :
    Affiliation.indexLookupSource kinds index = WG.indexLookup kinds index ∧
    (⦃fun w => ⌜Affiliation.Inv w⌝⦄ WG.indexLookup kinds index
      ⦃⇓? result w => ⌜Affiliation.Inv w ∧ ∀ owner borrowed,
        result = some (.handshake owner, borrowed) → borrowed = owner⌝⦄) ∧
    (∀ owner pid w v ambient ambient', ((Affiliation.acquireOwner owner).run w).run ambient = .ok ((some pid, v), ambient') →
      Affiliation.OwnerCertificate owner pid w) :=
  ⟨Affiliation.indexLookupSource_eq kinds index, Affiliation.indexLookup_spec kinds index,
    Affiliation.acquisition_certificate⟩

/-- Local original allocation/refusal, rotation and session contracts. NULL
allocation words are included; actual handshake reads derive compatibility in
beginSession. Slot aliases and absent old keys are allowed. These are normal
endpoint statements under the explicitly local invariant, not initialized
Runner affiliation or totality. The stronger old SlotAffiliation is unchanged. -/
theorem original_nullable_session_affiliation (word : Option PeerId) (pid : PeerId) (kid : KeypairId) :
    (⦃fun w => ⌜Affiliation.CreationInput word w⌝⦄ WG.keypairCreate word
      ⦃⇓? result w => ⌜Affiliation.Inv w ∧ ∀ id, result = some id →
        ∃ s stamp, Affiliation.view w = some s ∧ s.keys id = some (stamp, word) ∧ id < s.nextKey⌝⦄) ∧
    (⦃fun w => ⌜Affiliation.References pid [kid] (Affiliation.view w)⌝⦄ WG.addNewKeypair pid kid
      ⦃⇓? _ w => ⌜Affiliation.Inv w⌝⦄) ∧
    (⦃fun w => ⌜Affiliation.Inv w⌝⦄ WG.beginSession pid ⦃⇓? _ w => ⌜Affiliation.Inv w⌝⦄) :=
  ⟨Affiliation.keypairCreate_affiliation word, Affiliation.addNewKeypair_affiliation pid kid,
    Affiliation.beginSession_affiliation pid⟩

/-- Literal source factors expose the TX and RX acquisition expressions.
Successful strict TX acquisition derives positive credit and, from local slot
compatibility, the sending peer. Successful original decryption preserves the
packet's peer/key fields and uses the resident receiving key in its exact AEAD
equation. Reached-input affiliation, historical allocation uniqueness, public-key
intent, internal longest-prefix certificates and initialized path composition
remain separate; no current-table-at-wire-send claim is made. -/
theorem original_packet_affiliation_cuts (pid : PeerId) (kid : KeypairId)
    (entry : Option (IndexOwner × PeerId)) (state : Option Affiliation.State)
    (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Affiliation.sendStagedSource pid = WG.sendStagedPackets pid ∧
    Affiliation.consumeDataSource msg src ds = WG.consumeData msg src ds ∧
    (⦃fun w => ⌜Affiliation.view w = state⌝⦄ Affiliation.receiveKeyAcquire entry
      ⦃⇓? result w => ⌜Affiliation.view w = state ∧ ∀ key peer,
        result = (some key, some peer) → entry = some (.keypair key, peer)⌝⦄) ∧
    (∀ w v ambient ambient' d p, Affiliation.Inv w → w.dev = some d → d.peers[pid]? = some p →
      (p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid) →
      ((Affiliation.sendAcquire kid).run w).run ambient = .ok (((), v), ambient') →
      Framing.PeerBorrow.Borrowed (Framing.wgStoreView w) (some pid) (Framing.wgStoreView v)) ∧
    (∀ pkt out w v ambient ambient', ((WG.decryptPacket pkt).run w).run ambient = .ok ((some out, v), ambient') →
      ∃ d k, w.dev = some d ∧ d.keypairs[pkt.keypair]? = some k ∧
        out.peer = pkt.peer ∧ out.keypair = pkt.keypair ∧
        WG.aeadDecrypt k.receiving.key (WG.counterNonce (WG.u64le pkt.bytes 8)) (pkt.bytes.drop 16) [] = some out.bytes) :=
  ⟨Affiliation.sendStagedSource_eq pid, Affiliation.consumeDataSource_eq msg src ds,
    Affiliation.receiveKeyAcquire_spec entry state,
    fun w v ambient ambient' _ p hi hd hp hs hr => Affiliation.sendAcquire_owner kid pid p w v ambient ambient' hi hd hp hs hr,
    Affiliation.decryptPacket_fields⟩

/-- Original normal source/destination lookup answers refine the independent flat
winner at the actual query World. Failed acquisition is a Stop, not a None answer.
Actual packet constructors supply all-packet family/destination-byte shape; no
arbitrary mixed-family list or unbounded-Nat encoding equality is assumed. -/
theorem original_routing_lookup_and_packet_shapes (v4 : Bool) (addr : Nat)
    (bytes : List UInt8) (opts : Env.XmitOpts) :
    (∀ w v ambient ambient' xs peer, RoutedView (routingView w) xs →
      ((WG.lookupSrc (if v4 then 4 else 6) bytes).run w).run ambient = .ok ((peer, v), ambient') →
      PeerWinner (rootWidth v4) (sourceAddress v4 bytes) (selectedFlat v4 xs) peer) ∧
    (∀ w v ambient ambient' xs peer, RoutedView (routingView w) xs → addr < 2 ^ rootWidth v4 →
      ((WG.lookupDst (if v4 then 4 else 6) addr).run w).run ambient = .ok ((peer, v), ambient') →
      PeerWinner (rootWidth v4) addr (selectedFlat v4 xs) peer) ∧
    (⦃fun _ => ⌜True⌝⦄ Env.xmitPackets (if v4 then 4 else 6) addr bytes opts
      ⦃⇓? result _ => ⌜∀ packets mtu, result = .ok (packets, mtu) →
        ∀ packet ∈ packets, Packets.DestinationShape (if v4 then 4 else 6) addr packet.bytes⌝⦄) ∧
    Packets.DestinationShape 4 (WG.beAt bytes 12 4) (Env.Stack.rst4 bytes) ∧
    (∀ outer, (if v4 then 20 else 40) ≤ bytes.length →
      (⦃fun _ => ⌜True⌝⦄ WG.inetEcnDecapsulate (if v4 then 4 else 6) outer bytes
        ⦃⇓? out _ => ⌜Packets.AddressPreserved v4 bytes out⌝⦄)) :=
  ⟨fun w v ambient ambient' xs peer hi hr => lookupSrc_normal w v ambient ambient' xs v4 bytes peer hi hr,
    fun w v ambient ambient' xs peer hi ha hr => lookupDst_normal w v ambient ambient' xs v4 addr ha peer hi hr,
    Packets.xmitPackets_shape _ addr bytes opts, Packets.rst4_shape bytes,
    fun outer hl => Packets.inetEcnDecapsulate_address v4 outer bytes hl⟩

/-- Literal source factors and normal returned-packet/staging cuts retain exact
intermediate Worlds and original arguments. Routing agreement is an explicit
local entry premise. RX exposes the actual input/output family and preserved
source; TX derives query bounds from every actual header guard and identifies
the completed splice of the original packets with their caller-supplied MTU.
Initialized packet histories, authenticated key identity, copied trials and
routing at later encryption/wire-send time are not supplied by this contract. -/
theorem original_packet_routing_source_cuts (pid : PeerId) (pkt : RxPacket)
    (endpoint : Endpoint) (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    (WG.consumeDataDone pid pkt endpoint = (do
      let ready ← Packets.rxPrepare pid pkt endpoint
      match ready with | none => return none | some r => Packets.rxFinish pid r)) ∧
    (WG.wgXmit family addr packets mtu = (do
      if !(← Packets.txCheck family addr packets mtu) then return -EPROTONOSUPPORT
      let peer ← WG.lookupDst family addr
      match ← Packets.txSelect family packets mtu peer with
      | .error err => return err
      | .ok (pid, ready) => Packets.txFinish pid ready)) ∧
    (∀ w v ambient ambient' bytes xs, RoutedView (routingView w) xs →
      ((WG.consumeDataDone pid pkt endpoint).run w).run ambient = .ok ((some bytes, v), ambient') →
      ∃ v4 : Bool, WG.ipTunnelParseProtocol bytes = (if v4 then 4 else 6) ∧
        WG.ipTunnelParseProtocol pkt.bytes = (if v4 then 4 else 6) ∧
        PeerWinner (rootWidth v4) (sourceAddress v4 bytes) (selectedFlat v4 xs) (some pid) ∧
        sourceAddress v4 bytes = sourceAddress v4 pkt.bytes) ∧
    (∀ (v4 : Bool) w v ambient ambient' xs, RoutedView (routingView w) xs →
      ((WG.wgXmit (if v4 then 4 else 6) addr packets mtu).run w).run ambient = .ok ((0, v), ambient') →
      ∃ owner, Packets.TxHandoff (if v4 then 4 else 6) addr packets mtu w v ambient ambient' owner ∧
        PeerWinner (rootWidth v4) addr (selectedFlat v4 xs) (some owner) ∧
        ∀ packet ∈ packets, Packets.destinationField (if v4 then 4 else 6) packet.bytes = addr) :=
  ⟨Packets.consumeDataDone_factor pid pkt endpoint, Packets.wgXmit_factor family addr packets mtu,
    fun w v ambient ambient' bytes xs hi hr => Packets.consumeDataDone_authorized pid pkt endpoint w v ambient ambient' bytes xs hi hr,
    fun v4 w v ambient ambient' xs hi hr => Packets.wgXmit_authorized v4 addr packets mtu w v ambient ambient' xs hi hr⟩

/-- Local source-shaped session receipts: exact original erasure on all
inputs, exact R2 projection under its existing AllocationInv, and truthful
partial receipt histories on Stops from valid incoming receipt history. A Some front receipt links the actual entry,
nullable handshake word, allocation and peer read to the completed derivation.
This does not establish initialized session provenance or later residency. -/
theorem original_session_material_receipts (pid : PeerId) :
    Logged.ErasesStatePrefix (SessionOrigin.observed pid) (WG.beginSession pid) ∧
    Logged.StateProjectsUnder (fun h w _ => Lifetimes.AllocationInv h w) MaterialOrigin.life?
      (SessionOrigin.observed pid) (Lifetimes.beginSessionPrefix pid) ∧
    Logged.StatePrefixPreserves (fun h _ _ => MaterialOrigin.Valid SessionOrigin.Receipt.Valid h)
      (MaterialOrigin.Valid SessionOrigin.Receipt.Valid) (SessionOrigin.observed pid) ∧
    (∀ ctx w v ambient ambient', ((SessionOrigin.front pid).run w).run ambient = .ok ((some ctx, v), ambient') →
      ∃ readWorld initWorld deriveWorld readAmbient initAmbient deriveAmbient,
        SessionOrigin.Entered pid ctx w readWorld ambient readAmbient ∧
        ((WG.getPeer pid).run readWorld).run readAmbient = .ok ((ctx.peer, readWorld), readAmbient) ∧
        ((SessionOrigin.initKey ctx.slot (ctx.state == WG.HANDSHAKE_CONSUMED_RESPONSE) ctx.peer.remoteIndex).run readWorld).run readAmbient = .ok (((), initWorld), initAmbient) ∧
        ((branch .sessionInitiator (ctx.state == WG.HANDSHAKE_CONSUMED_RESPONSE) : WG.M Bool).run initWorld).run initAmbient = .ok ((ctx.initiator, deriveWorld), deriveAmbient) ∧
        ((WG.deriveKeys ctx.slot ctx.initiator ctx.peer.chainingKey).run deriveWorld).run deriveAmbient = .ok (((), v), ambient') ∧
        MaterialOrigin.Derivation ctx.slot ctx.initiator ctx.peer.chainingKey deriveWorld v deriveAmbient ambient') ∧
    (∀ (w : WGWorld) (d : Device) (word : Option PeerId) (id : KeypairId), id < d.nextKeypairId →
      (Lifetimes.keyAllocationDevice d (w.keypairCounter + 1) word).nextKeypairId = d.nextKeypairId + 1 ∧
      (Lifetimes.keyAllocationDevice d (w.keypairCounter + 1) word).ifindex = d.ifindex ∧
      (Lifetimes.keyAllocationDevice d (w.keypairCounter + 1) word).keypairs[d.nextKeypairId]? =
        some {internalId := w.keypairCounter + 1, peer := word} ∧
      (Lifetimes.keyAllocationDevice d (w.keypairCounter + 1) word).keypairs[id]? = d.keypairs[id]?) :=
  ⟨SessionOrigin.observed_erases pid, SessionOrigin.observed_projects pid,
    SessionOrigin.observed_valid pid, SessionOrigin.front_material pid, MaterialOrigin.allocation_fields⟩

/-- Local RX admission/decrypt receipts occur in the original consume and
worker source paths. They retain the complete allocated/stored packet and
exact index/acquisition/peer-check chain. Successful decryption changes only
nonce/bytes and uses the actual resident receiving material. Erasure
is unconditional; receipt validity is preserved from valid incoming
history (including empty), independently of the AllocationInv required by R2 projection. Initialized session matching, unique original ciphertext and
receipt-to-poll/Stack transport are separate obligations. -/
theorem original_rx_origin_receipts (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Logged.ErasesStatePrefix (RxOrigin.consume msg src ds) (WG.consumeData msg src ds) ∧
    Logged.StateProjectsUnder (fun h w _ => Lifetimes.AllocationInv h w) MaterialOrigin.life?
      (RxOrigin.consume msg src ds) (Lifetimes.consumeDataPrefix msg src ds) ∧
    Logged.StatePrefixPreserves (fun h _ _ => MaterialOrigin.Valid RxOrigin.Receipt.Valid h)
      (MaterialOrigin.Valid RxOrigin.Receipt.Valid) (RxOrigin.consume msg src ds) ∧
    Logged.ErasesStatePrefix RxOrigin.prepare Queues.RxWorkers.prepareSource ∧
    Logged.StateProjectsUnder (fun h w _ => Lifetimes.AllocationInv h w) MaterialOrigin.life?
      RxOrigin.prepare Queues.RxWorkers.preparePrefix ∧
    Logged.StatePrefixPreserves (fun h _ _ => MaterialOrigin.Valid RxOrigin.Receipt.Valid h)
      (MaterialOrigin.Valid RxOrigin.Receipt.Valid) RxOrigin.prepare ∧
    (∀ ctx w v ambient ambient', ((RxOrigin.admitSource msg src ds).run w).run ambient = .ok ((some ctx, v), ambient') →
      RxOrigin.Admitted msg src ds ctx w v ambient ambient') ∧
    (∀ id (r : Logged.WGRunWitness (RxPacket × Option RxPacket)) out,
      r.Valid (RxOrigin.readDecrypt id) → r.value.2 = some out →
      ∃ d k, r.before.dev = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
        d.keypairs[r.value.1.keypair]? = some k ∧ k.receiving.isValid = true ∧
        ((WG.decryptPacket r.value.1).run r.before).run r.ambientBefore = .ok ((some out, r.after), r.ambientAfter) ∧
        out = {r.value.1 with nonce := WG.u64le r.value.1.bytes 8, bytes := out.bytes} ∧
        WG.aeadDecrypt k.receiving.key (WG.counterNonce (WG.u64le r.value.1.bytes 8))
          (r.value.1.bytes.drop 16) [] = some out.bytes) :=
  ⟨RxOrigin.consume_erases msg src ds, RxOrigin.consume_projects msg src ds,
    RxOrigin.consume_valid msg src ds, RxOrigin.prepare_erases, RxOrigin.prepare_projects,
    RxOrigin.prepare_valid, RxOrigin.admission_execution msg src ds, RxOrigin.decrypt_receipt⟩

/-- Local material support uses one actual successful session-front witness for
both receiving material and the nullable keep-or-clear owner. The actual entry
peer/state/word are recovered without affiliation assumptions. Support is
installed before the session tail, which may delete the new key. Original
erasure is unconditional; R2 projection uses exactly its prior AllocationInv.
Valid incoming receipts remain valid on every outcome. This is a local adapter,
not initialized Runner origin or cryptographic peer-identity authentication. -/
theorem original_session_material_retention (pid : PeerId) :
    Logged.ErasesStatePrefix (Origins.localSession pid) (WG.beginSession pid) ∧
    Logged.StateProjectsUnder (fun h w _ => Lifetimes.AllocationInv h w) Origins.lifetime
      (Origins.localSession pid) (Lifetimes.beginSessionPrefix pid) ∧
    Logged.StatePrefixPreserves (fun h _ _ => Origins.Valid h) Origins.Valid (Origins.localSession pid) ∧
    Logged.StatePrefixPreserves
      (fun h w _ => MaterialOrigin.Valid SessionOrigin.Receipt.Valid (h.filterMap Origins.sessionDecode) ∧
        Origins.Inv (Origins.sessions h) w)
      (fun h => MaterialOrigin.Valid SessionOrigin.Receipt.Valid (h.filterMap Origins.sessionDecode))
      (Origins.localSession pid) ∧
    (∀ ctx w v ambient ambient', ((SessionOrigin.front pid).run w).run ambient = .ok ((some ctx,v),ambient') →
      ∃ d key, w.dev = some d ∧ d.peers[pid]? = some ctx.peer ∧
        ctx.state = ctx.peer.handshakeState ∧ ctx.word = ctx.peer.handshakeEntryPeer ∧
        ctx.slot = d.nextKeypairId ∧
        Origins.view v = some (d.ifindex, fun q => if ctx.slot = q then some key else d.keypairs[q]?) ∧
        key.internalId = w.keypairCounter + 1 ∧ key.peer = ctx.word ∧ key.receiving.isValid = true) ∧
    (∀ kp w v result ambient ambient', ((SessionOrigin.tail pid kp).run w).run ambient = .ok ((result,v),ambient') → Origins.Retains w v) ∧
    (∀ word w v result ambient ambient', ((WG.keypairCreate word).run w).run ambient = .ok ((result,v),ambient') → Origins.Retains w v) :=
  ⟨Origins.localSession_erases pid, Origins.localSession_projects pid,
    Origins.localSession_valid pid, Origins.localSession_support pid,
    Origins.front_effect pid, fun kp _ _ _ ambient ambient' hr => Origins.tail_retains pid kp ambient ambient' hr,
    Origins.create_retains⟩

/-- An actual successful local decrypt appends its full run receipt after a
matching session receipt in the SAME supplied journal. Incoming material support
is explicit: an arbitrary supplied witness may be a standalone original run,
not an earlier reached Runner occurrence. The exact stored packet, material,
AEAD and record-transform equations are retained. Nullable owner support does
not identify packet.peer with the session peer. All-input erasure and the old
same-input R2 projection are independent of this support premise. -/
theorem original_decrypt_material_history (id : SkbId) :
    Logged.ErasesStatePrefix (Origins.localDecrypt id) (RxOrigin.readDecrypt id) ∧
    Logged.StateProjectsUnder (fun h w _ => Lifetimes.AllocationInv h w) Origins.lifetime
      (Origins.localDecrypt id) (RxOrigin.readDecryptPrefix id) ∧
    Logged.StatePrefixPreserves (fun h _ _ => Origins.Valid h) Origins.Valid (Origins.localDecrypt id) ∧
    Logged.StatePrefixPreserves (fun h w _ => Origins.Inv (Origins.sessions h) w) (fun _ => True)
      (Origins.localDecrypt id) ∧
    (∀ w ambient h,
      let observed := Logged.runWGPrefix (RxOrigin.readDecryptPrefix id) w ambient (h.filterMap Origins.lifetime)
      let suffix := (observed.2.drop (h.filterMap Origins.lifetime).length).map Origins.Event.life
      Logged.runWGPrefix (Origins.localDecrypt id) w ambient h = match observed.1 with
        | .error e => (.error e,h ++ suffix)
        | .ok ((result,v),ambient') => (.ok ((result,v),ambient'),h ++ suffix ++ [.rx (.decrypt id ⟨result,w,v,ambient,ambient'⟩)])) ∧
    (∀ w ambient h packet out v ambient', Origins.Inv (Origins.sessions h) w →
      (Logged.runWGPrefix (Origins.localDecrypt id) w ambient h).1 = .ok (((packet,some out),v),ambient') →
      ∃ (suffix : List Lifetimes.LifetimeEvent) (d : Device) (k : Keypair) (pid : PeerId)
        (r : Logged.WGRunWitness (Option SessionOrigin.Context)) (ctx : SessionOrigin.Context)
        (originDev : Device) (original : Keypair) (before middle : List Origins.Event),
        (Logged.runWGPrefix (Origins.localDecrypt id) w ambient h).2 =
          h ++ suffix.map Origins.Event.life ++ [.rx (.decrypt id ⟨(packet,some out),w,v,ambient,ambient'⟩)] ∧
        h = before ++ [.session (.material pid r)] ++ middle ∧
        r.Valid (SessionOrigin.front pid) ∧ r.value = some ctx ∧ ctx.slot = packet.keypair ∧
        r.after.dev = some originDev ∧ originDev.ifindex = d.ifindex ∧
        originDev.keypairs[packet.keypair]? = some original ∧ original.receiving.isValid = true ∧
        original.peer = ctx.word ∧ MaterialOrigin.material k = MaterialOrigin.material original ∧
        Origins.WordLe k.peer ctx.word ∧ w.dev = some d ∧ d.rxSkbs[id]? = some packet ∧
        d.keypairs[packet.keypair]? = some k ∧ ((WG.decryptPacket packet).run w).run ambient = .ok ((some out,v),ambient') ∧
        out = {packet with nonce := WG.u64le packet.bytes 8, bytes := out.bytes} ∧
        WG.aeadDecrypt k.receiving.key (WG.counterNonce (WG.u64le packet.bytes 8))
          (packet.bytes.drop 16) [] = some out.bytes) :=
  ⟨Origins.localDecrypt_erases id, Origins.localDecrypt_projects id,
    Origins.localDecrypt_valid id, Origins.localDecrypt_support id,
    Origins.localDecrypt_run id, Origins.localDecrypt_origin id⟩

/-- Original owner acquisition and the complete index scan retain receiving
material on every normal return, including a None result that clears the peer
word. The keypair endpoint retains every other full-record field and derives
keep-or-clear from the actual borrow. No affiliation, non-NULL, residency or
reference-credit premise is added. The existing access observer preserves
supplied session support normally and receipt validity on Stop; it does not
establish initialized occurrence chronology or packet/peer authorization. -/
theorem original_index_material_retention (kinds : List IndexKind) (index : Nat) :
    Affiliation.indexLookupSource kinds index = WG.indexLookup kinds index ∧
    (∀ owner w result v ambient ambient', ((Affiliation.acquireOwner owner).run w).run ambient = .ok ((result,v),ambient') →
      Origins.Retains w v) ∧
    (∀ id w v result ambient ambient', ((Affiliation.acquireOwner (.keypair id)).run w).run ambient = .ok ((result,v),ambient') →
      ∃ (d : Device) (old : Keypair), w.dev = some d ∧ d.keypairs[id]? = some old ∧
        Origins.WordLe result old.peer ∧
        Origins.view v = some (d.ifindex, fun q =>
          if id = q then some {old with peer := result} else d.keypairs[q]?)) ∧
    (∀ w result v ambient ambient', ((WG.indexLookup kinds index).run w).run ambient = .ok ((result,v),ambient') →
      Origins.Retains w v) ∧
    Logged.ErasesStatePrefix
      (Origins.accessNative (R := SessionOrigin.Receipt) (Lifetimes.indexLookupPrefix kinds index))
      (WG.indexLookup kinds index) ∧
    Logged.StatePrefixPreserves (fun h w _ => Origins.SessionInv h w) (MaterialOrigin.Valid SessionOrigin.Receipt.Valid)
      (Origins.accessNative (Lifetimes.indexLookupPrefix kinds index)) :=
  ⟨Affiliation.indexLookupSource_eq kinds index,
    fun owner w result v ambient ambient' hr =>
      (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
        (Origins.acquireOwner_retains owner) w ambient result v ambient' hr,
    Origins.acquireOwner_keypair_effect,
    fun w result v ambient ambient' hr =>
      (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
        (Origins.indexLookup_retains kinds index) w ambient result v ambient' hr,
    Logged.focusStatePrefix_erases _ _ (Lifetimes.indexLookupPrefix_erases kinds index),
    Origins.indexLookup_support kinds index⟩

/-- Actual persistent caller source cuts use the enriched adapters once. Both
handshake session branches share the literal original source factor; the decrypt
cut captures the stored getter/decrypt before publication. Erasure covers arbitrary
incoming histories and all original results/Stops. Copied trials and admission
receipt injection are not asserted by these committed caller equations. -/
theorem original_origin_history_injection :
    Origins.HistoryAdapters.ops.session = (fun pid => Logged.liftWGObserver (Origins.localSession pid)) ∧
    (∀ pid, Origins.HandshakeSources.responseWith Origins.HandshakeSources.original pid =
      WG.sendHandshakeResponse pid) ∧
    (∀ msg src loaded mac,
      Origins.HandshakeSources.afterMacWith Origins.HandshakeSources.original msg src loaded mac =
        Cookies.afterMac msg src loaded mac) ∧
    Queues.RxHistory.decryptStep =
      Queues.RxWorkers.decryptWith Origins.HistoryAdapters.prepare
        (fun pid => Queues.RxHistory.mixed (Logged.liftWGObserver (Lifetimes.peerPutMixed (some pid))))
        Queues.RxHistory.napiSoftirq Queues.RxHistory.napiIrqExit ∧
    (∀ a : Activation, a.worker = .receiveWorker →
      Queues.RxHistory.activationIteration a = Origins.HistoryAdapters.receiveIteration) ∧
    Queues.RxHistory.handshakeReceiveWorker =
      Logged.workerLoopPrefix .receiveWorker none Origins.HistoryAdapters.receiveStep
        (Queues.RxHistory.nestedResched .receiveWorker)
        (WG.MAX_QUEUED_INCOMING_HANDSHAKES + 1) "the handshake queue did not drain" ∧
    Logged.ErasesPrefix Queues.RxHistory.decryptStep (WG.decryptStep Env.napiSoftirq Env.napiIrqExit) ∧
    (∀ a, Logged.ErasesPrefix (Queues.RxHistory.activationIteration a) (Env.Activation.iter a)) ∧
    Logged.ErasesPrefix Queues.RxHistory.handshakeReceiveWorker
      (WG.handshakeReceiveWorker (Env.nestedResched .receiveWorker)) := by
  refine ⟨rfl, Origins.HandshakeSources.response_original, Origins.HandshakeSources.afterMac_original,
    rfl, ?_, rfl, Queues.RxHistory.decryptStep_erases,
    Queues.RxHistory.activationIteration_erases, Queues.RxHistory.handshakeReceiveWorker_erases⟩
  intro a ha
  simp only [Queues.RxHistory.activationIteration, ha]

/-- Same-input full R2 audit/probe projection is conditional on the existing
AuditInv. The injected cuts preserve receipt validity from valid incoming history;
they do not repair fabricated receipts. Existing R4 completion/linkage predicates
retain their meanings under the actual metadata suffix. These local contracts do
not establish initialized material support, admission origin or peer identity. -/
theorem original_origin_history_projection :
    Logged.ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent Queues.RxHistory.decryptStep
      (Lifetimes.auditFocus (Lifetimes.decryptStepPrefix Lifetimes.napiSoftirqPrefix Lifetimes.napiIrqExitPrefix)) ∧
    (∀ a, Logged.ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent
      (Queues.RxHistory.activationIteration a) (Lifetimes.auditFocus (Lifetimes.activationIterPrefix a))) ∧
    Logged.ProjectsUnder Lifetimes.AuditInv Queues.RxHistory.auditEvent Queues.RxHistory.handshakeReceiveWorker
      (Lifetimes.handshakeReceiveWorkerAudit (Lifetimes.nestedReschedAudit .receiveWorker)) ∧
    Logged.PrefixPreserves (fun h _ => Origins.HistoryAdapters.Valid h) Origins.HistoryAdapters.Valid
      Origins.HistoryAdapters.prepare ∧
    Logged.PrefixPreserves (fun h _ => Origins.HistoryAdapters.Valid h) Origins.HistoryAdapters.Valid
      Origins.HistoryAdapters.receiveStep ∧
    Logged.PrefixPreserves (fun h _ => Origins.HistoryAdapters.Valid h) Origins.HistoryAdapters.Valid
      Origins.HistoryAdapters.receiveIteration ∧
    (∀ (α : Type) (a : Logged.PrefixM Origins.Event α),
      Queues.RxCompletion.Preserves Queues.RxCompletion.historyEvent (Origins.HistoryAdapters.focus a) ∧
      Queues.RxLink.Preserves Queues.RxLink.HistoryLinked (Origins.HistoryAdapters.focus a) ∧
      Queues.RxLink.Preserves Queues.RxLink.HistoryReceiptsValid (Origins.HistoryAdapters.focus a)) :=
  ⟨Queues.RxHistory.decryptStep_projects, Queues.RxHistory.activationIteration_projects,
    Queues.RxHistory.handshakeReceiveWorker_projects, Origins.HistoryAdapters.prepare_valid,
    Origins.HistoryAdapters.receiveStep_valid, Origins.HistoryAdapters.receiveIteration_valid,
    fun _ a => ⟨Queues.RxCompletion.origin_quiet a, Queues.RxLink.linked_origin a,
      Queues.RxLink.receipts_origin a⟩⟩


/-- Concrete original leaves retain receiving material on normal returns from
arbitrary Worlds. Erasure, invalidation and a cleared nullable owner are allowed.
The generic support consequence transports an already supplied session history;
this is neither initialized origin nor packet/public-key authorization. -/
theorem original_material_retaining_leaves :
    (∀ (α : Type) (a : Leanux.M α), Framing.SameProductStore a → Origins.Retaining.ProjectedRetainsCall World.wg a) ∧
    (∀ (α : Type) (a : Leanux.M α), Framing.SameView (fun w : World => Framing.wgStoreView w.wg) a → Origins.Retaining.ProjectedRetainsCall World.wg a) ∧
    (∀ pid, Origins.Retaining.RetainsCall (WG.peerGet pid)) ∧
    (∀ peer, Origins.Retaining.RetainsCall (WG.peerPut peer)) ∧
    (∀ kp, Origins.Retaining.RetainsCall (WG.keypairGet kp)) ∧
    (∀ kp now, Origins.Retaining.RetainsCall (WG.keypairPut kp now)) ∧
    (∀ word, Origins.Retaining.RetainsCall (WG.keypairCreate word)) ∧
    (∀ pid, Origins.Retaining.RetainsCall (WG.createInitiation pid) ∧
      Origins.Retaining.RetainsCall (WG.createResponse pid) ∧
      Origins.Retaining.RetainsCall (WG.sendHandshakeInitiation pid) ∧
      Origins.Retaining.RetainsCall (WG.timersSessionDerived pid)) ∧
    (∀ msg, Origins.Retaining.RetainsCall (WG.consumeInitiation msg) ∧
      Origins.Retaining.RetainsCall (WG.consumeResponse msg) ∧
      Origins.Retaining.RetainsCall (WG.cookieMessageConsume msg)) ∧
    (∀ (α : Type) (a : Leanux.M α) history w result v,
      Origins.Retaining.ProjectedRetainsCall World.wg a → Origins.Inv history w.wg →
      a.run w = .ok (result,v) → Origins.Inv history v.wg) :=
  ⟨fun _ _ h => Origins.Retaining.of_view (Origins.kernel (project := id) h),
    fun _ _ h => Origins.Retaining.of_view (Origins.sameView_of_sameWG (project := World.wg) h),
    fun pid => Origins.Retaining.of_view (Origins.Retaining.peerGet_material pid),
    fun peer => Origins.Retaining.of_view (Origins.Retaining.peerPut_material peer),
    Origins.Retaining.keypairGet_material, Origins.Retaining.keypairPut_material,
    Origins.Retaining.keypairCreate_material,
    fun pid => ⟨Origins.Retaining.of_view (Origins.Retaining.createInitiation_material pid),
      Origins.Retaining.of_view (Origins.Retaining.createResponse_material pid),
      Origins.Retaining.of_view (Origins.Retaining.sendHandshakeInitiation_material pid),
      Origins.Retaining.of_view (Origins.Retaining.timersSessionDerived_material pid)⟩,
    fun msg => ⟨Origins.Retaining.consumeInitiation_material msg,
      Origins.Retaining.consumeResponse_material msg, Origins.Retaining.cookieMessageConsume_material msg⟩,
    fun _ _ _ _ _ _ h hi hr => h.support hi hr⟩

/-- Original packet and concrete NAPI/Stack paths retain receiving material.
Crypt iterations use their actual checksum, IRQ, softirq and plain rescheduling
callbacks. This does not frame the session-installing receive worker/scheduler,
or guarantee residence, reference funding, callback completion or packet identity. -/
theorem original_material_retaining_traffic :
    (∀ pid, Origins.Retaining.RetainsCall (WG.sendStagedPackets pid) ∧
      Origins.Retaining.RetainsCall (WG.sendKeepalive pid) ∧
      Origins.Retaining.RetainsCall (WG.txStep pid) ∧
      Origins.Retaining.ProductRetainsCall (WG.txIter pid (Env.condResched .txWorker))) ∧
    (∀ family addr packets mtu, Origins.Retaining.RetainsCall (WG.wgXmit family addr packets mtu)) ∧
    (∀ msg src, Origins.Retaining.RetainsCall (WG.wgReceive msg src)) ∧
    (∀ msg src ds, Origins.Retaining.RetainsCall (WG.consumeData msg src ds)) ∧
    (∀ pid pkt endpoint, Origins.Retaining.RetainsCall (WG.consumeDataDone pid pkt endpoint)) ∧
    (∀ pid budget, Origins.Retaining.ProductRetainsCall
      (WG.rxPoll pid budget (fun xs => xs.forM Env.deliverInner))) ∧
    Origins.Retaining.ProductRetainsCall Env.napiSoftirq ∧
    Origins.Retaining.ProductRetainsCall Env.napiIrqExit ∧
    Origins.Retaining.ProductRetainsCall Env.pollScheduledInline ∧
    Origins.Retaining.ProductRetainsCall (WG.encryptIter Env.checksumHelp Env.napiSoftirq
      (Env.condResched .encryptWorker)) ∧
    Origins.Retaining.ProductRetainsCall (WG.decryptIter Env.napiSoftirq Env.napiIrqExit
      (Env.condResched .decryptWorker)) ∧
    (∀ bytes, Origins.Retaining.ProductRetainsCall (Env.deliverInner bytes)) :=
  ⟨fun pid => ⟨Origins.Retaining.sendStagedPackets_material pid,
      Origins.Retaining.sendKeepalive_material pid, Origins.Retaining.txStep_material pid,
      Origins.Retaining.actualTxIter_material pid⟩,
    Origins.Retaining.wgXmit_material, Origins.Retaining.wgReceive_material,
    Origins.Retaining.consumeData_material, Origins.Retaining.consumeDataDone_material,
    Origins.Retaining.actualRxPoll_material, Origins.Retaining.napiSoftirq_material,
    Origins.Retaining.napiIrqExit_material, Origins.Retaining.pollScheduledInline_material,
    Origins.Retaining.actualEncryptIter_material, Origins.Retaining.actualDecryptIter_material,
    Origins.Retaining.deliverInner_material⟩

/-- Actual clear/flush/timer/removal and guarded device lifecycle calls retain
receiving material at normal endpoints, including ordinary negative results.
Saved lists and aliased old slots need no validity/survival premise. Creation
uses the whole guarded empty-or-unchanged endpoint; arbitrary wgNewlink and
session installation are deliberately not asserted to retain this view. -/
theorem original_material_retaining_lifecycle :
    (∀ pid, Origins.Retaining.RetainsCall (WG.keypairsClear pid) ∧
      Origins.Retaining.RetainsCall (WG.expireCurrentPeerKeypairs pid) ∧
      Origins.Retaining.RetainsCall (WG.handshakeSendWorker pid) ∧
      Origins.Retaining.RetainsCall (WG.queuedExpiredZeroKeyMaterial pid) ∧
      Origins.Retaining.RetainsCall (WG.timersStop pid)) ∧
    (∀ upto, Origins.Retaining.RetainsCall (WG.drainHandshakeSendWq upto)) ∧
    (∀ peer, Origins.Retaining.RetainsCall (WG.peerRemove peer)) ∧
    Origins.Retaining.RetainsCall WG.peerRemoveAll ∧
    (∀ pid timer, Origins.Retaining.RetainsCall (WG.timerCallback pid timer)) ∧
    Origins.Retaining.RetainsCall WG.wgOpen ∧
    Origins.Retaining.RetainsCall WG.wgUp ∧
    Origins.Retaining.RetainsCall WG.wgDown ∧
    Origins.Retaining.RetainsCall WG.netnsPreExit ∧
    Origins.Retaining.RetainsCall WG.wgCreate ∧
    Origins.Retaining.RetainsCall WG.wgDestruct ∧
    Origins.Retaining.RetainsCall WG.wgDelete :=
  ⟨fun pid => ⟨Origins.Retaining.keypairsClear_material pid,
      Origins.Retaining.expireCurrentPeerKeypairs_material pid,
      Origins.Retaining.handshakeSendWorker_material pid,
      Origins.Retaining.queuedExpiredZeroKeyMaterial_material pid,
      Origins.Retaining.timersStop_material pid⟩,
    Origins.Retaining.drainHandshakeSendWq_material, Origins.Retaining.peerRemove_material,
    Origins.Retaining.peerRemoveAll_material, Origins.Retaining.timerCallback_material,
    Origins.Retaining.wgOpen_material, Origins.Retaining.wgUp_material,
    Origins.Retaining.wgDown_material, Origins.Retaining.of_view Origins.Retaining.netnsPreExit_material,
    Origins.Retaining.wgCreate_material, Origins.Retaining.wgDestruct_material,
    Origins.Retaining.wgDelete_material⟩

/-- The existing session/decrypt/poll/filter cuts preserve supplied stateful
support. Every successful decrypt receipt has full material and run evidence
from its strict earlier journal prefix at its captured entry World. Saved filter
entries retain that exact prefix's lifetime projection and material support.
This is not initialized provenance, R2 lifetime validity or copied-trial receipt
coverage; a stopped execution returns safe history, not a World. -/
theorem original_origin_support_cuts :
    (∀ pid, Origins.HistorySupport.Preserves (Origins.HistoryAdapters.session pid)) ∧
    (∀ id, Origins.HistorySupport.Preserves (Origins.HistoryAdapters.decrypt id)) ∧
    Origins.HistorySupport.Preserves Origins.HistoryAdapters.prepare ∧
    (∀ pid budget, Origins.HistorySupport.Preserves (Queues.RxHistory.observePoll pid budget)) ∧
    Origins.HistorySupport.Preserves (Queues.RxHistory.audit Lifetimes.consistentFilterAudit) ∧
    (∀ h pre post id (r : Logged.WGRunWitness (RxPacket × Option RxPacket)) out,
      Origins.HistorySupport.HistorySafe h → h = pre ++ .rx (.decrypt id r) :: post →
      r.value.2 = some out →
      ∃ d k, r.before.dev = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
        d.keypairs[r.value.1.keypair]? = some k ∧
        Origins.Supported (Origins.HistorySupport.sessions pre) d.ifindex r.value.1.keypair k ∧
        ((WG.decryptPacket r.value.1).run r.before).run r.ambientBefore = .ok ((some out,r.after),r.ambientAfter) ∧
        out = {r.value.1 with nonce := u64le r.value.1.bytes 8, bytes := out.bytes} ∧
        aeadDecrypt k.receiving.key (counterNonce (u64le r.value.1.bytes 8))
          (r.value.1.bytes.drop 16) [] = some out.bytes) ∧
    (∀ h pre post p, Origins.HistorySupport.HistorySafe h →
      h = pre ++ .audit (.probe p) :: post →
      p.history = Queues.RxHistory.prior pre ∧ Origins.HistorySupport.StateSupported pre p.world) :=
  ⟨Origins.HistorySupport.session, Origins.HistorySupport.decrypt,
    Origins.HistorySupport.prepare, Origins.HistorySupport.poll,
    Origins.HistorySupport.filter_probe, Origins.HistorySupport.HistorySafe.decrypt,
    Origins.HistorySupport.HistorySafe.probe⟩

/-- Concrete receive, crypt, NAPI and scheduler callers preserve the same
supplied support on the existing observer. Session installation composes its
actual receipt contract, while non-installing leaves use concrete full-material
retention. Filter-entry evidence includes Stops but is not a claim about the
internal origin receipts of isolated copied trials. -/
theorem original_origin_support_callers :
    Origins.HistorySupport.Preserves Origins.HistoryAdapters.receiveStep ∧
    Origins.HistorySupport.Preserves Origins.HistoryAdapters.receiveIteration ∧
    Origins.HistorySupport.Preserves Queues.RxHistory.encryptIteration ∧
    Origins.HistorySupport.Preserves Queues.RxHistory.decryptStep ∧
    Origins.HistorySupport.Preserves Queues.RxHistory.decryptIteration ∧
    (∀ pid, Origins.HistorySupport.Preserves (Queues.RxHistory.cryptAhead pid)) ∧
    (∀ a, Origins.HistorySupport.Preserves (Queues.RxHistory.activationIteration a) ∧
      Origins.HistorySupport.Preserves (Queues.RxHistory.activationRun a)) ∧
    (∀ worker, Origins.HistorySupport.Preserves (Queues.RxHistory.dispatch worker)) ∧
    (∀ stack, Origins.HistorySupport.Preserves (Queues.RxHistory.schedule stack)) ∧
    (∀ worker, Origins.HistorySupport.Preserves (Queues.RxHistory.nestedResched worker)) ∧
    Origins.HistorySupport.Preserves Queues.RxHistory.napiSoftirq ∧
    Origins.HistorySupport.Preserves Queues.RxHistory.pollScheduledInline ∧
    Origins.HistorySupport.Preserves Queues.RxHistory.napiIrqExit :=
  ⟨Origins.HistorySupport.receiveStep, Origins.HistorySupport.receiveIteration,
    Origins.HistorySupport.encryptIteration, Origins.HistorySupport.decryptStep,
    Origins.HistorySupport.decryptIteration, Origins.HistorySupport.cryptAhead,
    fun a => ⟨Origins.HistorySupport.activationIteration a, Origins.HistorySupport.activationRun a⟩,
    Origins.HistorySupport.dispatch, Origins.HistorySupport.schedule,
    Origins.HistorySupport.nestedResched, Origins.HistorySupport.napiSoftirq,
    Origins.HistorySupport.pollScheduledInline, Origins.HistorySupport.napiIrqExit⟩

/-- Both receive-worker entrances and every existing deferred/remaining Env
constructor compose stateful origin support, including actual timer, traffic,
batch and control suffixes. Normal results retain support at their returned
World; every outcome retains positional receipt/probe checks. Initial support,
configuration/dump composition, initialized Runner and configured peer identity
are separate obligations. No observer or older R2/R4 predicate is changed. -/
theorem original_origin_support_environment :
    (∀ worker (body : Queues.RxHistory.Obs Unit), Origins.HistorySupport.Preserves body →
      Origins.HistorySupport.Preserves (Logged.runWorkerPrefix worker body)) ∧
    Origins.HistorySupport.Preserves Queues.RxHistory.handshakeReceiveWorker ∧
    (∀ call, Origins.HistorySupport.Preserves (Queues.RxHistory.deferred call)) ∧
    (∀ call, Origins.HistorySupport.Preserves (Queues.RxHistory.remaining call)) :=
  ⟨Origins.HistorySupport.runWorker, Origins.HistorySupport.handshakeReceiveWorker,
    Origins.HistorySupport.deferred, Origins.HistorySupport.remaining⟩

/-- Actual peer creation, allowed-IP insertion and complete device configuration
retain full receiving material and the keep-or-clear owner relation on every
normal return, including partial updates returning negative errno. Deletion and
invalidation are allowed; no returned World is asserted after a Stop. -/
theorem original_material_retaining_configuration :
    (∀ key psk, Framing.SameView Origins.view (WG.peerCreate key psk)) ∧
    (∀ pid psk, Framing.SameView Origins.view (WG.handshakeInit pid psk)) ∧
    (∀ family addr cidr pid, Framing.SameView Origins.view (WG.insert family addr cidr pid)) ∧
    (∀ pid ip, Framing.SameView Origins.view (WG.setAllowedip pid ip)) ∧
    (∀ attrs, Origins.Retaining.RetainsCall (WG.setPeerCmd attrs)) ∧
    (∀ attrs, Origins.Retaining.RetainsCall (WG.wgSetDevice attrs)) :=
  ⟨Origins.Retaining.peerCreate_material, Origins.Retaining.handshakeInit_material,
    Origins.Retaining.insert_material, Origins.Retaining.setAllowedip_material,
    Origins.Retaining.setPeerCmd_material, Origins.Retaining.wgSetDevice_material⟩

/-- Cursor acquisition/release, dump callbacks, socket queues and the original
bounded whole-dump loop preserve every receiving-material view field on normal
return. Arbitrary cursor values need no validity, residency or drain premise. -/
theorem original_material_retaining_dump :
    (∀ ctx, Framing.SameView Origins.view (WG.wgGetDeviceDone ctx)) ∧
    (∀ ctx seq skb, Framing.SameView Origins.view (WG.wgGetDeviceDump ctx seq skb)) ∧
    (∀ fd, Framing.SameView Origins.view (WG.netlinkDump fd)) ∧
    (∀ fd ref, Framing.SameView Origins.view (WG.netlinkDumpStart fd ref)) ∧
    (∀ fd, Framing.SameView Origins.view (WG.netlinkRecvmsg fd)) ∧
    (∀ ref, Framing.SameView Origins.view (WG.wgGetDevice ref)) :=
  ⟨Origins.Retaining.wgGetDeviceDone_material, Origins.Retaining.wgGetDeviceDump_material,
    Origins.Retaining.netlinkDump_material, Origins.Retaining.netlinkDumpStart_material,
    Origins.Retaining.netlinkRecvmsg_material, Origins.Retaining.wgGetDevice_material⟩

/-- Original initialization discharges receiving-material support for every
committed session/decrypt/probe history, for all typed traces and both flags.
Successful decrypts retain exact stored packet/key, AEAD and strictly earlier
session evidence. Saved probes retain support at their actual entry Worlds.
JSON or indexed Stop and the same full R2 audit projection remain exact; failures
retain checked history, not a returned World. Copied-trial origin transcripts,
configured peer identity and packet-to-Stack authorization are separate claims. -/
theorem initialized_committed_material_support :
    (∀ trace placeholders,
      Logged.ErasesOuter (Queues.RxHistory.executeTraceHistory trace placeholders)
        (Runner.executeTrace trace placeholders) ∧
      Logged.runPrefixOuter (Lifetimes.executeTraceAudit trace placeholders) [] =
        ((Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).1,
          Queues.RxHistory.auditHistory
            (Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2) ∧
      Origins.HistorySupport.HistorySafe
        (Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2) ∧
    (∀ trace placeholders pre post id (r : Logged.WGRunWitness (RxPacket × Option RxPacket)) out,
      (Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2 =
        pre ++ .rx (.decrypt id r) :: post → r.value.2 = some out →
      ∃ d k, r.before.dev = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
        d.keypairs[r.value.1.keypair]? = some k ∧
        Origins.Supported (Origins.HistorySupport.sessions pre) d.ifindex r.value.1.keypair k ∧
        ((WG.decryptPacket r.value.1).run r.before).run r.ambientBefore = .ok ((some out,r.after),r.ambientAfter) ∧
        out = {r.value.1 with nonce := u64le r.value.1.bytes 8, bytes := out.bytes} ∧
        aeadDecrypt k.receiving.key (counterNonce (u64le r.value.1.bytes 8))
          (r.value.1.bytes.drop 16) [] = some out.bytes) ∧
    (∀ trace placeholders pre post p,
      (Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2 =
        pre ++ .audit (.probe p) :: post →
      p.history = Queues.RxHistory.prior pre ∧ Origins.HistorySupport.StateSupported pre p.world) :=
  ⟨fun trace placeholders => ⟨Queues.RxHistory.executeTraceHistory_erases trace placeholders,
      Queues.RxHistory.executeTraceHistory_projects trace placeholders,
      Origins.HistorySupport.executeTraceHistory_support trace placeholders⟩,
    fun trace placeholders pre post id r out he ho =>
      Origins.HistorySupport.HistorySafe.decrypt _ pre post id r out
        (Origins.HistorySupport.executeTraceHistory_support trace placeholders) he ho,
    fun trace placeholders pre post p he =>
      Origins.HistorySupport.HistorySafe.probe _ pre post p
        (Origins.HistorySupport.executeTraceHistory_support trace placeholders) he⟩

/-- Supplied configured-table coherence is preserved by original creation,
retirement, make-dead and fresh owner acquisition. Lookup identifies its actual
resident configured key. Slot bounds do not bound process-global stamps;
dangling rows and dead residents are allowed. This is not initialized closure. -/
theorem original_configured_peer_identity :
    (∀ key psk, ⦃fun w=>⌜ConfiguredIdentity.Inv w⌝⦄ WG.peerCreate key psk
      ⦃⇓? result w=>⌜ConfiguredIdentity.Inv w ∧ ∀pid,result=.ok pid →
        ∃s p,ConfiguredIdentity.view w=some s ∧ s.peers pid=some p ∧ p.static=key⌝⦄) ∧
    (∀ key w v pid ambient ambient', ConfiguredIdentity.Inv w →
      ((WG.pubkeyLookup key).run w).run ambient=.ok ((some pid,v),ambient') →
      ConfiguredIdentity.view v=ConfiguredIdentity.view w ∧
      ∃d p,w.dev=some d ∧ d.peers[pid]?=some p ∧ (key,pid)∈d.peerHashtable ∧
        p.remoteStatic=key ∧ 0<p.refcount) ∧
    (∀ peer, ⦃fun w=>⌜ConfiguredIdentity.Inv w⌝⦄ WG.peerPut peer
      ⦃⇓? _ w=>⌜ConfiguredIdentity.Inv w⌝⦄) ∧
    (∀ pid w v ambient ambient', ConfiguredIdentity.Inv w →
      ((WG.peerMakeDead pid).run w).run ambient=.ok (((),v),ambient') → ConfiguredIdentity.Inv v) ∧
    (∀ owner w v result ambient ambient', ConfiguredIdentity.Inv w →
      ((Affiliation.acquireOwner owner).run w).run ambient=.ok ((result,v),ambient') → ConfiguredIdentity.Inv v) :=
  ⟨ConfiguredIdentity.peerCreate_spec,ConfiguredIdentity.pubkeyLookup_identity,
    ConfiguredIdentity.peerPut_preserves,ConfiguredIdentity.peerMakeDead_preserves,
    ConfiguredIdentity.acquireOwner_preserves⟩

/-- Configured material support retains one actual derivation-front Context,
material/owner witness and entry table row. The actual whole normal session tail
supplies live/self facts; a Some front alone may precede a Stop. The unchanged
observer has unconditional erasure and its original same-input AllocationInv
projection. Incoming configured support is supplied, not initialized here. -/
theorem original_configured_session_support :
    (∀ pid, Logged.ErasesStatePrefix (SessionOrigin.observed pid) (WG.beginSession pid) ∧
      Logged.StateProjectsUnder (fun h w _ => Lifetimes.AllocationInv h w) MaterialOrigin.life?
        (SessionOrigin.observed pid) (Lifetimes.beginSessionPrefix pid)) ∧
    (∀ pid w v result ambient ambient' history, ConfiguredIdentity.Inv w → ConfiguredSession.Inv history w →
      ((WG.beginSession pid).run w).run ambient=.ok ((result,v),ambient') →
      ∃front u middle,((SessionOrigin.front pid).run w).run ambient=.ok ((front,u),middle) ∧
        ConfiguredSession.Inv (history++[SessionOrigin.Receipt.material pid ⟨front,w,u,ambient,middle⟩]) v) ∧
    (∀ pid w v result ambient ambient' h t, MaterialOrigin.Valid SessionOrigin.Receipt.Valid h →
      ConfiguredIdentity.Inv w → ConfiguredSession.Inv (h.filterMap Origins.receipt?) w →
      Logged.runWGPrefix (SessionOrigin.observed pid) w ambient h=(.ok ((result,v),ambient'),t) →
      ConfiguredSession.Inv (t.filterMap Origins.receipt?) v) ∧
    (∀ history epoch slot key pid, ConfiguredSession.Supported history epoch slot key →
      key.peer=some pid → ConfiguredSession.ByPeer history epoch slot key pid) :=
  ⟨fun pid=>⟨SessionOrigin.observed_erases pid,SessionOrigin.observed_projects pid⟩,
    ConfiguredSession.beginSession_support,ConfiguredSession.observed_support,
    fun _ _ _ _ _ hs hw=>hs.byPeer hw⟩

/-- Original prepare's fresh decrypt receipt is linked to the actual captured
ring item and write. A successful decrypt then identifies its historical
configured session caller, exact AEAD transformation and state-only stored
publication before IRQ. Some prepare may instead publish DEAD. The endpoint
claim is normal-only; lower receiptObserved separately retains later Stop
prefixes. Supplied support/compatibility are explicit, and current peer-slot
identity, initialized publication and later Stack/routing joins are supplied
by the separate initialized authorization contracts below. -/
theorem original_rx_publication_identity :
    Logged.ErasesStatePrefix RxOrigin.prepare Queues.RxWorkers.prepareSource ∧
    Logged.StateProjectsUnder (fun h w _ => Lifetimes.AllocationInv h w) MaterialOrigin.life?
      RxOrigin.prepare Queues.RxWorkers.preparePrefix ∧
    (∀ history w v ambient ambient' h t pid, ConfiguredSession.Inv history w → Queues.RxCredits.RxCompatible w →
      Logged.runWGPrefix RxOrigin.prepare w ambient h=(.ok ((some pid,v),ambient'),t) →
      ∃d id ring, ∃(r : Logged.WGRunWitness (RxPacket × Option RxPacket)), ∃pre suffix,
        w.dev=some d ∧ d.decryptQueue.consume=(some id,ring) ∧
        r.before=Packets.update w (fun d=>{d with decryptQueue:=ring}) ∧
        r.ambientBefore=CounterWindow.record ambient .decWorkerConsumed true ∧
        r.Valid (RxOrigin.readDecrypt id) ∧
        Logged.runWGPrefix (Logged.focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life?
          (RxOrigin.readDecryptPrefix id)) r.before r.ambientBefore h=
          (.ok ((r.value,r.after),r.ambientAfter),h++pre) ∧
        t=h++pre++[MaterialOrigin.Event.receipt (RxOrigin.Receipt.decrypt id r)]++suffix ∧
        ∀out,r.value.2=some out → PublicationIdentity.Identity history id r out pid v) :=
  ⟨RxOrigin.prepare_erases,RxOrigin.prepare_projects,PublicationIdentity.prepare_identity⟩

/-- The actual empty fixture establishes configured-table and same-receipt
current identity for every flag combination. Only the original seven WG store
fields are fixed; initialized transport through later calls is separate. -/
theorem configured_identity_initial (net bare : Bool) (w : WGWorld)
    (hw : Framing.wgStoreView w = Framing.wgStoreView (Runner.initialWG net bare)) :
    ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv [] w :=
  ⟨ConfiguredMaintenance.configured_initial net bare w hw, CurrentIdentity.initial net bare w hw⟩

/-- Nullable affiliation supplies exactly the compatibility used by RX
publication and current-key handoff; missing keys and NULL words remain allowed. -/
theorem nullable_affiliation_key_compatibility (w : WGWorld) (hi : Affiliation.Inv w) :
    Queues.RxCredits.KeysCompatible w :=
  Queues.RxCredits.keysCompatible_of_affiliation hi

/-- At the actual successful publication before IRQ, one session witness
supports key material and the resident peer's allocation stamp/static key.
This retains the weaker RX compatibility premise; full initialized transport
and the later routing/Stack join are not implied by this local certificate. -/
theorem successful_publication_current_identity (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : Logged.WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId)
    (v : WGWorld) (ambient : Ambient)
    (support : CurrentIdentity.Inv history r.before) (compat : Queues.RxCredits.RxCompatible r.before)
    (published : PublicationIdentity.Published id r out pid v ambient) :
    PublicationIdentity.CurrentCertificate history id r out pid v :=
  PublicationIdentity.published_current history id r out pid v ambient support compat published


/-- The actual fixture establishes nullable affiliation on the original seven
WG store fields. Clearing key slots preserves it; handshake clearing and expiry
retain its exact view. Missing keys and cleared owner words remain admissible. -/
theorem nullable_affiliation_initial_and_maintenance :
    (∀ net bare w, Framing.wgStoreView w = Framing.wgStoreView (Runner.initialWG net bare) →
      Affiliation.Inv w) ∧
    (∀ pid, Framing.Preserves Affiliation.Inv (WG.keypairsClear pid)) ∧
    (∀ pid, Framing.SameView Affiliation.view (WG.handshakeClear pid)) ∧
    (∀ pid, Framing.SameView Affiliation.view (WG.expireCurrentPeerKeypairs pid)) :=
  ⟨Affiliation.initial, Affiliation.keypairsClear_affiliation,
    Affiliation.handshakeClear_view, Affiliation.expireCurrentPeerKeypairs_view⟩

/-- Both original session execution and its unchanged observer carry one
configured receipt for receiving material and current peer identity. A normal
whole-session tail supplies the configured facts; incoming support is explicit.
No affiliation or global validity premise for unrelated receipts is required. -/
theorem original_current_session_support :
    (∀ pid w v result ambient ambient' history,
      ConfiguredIdentity.Inv w → CurrentIdentity.Inv history w →
      ((WG.beginSession pid).run w).run ambient = .ok ((result,v),ambient') →
      ∃ front u middle, ((SessionOrigin.front pid).run w).run ambient = .ok ((front,u),middle) ∧
        CurrentIdentity.Inv (history ++ [SessionOrigin.Receipt.material pid
          ⟨front,w,u,ambient,middle⟩]) v) ∧
    (∀ pid w v result ambient ambient' h t,
      ConfiguredIdentity.Inv w → CurrentIdentity.Inv (h.filterMap Origins.receipt?) w →
      Logged.runWGPrefix (SessionOrigin.observed pid) w ambient h = (.ok ((result,v),ambient'),t) →
      CurrentIdentity.Inv (t.filterMap Origins.receipt?) v) :=
  ⟨CurrentSession.beginSession_support, CurrentSession.observed_support⟩

/-- Native peer retirement retains receiving material and both identity fields
of surviving named residents. The relation permits deletion, invalidation and
cleared owners; neither an initialized invariant nor positivity is a premise. -/
theorem original_current_peer_retirement :
    (∀ peer, Lifetimes.ProjectedAction id CurrentIdentity.Retains (WG.peerPut peer)) ∧
    (∀ pid, Lifetimes.ProjectedAction id CurrentIdentity.Retains (WG.peerMakeDead pid)) :=
  ⟨CurrentIdentity.peerPut_retains, CurrentIdentity.peerMakeDead_retains⟩

/-- Whole normal receive preparation exposes the fresh actual decrypt receipt
at its journal position. Successful decryption certifies the same configured
session and the resident peer's current identity at publication before IRQ.
DEAD publication and later Stack/routing are not authorized by this statement. -/
theorem original_rx_publication_current_identity
    (history : List SessionOrigin.Receipt) (w v : WGWorld) (ambient ambient' : Ambient)
    (h t : List (MaterialOrigin.Event RxOrigin.Receipt)) (pid : PeerId)
    (support : CurrentIdentity.Inv history w) (compat : Queues.RxCredits.RxCompatible w)
    (hr : Logged.runWGPrefix RxOrigin.prepare w ambient h = (.ok ((some pid,v),ambient'),t)) :
    ∃ d id ring, ∃ (r : Logged.WGRunWitness (RxPacket × Option RxPacket)), ∃ pre suffix,
      w.dev = some d ∧ d.decryptQueue.consume = (some id,ring) ∧
      r.before = Packets.update w (fun d => {d with decryptQueue := ring}) ∧
      r.ambientBefore = CounterWindow.record ambient .decWorkerConsumed true ∧
      r.Valid (RxOrigin.readDecrypt id) ∧
      Logged.runWGPrefix (Logged.focusStatePrefix MaterialOrigin.Event.life MaterialOrigin.life?
        (RxOrigin.readDecryptPrefix id)) r.before r.ambientBefore h =
          (.ok ((r.value,r.after),r.ambientAfter),h ++ pre) ∧
      t = h ++ pre ++ [MaterialOrigin.Event.receipt (RxOrigin.Receipt.decrypt id r)] ++ suffix ∧
      ∀ out, r.value.2 = some out → PublicationIdentity.CurrentCertificate history id r out pid v :=
  PublicationIdentity.prepare_current_identity history w v ambient ambient' h t pid support compat hr


/-- The actual nullable owner acquisition and complete index scan retain
receiving material and full current peer identity, including normal None.
Configured table coherence is separately preserved by the same original scan. -/
theorem original_current_index_transport :
    (∀ owner, Lifetimes.ProjectedAction id CurrentIdentity.Retains (Affiliation.acquireOwner owner)) ∧
    (∀ kinds index, Lifetimes.ProjectedAction id CurrentIdentity.Retains (WG.indexLookup kinds index)) ∧
    (∀ kinds index, Framing.Preserves ConfiguredIdentity.Inv (WG.indexLookup kinds index)) :=
  ⟨CurrentIdentity.acquireOwner_current,CurrentIdentity.indexLookup_current,
    ConfiguredIdentity.indexLookup_preserves⟩

/-- Creation needs only bounds on named owners of valid receiving keys;
nullable affiliation supplies those bounds. The actual allocation/refusal
result and all initializer writes remain in the original native run. -/
theorem original_current_creation_transport :
    (∀ w, Affiliation.Inv w → CurrentIdentity.ReceivingOwnersBelow w) ∧
    (∀ key psk w v ambient ambient' result, CurrentIdentity.ReceivingOwnersBelow w →
      ((WG.peerCreate key psk).run w).run ambient = .ok ((result,v),ambient') →
      CurrentIdentity.Retains w v) ∧
    (∀ key psk history, Framing.Hoare (WG.peerCreate key psk)
      (fun w => CurrentIdentity.Inv history w ∧ CurrentIdentity.ReceivingOwnersBelow w)
      (fun _ w => CurrentIdentity.Inv history w)) :=
  ⟨fun _ => CurrentIdentity.receivingOwnersBelow_of_affiliation,
    CurrentIdentity.peerCreate_retains,CurrentIdentity.peerCreate_current⟩

/-- Concrete handshake construction, transmission and the worker's final peer
payment retain configured/current support. Deletion remains permitted, and
normal-only preservation adds no positivity or totality premise. -/
theorem original_configured_handshake_send :
    (∀ pid history, Framing.Preserves
      (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w)
      (WG.createInitiation pid)) ∧
    (∀ pid history, Framing.Preserves
      (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w)
      (WG.sendHandshakeInitiation pid)) ∧
    (∀ pid history, Framing.Preserves
      (fun w => ConfiguredIdentity.Inv w ∧ CurrentIdentity.Inv history w)
      (WG.handshakeSendWorker pid)) :=
  ⟨ConfiguredHandshake.createInitiation_preserves,ConfiguredHandshake.sendHandshakeInitiation_preserves,
    ConfiguredHandshake.handshakeSendWorker_preserves⟩

/-- Each new actual Stack entry has a strictly earlier successful consume
receipt in this poll's exact observed suffix, with routing at that consume's
real entry state and longest-prefix authorization of the delivered bytes.
The flat tables are supplied at poll entry; initialized historical key identity
is a separate obligation. A later Stop retains the reached certificates. -/
theorem original_poll_routing_entries (xs : FlatTable × FlatTable) (pid : PeerId) (budget : Nat)
    (w : World) (h : List Queues.RxHistory.Event)
    (hi : RoutedView (routingView w.wg) xs) :
    ∃ suffix : List Queues.RxJoint.Event,
      (Logged.runPrefix (Queues.RxHistory.observePoll pid budget) w h).2 =
        h ++ suffix.map Queues.RxHistory.promote ∧
      ∀ e, Queues.RxJoint.Event.entered e ∈ suffix →
        ∃ (r : Queues.RxDisposition.ConsumeReceipt), ∃ before between after,
          suffix = before ++ [.consumed e.tag.occurrence e.tag.skb e.stamp r] ++
            between ++ [.entered e] ++ after ∧
          e.origin = some r ∧ r.run.value = some e.tag.bytes ∧
          Queues.RxLink.Source e.tag.skb e.stamp r ∧
          RoutedView (routingView r.run.before) xs ∧
          ∃ v4 : Bool,
            ipTunnelParseProtocol e.tag.bytes = (if v4 then 4 else 6) ∧
            ipTunnelParseProtocol r.packet.bytes = (if v4 then 4 else 6) ∧
            PeerWinner (rootWidth v4) (sourceAddress v4 e.tag.bytes)
              (selectedFlat v4 xs) (some r.peer) ∧
            sourceAddress v4 e.tag.bytes = sourceAddress v4 r.packet.bytes :=
  Queues.PollAuthorization.observePoll_entries xs pid budget w h hi

/-- Normal native Noise construction and consumption preserve configured/current
identity. Authentication refusal may delete a peer; a Stop has no endpoint. -/
theorem original_current_receive_transport :
    (∀ pid history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.createResponse pid)) ∧
    (∀ msg history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.consumeInitiation msg)) ∧
    (∀ msg history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.consumeResponse msg)) :=
  ⟨ConfiguredReceive.createResponse_preserves,ConfiguredReceive.consumeInitiation_preserves,
    ConfiguredReceive.consumeResponse_preserves⟩

/-- Real flushed work, timer stop and peer removal retain the same configured
identity support on normal returns. All queue budgets and release guards remain
those of the original calls; no positivity or completion premise is added. -/
theorem original_current_peer_lifecycle :
    (∀ pid history, Framing.Preserves (CurrentLifecycle.Inv history)
      (WG.queuedExpiredZeroKeyMaterial pid)) ∧
    (∀ pid history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.runFlushedSendWork pid)) ∧
    (∀ pid history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.runFlushedClearWork pid)) ∧
    (∀ upTo history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.drainHandshakeSendWq upTo)) ∧
    (∀ pid history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.timersStop pid)) ∧
    (∀ pid history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.peerRemoveAfterDead pid)) ∧
    (∀ peer history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.peerRemove peer)) :=
  ⟨CurrentLifecycle.queuedExpiredZeroKeyMaterial_preserves,
    CurrentLifecycle.runFlushedSendWork_preserves,CurrentLifecycle.runFlushedClearWork_preserves,
    CurrentLifecycle.drainHandshakeSendWq_preserves,CurrentLifecycle.timersStop_preserves,
    CurrentLifecycle.peerRemoveAfterDead_preserves,CurrentLifecycle.peerRemove_preserves⟩

/-- Creation, stopping and destruction preserve supplied identity support.
Native deletion callbacks remain arbitrary under their explicit preservation
contracts; empty newly registered devices need no historical session receipt. -/
theorem original_current_device_lifecycle :
    (∀ history, Framing.Preserves (CurrentLifecycle.Inv history) WG.peerRemoveAll) ∧
    (∀ history, Framing.Preserves (CurrentLifecycle.Inv history) WG.wgStop) ∧
    (∀ history, Framing.Preserves (CurrentLifecycle.Inv history) WG.wgDown) ∧
    (∀ history, Framing.Preserves (CurrentLifecycle.Inv history) WG.wgDestruct) ∧
    (∀ history (onDown onUnregister : WG.M Unit),
      Framing.Preserves (CurrentLifecycle.Inv history) onDown →
      Framing.Preserves (CurrentLifecycle.Inv history) onUnregister →
      Framing.Preserves (CurrentLifecycle.Inv history) (WG.wgDelete onDown onUnregister)) ∧
    (∀ history, Framing.Preserves (CurrentLifecycle.Inv history) WG.wgCreate) :=
  ⟨CurrentLifecycle.peerRemoveAll_preserves,CurrentLifecycle.wgStop_preserves,
    CurrentLifecycle.wgDown_preserves,CurrentLifecycle.wgDestruct_preserves,
    CurrentLifecycle.wgDelete_preserves,CurrentLifecycle.wgCreate_preserves⟩

/-- The existing session observer preserves reached material/history safety
and stronger configured/current identity for the identical actual execution.
Incoming support is supplied; initialized whole-run support is separate. -/
theorem original_current_session_journal (pid : PeerId) :
    Logged.PrefixPreserves
      (fun h w => Origins.HistorySupport.SupportInv h w ∧ CurrentSessionPrefix.StateInv h w)
      Origins.HistorySupport.HistorySafe (Origins.HistoryAdapters.session pid) :=
  CurrentSessionPrefix.session_supported pid

/-- Each joint adapter executes the actual lifetime observer once and projects
exactly to the original routing completion stream. Every normal errno emits a
completion; a Stop retains the earlier access prefix without a completion. -/
theorem original_joint_routing_observers :
    (∀ pid attrs, Logged.ErasesStatePrefix (Queues.RoutingJoint.completedAllowedip pid attrs)
      (WG.setAllowedip pid attrs)) ∧
    (∀ pid, Logged.ErasesStatePrefix (Queues.RoutingJoint.completedRemovePeer pid) (WG.removeByPeer pid)) ∧
    Logged.ErasesStatePrefix Queues.RoutingJoint.completedFree WG.free ∧
    (∀ pid attrs, Logged.StateProjectsPrefix Queues.RoutingJoint.routingEvent id
      (Queues.RoutingJoint.completedAllowedip pid attrs) (AllowedIps.completedAllowedip pid attrs)) ∧
    (∀ pid, Logged.StateProjectsPrefix Queues.RoutingJoint.routingEvent id
      (Queues.RoutingJoint.completedRemovePeer pid) (AllowedIps.completedRemovePeer pid)) ∧
    Logged.StateProjectsPrefix Queues.RoutingJoint.routingEvent id Queues.RoutingJoint.completedFree
      AllowedIps.completedFree :=
  ⟨Queues.RoutingJoint.completedAllowedip_erases,Queues.RoutingJoint.completedRemovePeer_erases,
    Queues.RoutingJoint.completedFree_erases,Queues.RoutingJoint.completedAllowedip_routing,
    Queues.RoutingJoint.completedRemovePeer_routing,Queues.RoutingJoint.completedFree_routing⟩


/-- Native traffic and receive paths preserve supplied configured/current
identity on normal return. Packet admission retains the actual nullable lookup and release arms. -/
theorem original_current_traffic_and_receive :
    (∀ pid retry history, Framing.Preserves (CurrentLifecycle.Inv history)
      (WG.sendQueuedHandshakeInitiation pid retry)) ∧
    (∀ pid kid history, Framing.Preserves (CurrentLifecycle.Inv history)
      (WG.receivedWithKeypair pid kid)) ∧
    (∀ pid history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.keepKeyFreshRx pid)) ∧
    (∀ pid history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.sendStagedPackets pid)) ∧
    (∀ pid history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.sendKeepalive pid)) ∧
    (∀ msg history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.cookieMessageConsume msg)) ∧
    (∀ id history, Framing.Preserves (CurrentLifecycle.Inv history) (RxOrigin.readDecrypt id)) ∧
    (∀ pid pkt endpoint history, Framing.Preserves (CurrentLifecycle.Inv history)
      (WG.consumeDataDone pid pkt endpoint)) ∧
    (∀ msg src ds history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.consumeData msg src ds)) ∧
    (∀ msg src history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.packetReceive msg src)) ∧
    (∀ msg src history, Framing.Preserves (CurrentLifecycle.Inv history) (WG.wgReceive msg src)) :=
  ⟨CurrentTraffic.sendQueuedHandshakeInitiation_preserves,CurrentTraffic.receivedWithKeypair_preserves,
    CurrentTraffic.keepKeyFreshRx_preserves,CurrentTraffic.sendStagedPackets_preserves,
    CurrentTraffic.sendKeepalive_preserves,CurrentTraffic.cookieMessageConsume_preserves,
    CurrentRx.readDecrypt_preserves,CurrentRx.consumeDataDone_preserves,
    CurrentRx.consumeData_preserves,CurrentRx.packetReceive_preserves,CurrentRx.wgReceive_preserves⟩

/-- Existing focused receive observers retain current support at the actual
session cut. No premise certifies an unrelated incoming journal. -/
theorem original_current_receive_journal :
    (∀ pid, CurrentHistory.Preserves
      (Origins.HistoryAdapters.focus (Origins.HistoryAdapters.localResponse pid))) ∧
    (∀ msg src loaded mac, CurrentHistory.Preserves
      (Origins.HistoryAdapters.focus (Origins.HistoryAdapters.localAfterMac msg src loaded mac))) ∧
    (∀ msg src, CurrentHistory.Preserves
      (Origins.HistoryAdapters.focus (Origins.HistoryAdapters.localReception msg src))) ∧
    CurrentHistory.Preserves Origins.HistoryAdapters.receiveStep :=
  ⟨CurrentReceiveHistory.response,CurrentReceiveHistory.afterMac,
    CurrentReceiveHistory.reception,CurrentReceiveHistory.receiveStep⟩

/-- Concrete session, decrypt and saved-probe observers preserve positional
current checks together with the existing material/history safety. Stop prefixes
retain every check already emitted; initialization remains a separate claim. -/
theorem original_current_sensitive_journal :
    (∀ pid, CurrentChecks.Preserves (Origins.HistoryAdapters.session pid)) ∧
    (∀ id, CurrentChecks.Preserves (Origins.HistoryAdapters.decrypt id)) ∧
    CurrentChecks.Preserves (Queues.RxHistory.audit Lifetimes.consistentFilterAudit) :=
  ⟨CurrentChecks.session,fun id => CurrentChecks.decrypt id (CurrentRx.readDecrypt_preserves id),
    CurrentChecks.filter_probe⟩

/-- A specified occurrence uses its strict earlier session prefix. Probe history
is the actual earlier lifetime projection, including when later work stops. -/
theorem positional_current_checks (h : List Queues.RxHistory.Event) (safe : CurrentChecks.Safe h) :
    (∀ pre post id r, h = pre ++ .rx (.decrypt id r) :: post →
      CurrentLifecycle.Inv (Origins.HistorySupport.sessions pre) r.before) ∧
    (∀ pre post p, h = pre ++ .audit (.probe p) :: post →
      p.history = Queues.RxHistory.prior pre ∧ CurrentSessionPrefix.StateInv pre p.world) :=
  ⟨fun _ _ _ _ position => CurrentChecks.Safe.decrypt safe position,
    fun _ _ _ position => CurrentChecks.Safe.probe safe position⟩

/-- One actual consume execution emits its exact normal receipt with the same
anchored publication identity; later cleanup need not retain packet/key residency.
Transport across earlier interleavings is the explicit Live premise. -/
theorem original_publication_consume (history : List SessionOrigin.Receipt) (id occurrence : Nat)
    (r : Logged.WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId)
    (published : WGWorld) (ep : Endpoint) (w v : World) (h t : List Queues.RxJoint.Event)
    (value : Option Queues.RxJoint.Entry)
    (live : PublicationIdentity.Live history id r out pid published w.wg)
    (hr : Logged.runPrefix (Queues.RxJoint.consume pid occurrence id (Lifetimes.packetStamp published id)
      {out with state := .crypted} ep) w h = (.ok (value,v),t)) :
    ∃ receipt pre suffix,
      receipt.run.before = w.wg ∧ receipt.run.ambientBefore = w.ambient ∧
      receipt.run.after = v.wg ∧ receipt.run.ambientAfter = v.ambient ∧
      PublicationIdentity.ConsumeCertificate history id r out pid published
        (Lifetimes.packetStamp published id) receipt ∧
      t = h ++ pre ++ [.consumed occurrence id (Lifetimes.packetStamp published id) receipt] ++ suffix ∧
      ∀ e, value = some e → e.origin = some receipt ∧ receipt.run.value = some e.tag.bytes :=
  PublicationIdentity.consume_current history id occurrence r out pid published ep w v h t value live hr

/-- The joint allowed-IP loop has exactly the original completion projection,
with the same actual history passed to its supplied continuation. -/
theorem original_joint_allowed_ips_routing (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → Logged.WGPrefix Queues.RoutingJoint.Event Int)
    (routingNext : Int → Logged.WGPrefix RoutingCompletion Int)
    (hn : ∀ ret, Logged.StateProjectsPrefix Queues.RoutingJoint.routingEvent id
      (next ret) (routingNext ret)) :
    Logged.StateProjectsPrefix Queues.RoutingJoint.routingEvent id
      (Queues.RoutingJoint.peerAllowedIps attrs peer pid next)
      (Configuration.peerAllowedIpsObservedWG attrs peer pid routingNext) :=
  Queues.RoutingJoint.peerAllowedIps_routing attrs peer pid next routingNext hn

/-- The second projection recovers the unchanged product RX observer. Concrete
configuration leaves establish append behavior; only the supplied lower
continuation carries an explicit append obligation. -/
theorem original_joint_allowed_ips_rx (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (next : Int → Logged.WGPrefix Queues.RoutingJoint.Event Int)
    (rxNext : Int → Lifetimes.MixedM Int)
    (ha : ∀ ret, Logged.StateAppends (rxNext ret))
    (hn : ∀ ret, Logged.StateProjectsPrefix Queues.RoutingJoint.rxEvent id
      (next ret) (Queues.RoutingJoint.nativeRx (rxNext ret))) :
    Logged.ProjectsPrefix Queues.RoutingJoint.rxEvent id
      (Logged.liftWGObserver (Queues.RoutingJoint.peerAllowedIps attrs peer pid next))
      (Queues.RxHistory.mixed
        (Logged.liftWGObserver (Lifetimes.peerAllowedIpsPrefix attrs peer pid rxNext))) :=
  Queues.RoutingJoint.peerAllowedIps_rx_product attrs peer pid next rxNext ha hn

/-- GRO callbacks remain arbitrary product actions with explicit preservation
contracts. This proves the real poll's normal-state identity transport, including
all budget and queue guards; it does not assert totality or initialization. -/
theorem original_current_poll_callbacks (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs history, Framing.Preserves
      (fun w : World => CurrentLifecycle.Inv history w.wg) (callback xs))
    (history : List SessionOrigin.Receipt) :
    Framing.Preserves (fun w : World => CurrentLifecycle.Inv history w.wg)
      (WG.rxPoll pid budget callback) :=
  CurrentPoll.poll pid budget callback hc history

/-- The same receive response, admission and worker iteration preserve exact
positional current checks together with material support, on normal returns and
on every emitted Stop prefix. -/
theorem original_current_receive_checks :
    (∀ pid, CurrentChecks.Preserves
      (Origins.HistoryAdapters.focus (Origins.HistoryAdapters.localResponse pid))) ∧
    (∀ msg src loaded mac, CurrentChecks.Preserves
      (Origins.HistoryAdapters.focus (Origins.HistoryAdapters.localAfterMac msg src loaded mac))) ∧
    (∀ msg src, CurrentChecks.Preserves
      (Origins.HistoryAdapters.focus (Origins.HistoryAdapters.localReception msg src))) ∧
    CurrentChecks.Preserves Origins.HistoryAdapters.receiveStep ∧
    CurrentChecks.Preserves Origins.HistoryAdapters.receiveIteration :=
  ⟨CurrentReceiveChecks.response,CurrentReceiveChecks.afterMac,CurrentReceiveChecks.reception,
    CurrentReceiveChecks.receiveStep,CurrentReceiveChecks.receiveIteration⟩

/-- The actual transmit entry and fixture stack retain supplied configured/current
identity on normal returns, including IPv4 replies sent back through WireGuard. -/
theorem original_current_stack :
    (∀ family addr packets mtu history, Framing.Preserves (CurrentLifecycle.Inv history)
      (WG.wgXmit family addr packets mtu)) ∧
    (∀ (packets : List (List UInt8)) history, Framing.Preserves
      (fun w : World => CurrentLifecycle.Inv history w.wg) (packets.forM Env.deliverInner)) :=
  ⟨CurrentStack.wgXmit_preserves, CurrentStack.stackForM_preserves⟩

/-- The concrete poll uses the actual stack callback and retains prior positional
checks even when a later action stops. Initial support is still supplied. -/
theorem original_current_poll :
    (∀ pid budget history, Framing.Preserves
      (fun w : World => CurrentLifecycle.Inv history w.wg)
      (WG.rxPoll pid budget (fun packets => packets.forM Env.deliverInner))) ∧
    (∀ pid budget, CurrentChecks.Preserves (Queues.RxHistory.observePoll pid budget)) :=
  ⟨CurrentPoll.actual, CurrentPoll.checked⟩

/-- The real fixture starts with receiving-owner and RX key-slot bounds. These
bounds exclude dangling RX references to a slot that allocation could reuse. -/
theorem initial_receiving_owner_carrier (net bare : Bool) (w : WGWorld)
    (hw : Framing.wgStoreView w = Framing.wgStoreView (Runner.initialWG net bare)) : OwnerBounds.Carrier w :=
  OwnerBounds.initial net bare w hw

/-- Concrete peer allocation preserves current identity and its receiving-owner
carrier. Key allocation preserves that carrier for every nullable owner word;
a newly allocated key has no valid receiving material yet. -/
theorem original_owner_creation :
    (∀ key psk history, Framing.Preserves
      (fun w => CurrentLifecycle.Inv history w ∧ OwnerBounds.Carrier w)
      (WG.peerCreate key psk)) ∧
    (∀ word, Framing.Preserves OwnerBounds.Carrier (WG.keypairCreate word)) :=
  ⟨OwnerCreation.peerCreate_current, OwnerBounds.keypairCreate_preserves⟩

/-- The same actual session front certifies installed receiving material and
preserves the owner/RX carrier. The statement asserts only normal executions
and retains the exact native WG and ambient endpoints of that front. -/
theorem original_owner_session (pid : PeerId) (w v : WGWorld) (result : Bool)
    (a b : Ambient) (history : List SessionOrigin.Receipt)
    (hi : CurrentLifecycle.Inv history w ∧ OwnerBounds.Carrier w)
    (hr : ((WG.beginSession pid).run w).run a = .ok ((result, v), b)) :
    ∃ front u middle, ((SessionOrigin.front pid).run w).run a = .ok ((front, u), middle) ∧
      CurrentLifecycle.Inv
        (history ++ [SessionOrigin.Receipt.material pid ⟨front, w, u, a, middle⟩]) v ∧
      OwnerBounds.Carrier v :=
  OwnerCreation.beginSession_current pid w v result a b history hi hr

/-- One execution of the complete configuration tail retains the exact old
routing completion stream and the exact old product RX lifetime stream,
including their arbitrary incoming histories and stopped prefixes. -/
theorem original_joint_configuration_tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Logged.StateProjectsPrefix Queues.RoutingJoint.routingEvent id
      (Queues.RoutingJoint.peerConfigTail attrs peer pid)
      (Configuration.peerConfigTailObserved attrs peer pid) ∧
    Logged.ProjectsPrefix Queues.RoutingJoint.rxEvent id
      (Logged.liftWGObserver (Queues.RoutingJoint.peerConfigTail attrs peer pid))
      (Queues.RxHistory.mixed (Logged.liftWGObserver
        (Lifetimes.peerConfigTailPrefix attrs peer pid))) :=
  ⟨Queues.RoutingJoint.peerConfigTail_routing attrs peer pid,
    Queues.RoutingJoint.peerConfigTail_rx_product attrs peer pid⟩


/-- The existing session and peer-allocation observers carry receiving-owner
bounds on the same execution as their current/history and lifetime guarantees.
Stops retain the original safe journal without asserting a final state. -/
theorem original_owner_journals :
    (∀ pid, Logged.PrefixPreserves
      (fun h w => CurrentChecks.Inv h w ∧ OwnerBounds.Carrier w.wg)
      CurrentChecks.Safe (Origins.HistoryAdapters.session pid)) ∧
    (∀ key psk history, Logged.PrefixPreserves
      (fun h w => Lifetimes.AllocationInv h w.wg ∧ CurrentLifecycle.Inv history w.wg ∧
        OwnerBounds.Carrier w.wg)
      Lifetimes.LifetimeEvent.Safe
      (Logged.liftWGObserver (Lifetimes.peerCreateMixed key psk))) :=
  ⟨OwnerHistory.session, OwnerHistory.peerCreateProduct⟩

/-- A source-linked normal consume supplies its own entry peer residency.
Earlier transport may permit absence, but must retain the anchored packet and
both peer identity fields whenever the peer is resident. -/
theorem original_retained_publication_receipt (history : List SessionOrigin.Receipt)
    (id : SkbId) (r : Logged.WGRunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (pid : PeerId) (published : WGWorld)
    (stamp : Lifetimes.PacketStamp) (receipt : Queues.RxDisposition.ConsumeReceipt)
    (retained : PublicationIdentity.Retained history id r out pid published receipt.run.before)
    (source : Queues.RxLink.Source id stamp receipt) :
    PublicationIdentity.ConsumeCertificate history id r out pid published stamp receipt :=
  PublicationIdentity.retained_receipt retained source


/-- The real nullable owner acquisition and index lookup preserve the receiving
owner carrier on every normal return, including ordinary lookup refusal. -/
theorem original_receiving_owner_lookup :
    (∀ owner, Framing.Preserves OwnerBounds.Carrier (Affiliation.acquireOwner owner)) ∧
    (∀ kinds index, Framing.Preserves OwnerBounds.Carrier (WG.indexLookup kinds index)) :=
  ⟨OwnerIndex.acquireOwner_preserves, OwnerIndex.indexLookup_preserves⟩

/-- Existing prepare, NAPI and crypt worker observers preserve current checks
at their actual journal positions. Every stopped prefix retains the checks
already emitted; no initialization, successful authentication or totality is assumed. -/
theorem original_current_workers :
    CurrentChecks.Preserves Origins.HistoryAdapters.prepare ∧
    CurrentChecks.Preserves Queues.RxHistory.napiSoftirq ∧
    CurrentChecks.Preserves Queues.RxHistory.pollScheduledInline ∧
    CurrentChecks.Preserves Queues.RxHistory.napiIrqExit ∧
    CurrentChecks.Preserves Queues.RxHistory.decryptStep ∧
    CurrentChecks.Preserves Queues.RxHistory.decryptIteration ∧
    CurrentChecks.Preserves Queues.RxHistory.encryptIteration :=
  ⟨CurrentWorkers.prepare, CurrentWorkers.napiSoftirq, CurrentWorkers.pollScheduledInline,
    CurrentWorkers.napiIrqExit, CurrentWorkers.decryptStep, CurrentWorkers.decryptIteration,
    CurrentWorkers.encryptIteration⟩

/-- The joint peer-removal observer retains both original streams through
actual timer stopping, flushed work and cleanup, including all stopped prefixes. -/
theorem original_joint_configuration_removal (peer : Option PeerId) :
    Logged.StateProjectsPrefix Queues.RoutingJoint.routingEvent id
      (Queues.RoutingJoint.removePeer peer) (Configuration.peerRemoveObserved peer) ∧
    Logged.ProjectsPrefix Queues.RoutingJoint.rxEvent id
      (Logged.liftWGObserver (Queues.RoutingJoint.removePeer peer))
      (Queues.RxHistory.mixed (Logged.liftWGObserver (Lifetimes.peerRemovePrefix peer))) :=
  ⟨Queues.RoutingJoint.removePeer_routing peer, Queues.RoutingJoint.removePeer_rx_product peer⟩

/-- Complete configuration updates execute the actual removal and tail observers.
Their old routing and product RX projections require no supplied callback or
append law, and keep the arbitrary incoming journals and exact failed prefixes. -/
theorem original_joint_configuration_update (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Logged.StateProjectsPrefix Queues.RoutingJoint.routingEvent id
      (Queues.RoutingJoint.peerConfigUpdate Queues.RoutingJoint.removePeer attrs peer flags psk pid)
      (Configuration.peerConfigUpdateObserved attrs peer flags psk pid) ∧
    Logged.ProjectsPrefix Queues.RoutingJoint.rxEvent id
      (Logged.liftWGObserver
        (Queues.RoutingJoint.peerConfigUpdate Queues.RoutingJoint.removePeer attrs peer flags psk pid))
      (Queues.RxHistory.mixed
        (Logged.liftWGObserver (Lifetimes.peerConfigUpdatePrefix attrs peer flags psk pid))) :=
  ⟨Queues.RoutingJoint.peerConfigUpdate_concrete_routing attrs peer flags psk pid,
    Queues.RoutingJoint.peerConfigUpdate_concrete_product attrs peer flags psk pid⟩

/-- The actual scheduler preserves positional current checks through its
crypt-ahead, activation, dispatch and saved-trial probe calls. -/
theorem original_current_schedule :
    (∀ pid, CurrentChecks.Preserves (Queues.RxHistory.cryptAhead pid)) ∧
    (∀ a, CurrentChecks.Preserves (Queues.RxHistory.activationIteration a)) ∧
    (∀ a, CurrentChecks.Preserves (Queues.RxHistory.activationRun a)) ∧
    (∀ worker, CurrentChecks.Preserves (Queues.RxHistory.dispatch worker)) ∧
    (∀ stack, CurrentChecks.Preserves (Queues.RxHistory.schedule stack)) ∧
    (∀ self, CurrentChecks.Preserves (Queues.RxHistory.nestedResched self)) :=
  ⟨CurrentEnvironment.cryptAhead,CurrentEnvironment.activationIteration,
    CurrentEnvironment.activationRun,CurrentEnvironment.dispatch,
    CurrentEnvironment.schedule,CurrentEnvironment.nestedResched⟩

/-- All actual deferred-call cases, including both timer modes and their
exact end guards, preserve supplied current checks and every stopped prefix. -/
theorem original_current_deferred :
    (∀ call, CurrentChecks.Preserves (Queues.RxHistory.deferred call)) ∧
    (∀ pid timer history, Framing.Preserves (CurrentLifecycle.Inv history)
      (WG.timerCallback pid timer)) :=
  ⟨CurrentDeferred.deferred,CurrentDeferred.timerCallback_preserves⟩

/-- One complete peer command carries both unchanged original observation
streams, without assuming a well-formed attribute set or successful return. -/
theorem original_joint_peer_command (attrs : PeerAttrs) :
    Logged.StateProjectsPrefix Queues.RoutingJoint.routingEvent id
      (Queues.RoutingJoint.setPeerCommand attrs) (Configuration.setPeerCmdObserved attrs) ∧
    Logged.ProjectsPrefix Queues.RoutingJoint.rxEvent id
      (Logged.liftWGObserver (Queues.RoutingJoint.setPeerCommand attrs))
      (Queues.RxHistory.mixed (Logged.liftWGObserver (Lifetimes.setPeerCmdPrefix attrs))) ∧
    Logged.ErasesStatePrefix (Queues.RoutingJoint.setPeerCommand attrs) (WG.setPeerCmd attrs) :=
  ⟨Queues.RoutingJoint.setPeerCommand_routing attrs,
    Queues.RoutingJoint.setPeerCommand_rx_product attrs,
    Queues.RoutingJoint.setPeerCommand_erases attrs⟩

/-- Whole device configuration retains the actual clears, saved peer loops,
attribute failures and key-update stages in one native and product execution. -/
theorem original_joint_device_configuration (attrs : DeviceAttrs) :
    Logged.StateProjectsPrefix Queues.RoutingJoint.routingEvent id
      (Queues.RoutingJoint.setDevice attrs) (Configuration.wgSetDeviceObserved attrs) ∧
    Logged.ProjectsPrefix Queues.RoutingJoint.rxEvent id
      (Logged.liftWGObserver (Queues.RoutingJoint.setDevice attrs))
      (Queues.RxHistory.mixed (Logged.liftWGObserver (Lifetimes.wgSetDevicePrefix attrs))) ∧
    Logged.ErasesStatePrefix (Queues.RoutingJoint.setDevice attrs) (WG.wgSetDevice attrs) :=
  ⟨Queues.RoutingJoint.setDevice_routing attrs,
    Queues.RoutingJoint.setDevice_rx_product attrs,
    Queues.RoutingJoint.setDevice_erases attrs⟩

/-- The empty actual WG fixture establishes the joint current, R2 boundary
and receiving-owner invariant for both original fixture flags. -/
theorem original_owner_checked_fixture (net bare : Bool) (w : World)
    (hw : Framing.wgStoreView w.wg = Framing.wgStoreView (Runner.initialWG net bare)) :
    OwnerChecks.Inv [] w :=
  OwnerChecks.initial net bare w hw

/-- A named actual decrypt occurrence uses its strict earlier session prefix
and captured input carrier; successful publication keeps one current witness.
This is a safe-journal extraction, not initialized caller closure. -/
theorem original_owner_checked_publication
    (h pre post : List Queues.RxHistory.Event) (id : SkbId)
    (r : Logged.WGRunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (pid : PeerId) (v : WGWorld) (ambient : Ambient)
    (safe : OwnerChecks.Safe h)
    (position : h = pre ++ .rx (.decrypt id r) :: post)
    (published : PublicationIdentity.Published id r out pid v ambient) :
    PublicationIdentity.CurrentCertificate (Origins.HistorySupport.sessions pre) id r out pid v :=
  OwnerChecks.Safe.published safe position published

/-- Original receive admission, queue installation and cleanup preserve the
carrier from the input allocation invariant, including ordinary refusal paths. -/
theorem original_owner_consume (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (history : List Lifetimes.LifetimeEvent) :
    Framing.Hoare (WG.consumeData msg src ds)
      (fun w => Lifetimes.AllocationInv history w ∧ OwnerBounds.Carrier w)
      (fun _ w => OwnerBounds.Carrier w) :=
  OwnerConsume.consumeData_spec msg src ds history

/-- The same actual lifetime observer carries current checks, allocation
safety and owner bounds; the allocation premise is its own input journal. -/
theorem original_owner_checked_consume (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    OwnerChecks.Preserves
      (Queues.RxHistory.mixed (Logged.liftWGObserver (Lifetimes.consumeDataPrefix msg src ds))) :=
  OwnerChecks.consumeData msg src ds


/-- Concrete packet and UDP receive observers carry the joint invariant on
the same lifetime journal, preserving normal refusals and stopped prefixes. -/
theorem original_owner_checked_receive (msg : List UInt8) (src : SkbSource) :
    OwnerChecks.Preserves
      (Queues.RxHistory.mixed (Logged.liftWGObserver (Lifetimes.packetReceivePrefix msg src))) ∧
    OwnerChecks.Preserves
      (Queues.RxHistory.mixed (Logged.liftWGObserver (Lifetimes.wgReceivePrefix msg src))) :=
  ⟨OwnerReceive.packetReceive_checked msg src,OwnerReceive.wgReceive_checked msg src⟩

/-- Concrete decrypt discharges the native carrier obligation at the actual
captured entry. Publication and prepare preserve the same carrier before IRQ. -/
theorem original_owner_decrypt :
    (∀ id, OwnerChecks.Preserves (Origins.HistoryAdapters.decrypt id)) ∧
    (∀ id state, Framing.Preserves OwnerBounds.Carrier (Queues.RxWorkers.publishSource id state)) ∧
    Framing.Preserves OwnerBounds.Carrier Queues.RxWorkers.prepareSource :=
  ⟨OwnerDecrypt.decrypt,OwnerDecrypt.publishSource_preserves,OwnerDecrypt.prepareSource_preserves⟩

/-- The original product decrypt step retains arbitrary IRQ and softirq
callbacks under their stated carrier contracts, including actual final repayment. -/
theorem original_owner_decrypt_worker (softirq irq : Leanux.M Unit)
    (hs : Framing.Preserves (fun w : World => OwnerBounds.Carrier w.wg) softirq)
    (hi : Framing.Preserves (fun w : World => OwnerBounds.Carrier w.wg) irq) :
    Framing.Preserves (fun w : World => OwnerBounds.Carrier w.wg) (WG.decryptStep softirq irq) :=
  OwnerDecrypt.decryptStep_preserves softirq irq hs hi


/-- Full wgSet entry, dispatch and return-to-user waits share one actual
execution. Both original streams and every stopped prefix project exactly. -/
theorem original_joint_set_syscall (attrs : DeviceAttrs) :
    Logged.ProjectsPrefix Queues.RoutingJoint.routingEvent id
      (Queues.RoutingJoint.syscallSet attrs) (Configuration.syscallObserved (.wgSet attrs)) ∧
    Logged.ProjectsPrefix Queues.RoutingJoint.rxEvent id
      (Queues.RoutingJoint.syscallSet attrs) (Queues.RxHistory.syscall (.wgSet attrs)) ∧
    Logged.ErasesPrefix (Queues.RoutingJoint.syscallSet attrs) (Leanux.syscall (.wgSet attrs)) :=
  ⟨Queues.RoutingJoint.syscallSet_routing attrs,
    Queues.RoutingJoint.syscallSet_rx attrs,Queues.RoutingJoint.syscallSet_erases attrs⟩


/-- All fifteen remaining environment cases retain positional current checks
on the original journals, including failed prefixes. -/
theorem original_current_remaining (call : Lifetimes.EnvRemainingCall) :
    CurrentChecks.Preserves (Queues.RxHistory.remaining call) :=
  CurrentRemaining.remaining call

/-- Native consume completion and its original lifetime observer preserve
receiving-owner bounds through key updates, staging and final payment. -/
theorem original_owner_completion (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Framing.Preserves OwnerBounds.Carrier (WG.consumeDataDone pid pkt endpoint) ∧
    OwnerChecks.Preserves (Queues.RxHistory.mixed
      (Logged.liftWGObserver (Lifetimes.consumeDataDonePrefix pid pkt endpoint))) :=
  ⟨OwnerCompletion.consumeDataDone_preserves pid pkt endpoint,
    OwnerCompletion.consumeDataDone_checked pid pkt endpoint⟩

/-- The product poll retains arbitrary callbacks under their precise carrier
contract; the actual stack callback discharges that contract. -/
theorem original_owner_poll (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, Framing.Preserves (fun w : World => OwnerBounds.Carrier w.wg) (callback xs)) :
    Framing.Preserves (fun w : World => OwnerBounds.Carrier w.wg)
      (WG.rxPoll pid budget callback) ∧
    Framing.Preserves (fun w : World => OwnerBounds.Carrier w.wg)
      (WG.rxPoll pid budget (fun packets => packets.forM Leanux.Env.deliverInner)) :=
  ⟨OwnerPoll.poll pid budget callback hc,OwnerStack.poll_stack pid budget⟩

/-- Actual poll and NAPI observers retain current checks, owner bounds and
the same allocation journal, including stopped prefixes. -/
theorem original_owner_checked_poll (pid : PeerId) (budget : Nat) :
    OwnerChecks.Preserves (Queues.RxHistory.observePoll pid budget) ∧
    OwnerChecks.Preserves Queues.RxHistory.napiSoftirq ∧
    OwnerChecks.Preserves Queues.RxHistory.pollScheduledInline ∧
    OwnerChecks.Preserves Queues.RxHistory.napiIrqExit :=
  ⟨OwnerWorkers.poll pid budget,OwnerWorkers.napiSoftirq,
    OwnerWorkers.pollScheduledInline,OwnerWorkers.napiIrqExit⟩

/-- Both concrete crypt workers retain the checked carrier. Prepare checks
the captured decrypt entry before its actual publication. -/
theorem original_owner_checked_crypt :
    OwnerChecks.Preserves Origins.HistoryAdapters.prepare ∧
    OwnerChecks.Preserves Queues.RxHistory.decryptStep ∧
    OwnerChecks.Preserves Queues.RxHistory.decryptIteration ∧
    OwnerChecks.Preserves Queues.RxHistory.encryptIteration :=
  ⟨OwnerPrepare.prepare,OwnerCryptWorkers.decryptStep,
    OwnerCryptWorkers.decryptIteration,OwnerEncrypt.encryptIteration⟩

/-- Concrete transmit completion and the actual transmit observer retain
receiving-owner checks through final key/peer payments. -/
theorem original_owner_checked_transmit (pid : PeerId) :
    Framing.Preserves OwnerBounds.Carrier (WG.txStep pid) ∧
    OwnerChecks.Preserves (Queues.RxHistory.mixed
      (Lifetimes.txIterPrefix pid (Logged.liftPrefix (Env.condResched .txWorker)))) :=
  ⟨OwnerTransmit.txStep_preserves pid,OwnerTransmit.txIteration pid⟩

/-- Peer configuration retains nullable ownership and every source guard;
ordinary errors may retain partial changes and final payment may delete. -/
theorem original_owner_configuration_tail (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Framing.Preserves OwnerBounds.Carrier
      (Configuration.peerConfigUpdateSource attrs peer flags psk pid) :=
  OwnerPeerConfiguration.peerConfigUpdate_preserves attrs peer flags psk pid

/-- The whole peer command carries current identity and owner bounds jointly,
including actual creation at the peer frontier and all normal errno returns. -/
theorem original_owner_checked_peer_command (attrs : PeerAttrs)
    (history : List SessionOrigin.Receipt) :
    Framing.Preserves (JointOwnerConfiguration.Inv history) (WG.setPeerCmd attrs) ∧
    OwnerChecks.Preserves (Queues.RxHistory.mixed
      (Logged.liftWGObserver (Lifetimes.setPeerCmdPrefix attrs))) :=
  ⟨JointOwnerConfiguration.setPeerCmd_preserves attrs history,
    JointOwnerConfiguration.setPeerCmd_checked attrs⟩

/-- Whole device configuration derives joint owner/current preservation
through key changes, remove-all, and every actual peer command. -/
theorem original_owner_checked_device_configuration (attrs : DeviceAttrs)
    (history : List SessionOrigin.Receipt) :
    Framing.Preserves (JointOwnerConfiguration.Inv history) (WG.wgSetDevice attrs) ∧
    OwnerChecks.Preserves (Queues.RxHistory.mixed
      (Logged.liftWGObserver (Lifetimes.wgSetDevicePrefix attrs))) :=
  ⟨JointOwnerDevice.wgSetDevice_preserves attrs history,
    JointOwnerDevice.wgSetDevice_checked attrs⟩

/-- Actual peer removal and device teardown preserve receiving-owner bounds.
Queued-work rejection and all other source Stops remain possible. -/
theorem original_owner_removal (peer : Option PeerId) :
    Framing.Preserves OwnerBounds.Carrier (WG.peerRemove peer) ∧
    Framing.Preserves OwnerBounds.Carrier WG.peerRemoveAll ∧
    Framing.Preserves OwnerBounds.Carrier WG.wgStop ∧
    Framing.Preserves OwnerBounds.Carrier WG.wgDown ∧
    Framing.Preserves OwnerBounds.Carrier WG.wgDestruct :=
  ⟨OwnerRemoval.peerRemove_preserves peer,OwnerDevice.peerRemoveAll_preserves,
    OwnerDevice.wgStop_preserves,OwnerDevice.wgDown_preserves,OwnerDevice.wgDestruct_preserves⟩

/-- Creation derives empty-key/RX bounds for a fresh device. Deletion keeps
its arbitrary native notifier callbacks and their stated contracts. -/
theorem original_owner_device_lifecycle (onDown onUnregister : WG.M Unit)
    (down : Framing.Preserves OwnerBounds.Carrier onDown)
    (unregister : Framing.Preserves OwnerBounds.Carrier onUnregister) :
    Framing.Preserves OwnerBounds.Carrier WG.wgCreate ∧
    Framing.Preserves OwnerBounds.Carrier (WG.wgDelete onDown onUnregister) :=
  ⟨OwnerDeviceCreation.wgCreate_preserves,
    OwnerDeviceCreation.wgDelete_preserves onDown onUnregister down unregister⟩

/-- Every actual syscall constructor has both original journal projections
and exact executable erasure, for arbitrary incoming histories and Stops. -/
theorem original_joint_syscall (call : Syscall) :
    Logged.ProjectsPrefix Queues.RoutingJoint.routingEvent id
      (Queues.RoutingJoint.syscall call) (Configuration.syscallObserved call) ∧
    Logged.ProjectsPrefix Queues.RoutingJoint.rxEvent id
      (Queues.RoutingJoint.syscall call) (Queues.RxHistory.syscall call) ∧
    Logged.ErasesPrefix (Queues.RoutingJoint.syscall call) (Leanux.syscall call) :=
  ⟨Queues.RoutingJoint.syscall_routing call,Queues.RoutingJoint.syscall_rx call,
    Queues.RoutingJoint.syscall_erases call⟩

/-- Both original initialized observers arise from one typed execution. The
RX projection drops the successful final World only; errors keep their index. -/
theorem original_joint_runner (trace : Runner.Trace) (placeholders : Bool) :
    Logged.ProjectsOuter Queues.RoutingJoint.routingEvent id
      (Queues.RoutingJoint.executeTrace trace placeholders)
      (Configuration.executeTraceObserved trace placeholders) ∧
    Logged.ProjectsOuter Queues.RoutingJoint.rxEvent Prod.fst
      (Queues.RoutingJoint.executeTrace trace placeholders)
      (Queues.RxHistory.executeTraceHistory trace placeholders) ∧
    Logged.ErasesOuter (Queues.RoutingJoint.executeTrace trace placeholders)
      (Configuration.sourceRunner trace placeholders) :=
  ⟨Queues.RoutingJoint.executeTrace_routing trace placeholders,
    Queues.RoutingJoint.executeTrace_rx trace placeholders,
    Queues.RoutingJoint.executeTrace_erases trace placeholders⟩

/-- The joint runner has the public runner's exact JSON/error result without
an address-shape, successful-run or initialized-authorization assumption. -/
theorem original_joint_runner_json (trace : Runner.Trace) (placeholders : Bool)
    (history : List Queues.RoutingJoint.Event) :
    (Logged.runPrefixOuter (Queues.RoutingJoint.executeTrace trace placeholders) history).1.map Prod.fst =
      Runner.executeTrace trace placeholders :=
  Queues.RoutingJoint.executeTrace_json trace placeholders history

/-- The actual handshake worker retains current and owner checks on its exact
journal. Session creation supplies actual receipts and Stops retain safe prefixes. -/
theorem original_owner_receive_worker :
    OwnerChecks.Preserves Origins.HistoryAdapters.receiveStep ∧
    OwnerChecks.Preserves Origins.HistoryAdapters.receiveIteration :=
  ⟨OwnerHandshake.receiveStep,OwnerHandshake.receiveIteration⟩

/-- Every recorded scheduler choice and nested reschedule retains owner/current
checks, including crypt-ahead and the existing copied-trial marker. -/
theorem original_owner_scheduler (stack : Option Worker) (self : Worker) :
    OwnerChecks.Preserves (Queues.RxHistory.schedule stack) ∧
    OwnerChecks.Preserves (Queues.RxHistory.nestedResched self) :=
  ⟨OwnerEnvironment.schedule stack,OwnerEnvironment.nestedResched self⟩

/-- All five actual timer callbacks preserve receiving-owner bounds and the
original checked journal, including duplicate-work refusal and final payment. -/
theorem original_owner_timer (pid : PeerId) (timer : PeerTimer) :
    Framing.Preserves OwnerBounds.Carrier (WG.timerCallback pid timer) ∧
    OwnerChecks.Preserves (Queues.RxHistory.mixed
      (Logged.liftWGObserver (Lifetimes.timerCallbackPrefix pid timer))) :=
  ⟨OwnerTimers.timerCallback_preserves pid timer,OwnerTimers.timerCallback_checked pid timer⟩

/-- All fourteen deferred calls preserve the same checked invariant. Timer
scans obtain their saved-peer conditions from their actual preceding getters. -/
theorem original_owner_deferred (call : Lifetimes.EnvDeferredCall) :
    OwnerChecks.Preserves (Queues.RxHistory.deferred call) :=
  OwnerDeferred.deferred call

/-- The actual fixture has no crypted RX packet needing a historical anchor,
for both flags. This is initialization only, not whole-run transport. -/
theorem original_packet_history_initial (net bare : Bool) (w : WGWorld)
    (hw : Framing.wgStoreView w = Framing.wgStoreView (Runner.initialWG net bare)) :
    PublicationHistory.Inv [] w :=
  PublicationHistory.initial net bare w hw

/-- Actual prepare preserves every old crypted-packet anchor and establishes
its selected anchor at successful publication. Failed decryption publishes DEAD;
a Stop keeps the actual safe journal and has no fictitious final state. -/
theorem original_packet_history_prepare :
    Logged.PrefixPreserves (fun h w => OwnerChecks.Inv h w ∧ PublicationHistory.Inv h w.wg)
      OwnerChecks.Safe Origins.HistoryAdapters.prepare :=
  PublicationHistory.prepare_preserves

/-- Normal consume, including nondelivery, links its exact receipt to a strict
earlier decrypt occurrence under the supplied packet invariant. The caller must
carry that invariant on its own real prefix; initialized reachability is separate. -/
theorem original_packet_history_consume (history : List Queues.RxHistory.Event) (pid occurrence id : Nat)
    (stamp : Lifetimes.PacketStamp) (pkt : RxPacket) (ep : Endpoint) (w v : World)
    (h t : List Queues.RxJoint.Event) (value : Option Queues.RxJoint.Entry)
    (packets : PublicationHistory.Inv history w.wg)
    (selected : Queues.RxDisposition.SelectedAt id stamp pkt w)
    (peer : pkt.peer = pid) (crypted : pkt.state = .crypted)
    (hr : Logged.runPrefix (Queues.RxJoint.consume pid occurrence id stamp pkt ep) w h = (.ok (value,v),t)) :
    ∃ prior later, ∃ (decrypt : Logged.WGRunWitness (RxPacket × Option RxPacket)),
      ∃ out publishedPeer published publicationAmbient,
      ∃ (receipt : Queues.RxDisposition.ConsumeReceipt), ∃ before after,
      history = prior ++ .rx (.decrypt id decrypt) :: later ∧
      PublicationIdentity.Published id decrypt out publishedPeer published publicationAmbient ∧
      receipt.run.before = w.wg ∧ receipt.run.ambientBefore = w.ambient ∧
      receipt.run.after = v.wg ∧ receipt.run.ambientAfter = v.ambient ∧
      PublicationIdentity.ConsumeCertificate (Origins.HistorySupport.sessions prior)
        id decrypt out publishedPeer published stamp receipt ∧
      t = h ++ before ++ [.consumed occurrence id stamp receipt] ++ after ∧
      ∀ e, value = some e → e.origin = some receipt ∧ receipt.run.value = some e.tag.bytes :=
  PublicationHistory.consume_anchored history pid occurrence id stamp pkt ep w v h t value packets selected peer crypted hr

/-- Every remaining environment constructor keeps the actual owner/current
checks and failed prefix, with no substituted callback. -/
theorem original_owner_remaining (call : Lifetimes.EnvRemainingCall) :
    OwnerChecks.Preserves (Queues.RxHistory.remaining call) :=
  OwnerRemaining.remaining call

/-- Every original syscall dispatch arm and its source-designated wait suffix
preserves the checked journal, including normal errno and Stop paths. -/
theorem original_owner_syscall (call : Syscall) :
    OwnerChecks.Preserves (Queues.RxHistory.syscallDispatch call) ∧
    OwnerChecks.Preserves (Queues.RxHistory.syscall call) :=
  ⟨OwnerSyscalls.dispatch call,OwnerSyscalls.syscall call⟩

/-- The fixture starts with no crypted RX cells. Actual publication establishes
the peer frontier bound used by later creation, separately from key validity. -/
theorem original_packet_frontier_initial (net bare : Bool) (w : WGWorld)
    (hw : Framing.wgStoreView w = Framing.wgStoreView (Runner.initialWG net bare)) :
    PublicationFrontier.Inv [] w := PublicationFrontier.initial net bare w hw

/-- The existing prepare observer carries both the earlier publication anchor
and its concrete peer-slot bound; Stop asserts only the actual safe prefix. -/
theorem original_packet_frontier_prepare :
    Logged.PrefixPreserves (fun h w => OwnerChecks.Inv h w ∧ PublicationFrontier.Inv h w.wg)
      OwnerChecks.Safe Origins.HistoryAdapters.prepare :=
  PublicationFrontier.prepare_preserves

/-- Fresh peer creation preserves old published packets without a vacant-slot
premise. Their saved peer IDs lie below the allocation frontier. -/
theorem original_packet_frontier_create (key : Key) (psk : Option Key)
    (history : List Queues.RxHistory.Event) :
    Framing.Preserves (PublicationFrontier.Inv history) (WG.peerCreate key psk) :=
  PublicationFrontier.peerCreate_preserves key psk history

/-- Packet freeing removes only that obligation; setup establishes an empty
population. Neither operation transports a certificate across an arbitrary reset. -/
theorem original_packet_frontier_lifecycle (id : SkbId) (history : List Queues.RxHistory.Event) :
    Framing.Preserves (PublicationFrontier.Inv history) (WG.freeRxSkb id) ∧
    Framing.Hoare WG.wgSetup (fun _ => True) (fun _ w => PublicationFrontier.Inv history w) :=
  ⟨PublicationFrontier.freeRxSkb_preserves id history,PublicationFrontier.wgSetup_establishes history⟩

/-- Actual completion preserves each stored packet's earlier publication,
including staged sends and peer disappearance, without later key validity. -/
theorem original_packet_history_completion (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (history : List Queues.RxHistory.Event) :
    Framing.Preserves (PublicationHistory.Inv history) (WG.consumeDataDone pid pkt endpoint) :=
  PublicationCompletion.consumeDataDone_preserves pid pkt endpoint history

/-- Every typed initialized trace, under either placeholder setting, preserves
all captured current/owner checks on its actual completed or stopped journal. -/
theorem original_owner_runner (trace : Runner.Trace) (placeholders : Bool) :
    OwnerChecks.Safe (Logged.runPrefixOuter
      (Queues.RxHistory.executeTraceHistory trace placeholders) []).2 :=
  OwnerRunner.executeTrace trace placeholders

/-- Each reached initialized decrypt uses one specified strict earlier session
prefix, together with the owner bounds of that exact captured WG state. -/
theorem original_initialized_decrypt (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Queues.RxHistory.Event) (id : SkbId)
    (r : Logged.WGRunWitness (RxPacket × Option RxPacket))
    (position : (Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .rx (.decrypt id r) :: post) :
    CurrentLifecycle.Inv (Origins.HistorySupport.sessions pre) r.before ∧ OwnerBounds.Carrier r.before :=
  OwnerRunner.decrypt trace placeholders pre post id r position

/-- Copied-trial probes have their actual earlier allocation history and
captured current/owner facts; the trial is not a committed callback occurrence. -/
theorem original_initialized_owner_probe (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Queues.RxHistory.Event) (p : Lifetimes.ProbeEntry)
    (position : (Logged.runPrefixOuter (Queues.RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .audit (.probe p) :: post) :
    p.history = Queues.RxHistory.prior pre ∧ CurrentSessionPrefix.StateInv pre p.world ∧
      OwnerBounds.Carrier p.world.wg :=
  OwnerRunner.probe trace placeholders pre post p position

/-- Owner checks, exact packet linkage and routing-completion safety are
projections of one actual initialized journal. Routing keeps its shape premise. -/
theorem original_joint_initialized_checks (trace : Runner.Trace)
    (shape : Configuration.TraceAddressShape trace) (placeholders : Bool) :
    let h := (Logged.runPrefixOuter (Queues.RoutingJoint.executeTrace trace placeholders) []).2
    OwnerChecks.Safe (h.filterMap Queues.RoutingJoint.rxEvent) ∧
    Queues.RxLink.HistoryLinked (h.filterMap Queues.RoutingJoint.rxEvent) ∧
    Queues.RxLink.HistoryReceiptsValid (h.filterMap Queues.RoutingJoint.rxEvent) ∧
    AllowedIps.CompletionSafe ([],[]) (h.filterMap Queues.RoutingJoint.routingEvent) :=
  RoutingPosition.executeTrace_checks trace shape placeholders

/-- The actual poll preserves routing at every captured consume entry,
including normal nondelivery and the prefix of an eventual Stop. -/
theorem original_poll_positional_routing (initial : AllowedIps.FlatTable × AllowedIps.FlatTable)
    (pid : PeerId) (budget : Nat) :
    Logged.PrefixPreserves (RoutingPosition.Inv initial) (RoutingPosition.Safe initial)
      (Queues.RoutingJoint.rxAction (Queues.RxHistory.observePoll pid budget)) :=
  RoutingPosition.Poll.observePoll initial pid budget

/-- A successful consume uses the routing table at its own strict joint
prefix. This local theorem exposes the remaining initialized positional premise. -/
theorem original_consumed_routing_authorization
    (initial : AllowedIps.FlatTable × AllowedIps.FlatTable)
    (h pre post : List Queues.RoutingJoint.Event) (occurrence id : Nat)
    (stamp : Lifetimes.PacketStamp) (receipt : Queues.RxDisposition.ConsumeReceipt)
    (checks : RoutingPosition.Checks initial h)
    (position : h = pre ++ .rx (.consumed occurrence id stamp receipt) :: post)
    (valid : receipt.Valid) (bytes : List UInt8) (delivered : receipt.run.value = some bytes) :
    ∃ v4 : Bool, ipTunnelParseProtocol bytes = (if v4 then 4 else 6) ∧
      ipTunnelParseProtocol receipt.packet.bytes = (if v4 then 4 else 6) ∧
      AllowedIps.PeerWinner (AllowedIps.rootWidth v4) (AllowedIps.sourceAddress v4 bytes)
        (AllowedIps.selectedFlat v4 (AllowedIps.completionFold
          (pre.filterMap Queues.RoutingJoint.routingEvent) initial)) (some receipt.peer) ∧
      AllowedIps.sourceAddress v4 bytes = AllowedIps.sourceAddress v4 receipt.packet.bytes :=
  RoutingPosition.consume_authorized checks position valid bytes delivered

/-- Native UDP admission preserves existing encrypted publications while
its new UNCRYPTED/DEAD cells create no certificate obligation. -/
theorem original_packet_frontier_ingress (msg : List UInt8) (src : SkbSource)
    (history : List Queues.RxHistory.Event) :
    Framing.Preserves (PublicationFrontier.Inv history) (WG.wgReceive msg src) :=
  PublicationFrontier.wgReceive_preserves msg src history

/-- Key allocation and rotation retain existing encrypted packet anchors;
the allocating front is not required to keep the old key frontier. -/
theorem original_packet_frontier_session (pid : PeerId) (history : List Queues.RxHistory.Event) :
    Framing.Preserves (PublicationFrontier.Inv history) (WG.beginSession pid) :=
  PublicationFrontier.beginSession_preserves pid history

/-- Actual handshake reception permits authentication failures, nullable
reference payments and new sessions while preserving older packet anchors. -/
theorem original_packet_frontier_handshake (history : List Queues.RxHistory.Event) :
    Framing.Preserves (PublicationFrontier.Inv history) WG.receiveStep :=
  PublicationHandshake.receiveStep history

/-- Complete native removal retains publication anchors through concrete
queued work, both saved-peer passes and the original stopped drain behavior. -/
theorem original_packet_frontier_removal (call : Lifetimes.PeerRemovalCall)
    (history : List Queues.RxHistory.Event) :
    Framing.Preserves (PublicationFrontier.Inv history) call.original :=
  PublicationFrontier.removalCall_preserves call history

/-- Every newly consumed poll occurrence has its exact certificate under
its own strict earlier receive prefix. The concrete Stack callback is used. -/
theorem original_poll_publication_checks (pid : PeerId) (budget : Nat) :
    PublicationChecks.Preserves (Queues.RxHistory.observePoll pid budget) :=
  PublicationChecks.actual_poll pid budget

/-- The actual empty fixture establishes the combined packet and owner
invariant from the WG store projection alone, for either fixture flag. -/
theorem original_publication_joint_initial (net bare : Bool) (w : World)
    (hw : Framing.wgStoreView w.wg = Framing.wgStoreView (Runner.initialWG net bare)) :
    PublicationJoint.Inv [] w := PublicationJoint.initial net bare w hw

/-- A real prepare publication establishes the new anchor and peer bound
while leaving earlier consume certificates at their original positions. -/
theorem original_publication_joint_prepare : PublicationJoint.Preserves Origins.HistoryAdapters.prepare :=
  PublicationJoint.prepare

/-- Poll combines the original owner evidence and positional publication
certificates on exactly the same normal or stopped invocation. -/
theorem original_publication_joint_poll (pid : PeerId) (budget : Nat) :
    PublicationJoint.Preserves (Queues.RxHistory.observePoll pid budget) :=
  PublicationJoint.poll pid budget

/-- All three scheduling entry points use the same combined packet history. -/
theorem original_publication_joint_napi :
    PublicationJoint.Preserves Queues.RxHistory.napiSoftirq ∧
    PublicationJoint.Preserves Queues.RxHistory.pollScheduledInline ∧
    PublicationJoint.Preserves Queues.RxHistory.napiIrqExit :=
  ⟨PublicationJoint.napiSoftirq,PublicationJoint.pollScheduledInline,PublicationJoint.napiIrqExit⟩

/-- Actual crypt workers preserve the joint invariant, including prepare,
NAPI callbacks, encryption writes and the source rescheduling decisions. -/
theorem original_publication_joint_crypt :
    PublicationJoint.Preserves Queues.RxHistory.decryptIteration ∧
    PublicationJoint.Preserves Queues.RxHistory.encryptIteration :=
  ⟨PublicationJoint.decryptIteration,PublicationJoint.encryptIteration⟩

/-- The original handshake iteration carries owner facts and older packet
certificates through the actual session journal and rescheduling call. -/
theorem original_publication_joint_receive :
    PublicationJoint.Preserves Origins.HistoryAdapters.receiveIteration :=
  PublicationJoint.receiveIteration


section PublicationClosure
open Leanux.Proofs.Logged

/-- Actual crypt/receive iterations keep routing at each consumed occurrence.
No routing fact is inferred from the eventual endpoint of the whole run. -/
theorem original_positional_routing_workers (initial : AllowedIps.FlatTable × AllowedIps.FlatTable) :
    RoutingPosition.Callers.Focused initial Origins.HistoryAdapters.receiveIteration ∧
    RoutingPosition.Callers.Focused initial Queues.RxHistory.decryptIteration ∧
    RoutingPosition.Callers.Focused initial Queues.RxHistory.encryptIteration :=
  ⟨RoutingPosition.Callers.receiveIteration initial,RoutingPosition.Callers.decryptIteration initial,
    RoutingPosition.Callers.encryptIteration initial⟩

/-- The original scheduling calls retain actual captured consume prefixes,
including cryptAhead and nested rescheduling. -/
theorem original_positional_routing_scheduler (initial : AllowedIps.FlatTable × AllowedIps.FlatTable)
    (activation : Activation) (worker : Worker) (stack : Option Worker) (pid : PeerId) :
    RoutingPosition.Callers.Focused initial (Queues.RxHistory.cryptAhead pid) ∧
    RoutingPosition.Callers.Focused initial (Queues.RxHistory.activationRun activation) ∧
    RoutingPosition.Callers.Focused initial (Queues.RxHistory.dispatch worker) ∧
    RoutingPosition.Callers.Focused initial (Queues.RxHistory.schedule stack) ∧
    RoutingPosition.Callers.Focused initial (Queues.RxHistory.nestedResched worker) :=
  ⟨RoutingPosition.Environment.cryptAhead initial pid,RoutingPosition.Environment.activationRun initial activation,
    RoutingPosition.Environment.dispatch initial worker,RoutingPosition.Environment.schedule initial stack,
    RoutingPosition.Environment.nestedResched initial worker⟩

/-- All original deferred constructors carry the positional routing checks. -/
theorem original_positional_routing_deferred (initial : AllowedIps.FlatTable × AllowedIps.FlatTable)
    (call : Lifetimes.EnvDeferredCall) :
    RoutingPosition.Callers.Focused initial (Queues.RxHistory.deferred call) :=
  RoutingPosition.Deferred.deferred initial call

/-- Configuration changes the routing journal and leaves earlier consume
positions fixed. Address shape is the existing configuration premise. -/
theorem original_positional_routing_configuration (initial : AllowedIps.FlatTable × AllowedIps.FlatTable)
    (attrs : DeviceAttrs) (shape : Configuration.DeviceAddressShape attrs) :
    PrefixPreserves (RoutingPosition.Inv initial) (RoutingPosition.Safe initial)
      (Queues.RoutingJoint.dispatchSet attrs) ∧
    PrefixPreserves (RoutingPosition.Inv initial) (RoutingPosition.Safe initial)
      Queues.RoutingJoint.dispatchCreate ∧
    PrefixPreserves (RoutingPosition.Inv initial) (RoutingPosition.Safe initial)
      Queues.RoutingJoint.dispatchDelete :=
  ⟨RoutingPosition.Controls.dispatchSet initial attrs shape,RoutingPosition.Controls.dispatchCreate initial,
    RoutingPosition.Controls.dispatchDelete initial⟩

/-- Actual transmit completion preserves the packet/owner checks already
recorded in the incoming receive journal. -/
theorem original_publication_joint_transmit (pid : PeerId) :
    PublicationJoint.Preserves (Queues.RxHistory.mixed
      (Lifetimes.txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  PublicationJoint.txIteration pid

/-- The combined packet journal traverses the full recorded scheduler. -/
theorem original_publication_joint_scheduler (activation : Activation) (worker : Worker)
    (stack : Option Worker) :
    PublicationJoint.Preserves (Queues.RxHistory.activationRun activation) ∧
    PublicationJoint.Preserves (Queues.RxHistory.dispatch worker) ∧
    PublicationJoint.Preserves (Queues.RxHistory.schedule stack) ∧
    PublicationJoint.Preserves (Queues.RxHistory.nestedResched worker) :=
  ⟨PublicationJoint.activationRun activation,PublicationJoint.dispatch worker,
    PublicationJoint.schedule stack,PublicationJoint.nestedResched worker⟩

/-- Every actual peer timer callback retains older positional certificates. -/
theorem original_publication_joint_timer (pid : PeerId) (timer : PeerTimer) :
    PublicationJoint.Preserves (Queues.RxHistory.mixed
      (liftWGObserver (Lifetimes.timerCallbackPrefix pid timer))) :=
  PublicationJoint.timerCallback pid timer

/-- All fourteen deferred constructors retain normal state and stopped checks;
saved-device scans use the actual getter receipt. -/
theorem original_publication_joint_deferred (call : Lifetimes.EnvDeferredCall) :
    PublicationJoint.Preserves (Queues.RxHistory.deferred call) := PublicationDeferred.deferred call

/-- Actual ingress, exact flood and full batch observers preserve the same
packet journal through their scheduler, worker and poll calls. -/
theorem original_publication_joint_traffic (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest count : Nat) (messages : List (List UInt8))
    (items : List Env.BatchItem) :
    PublicationJoint.Preserves (Queues.RxHistory.inject family port msg tos ll dest) ∧
    PublicationJoint.Preserves (Queues.RxHistory.flood count port family messages) ∧
    PublicationJoint.Preserves (Queues.RxHistory.batch items) :=
  ⟨PublicationTraffic.inject family port msg tos ll dest,
    PublicationTraffic.flood count port family messages,PublicationTraffic.batch items⟩

/-- Peer/device commands keep arbitrary old packet histories through actual
creation, private-key replacement, removal and partial negative-errno updates. -/
theorem original_publication_joint_configuration (pid : PeerId) (ip : AllowedIpAttrs)
    (peer : PeerAttrs) (device : DeviceAttrs) :
    PublicationJoint.Preserves (Queues.RxHistory.mixed
      (liftWGObserver (Lifetimes.setAllowedipPrefix pid ip))) ∧
    PublicationJoint.Preserves (Queues.RxHistory.mixed
      (liftWGObserver (Lifetimes.setPeerCmdPrefix peer))) ∧
    PublicationJoint.Preserves (Queues.RxHistory.mixed
      (liftWGObserver (Lifetimes.wgSetDevicePrefix device))) :=
  ⟨PublicationJoint.setAllowedip pid ip,PublicationJoint.setPeerCmd peer,PublicationJoint.wgSetDevice device⟩

/-- Native lifecycle returns retain old publications, and actual creation
starts with an empty RX store. No normal state is asserted on a Stop. -/
theorem original_packet_frontier_device (history : List Queues.RxHistory.Event)
    (onDown onUnregister : WG.M Unit)
    (down : Framing.Preserves (PublicationFrontier.Inv history) onDown)
    (unregister : Framing.Preserves (PublicationFrontier.Inv history) onUnregister) :
    Framing.Preserves (PublicationFrontier.Inv history) WG.wgUp ∧
    Framing.Preserves (PublicationFrontier.Inv history) WG.wgDown ∧
    Framing.Preserves (PublicationFrontier.Inv history) WG.wgCreate ∧
    Framing.Preserves (PublicationFrontier.Inv history) WG.netnsPreExit ∧
    Framing.Preserves (PublicationFrontier.Inv history) (WG.wgDelete onDown onUnregister) :=
  ⟨PublicationFrontier.wgUp_preserves history,PublicationFrontier.wgDown_preserves history,
    PublicationFrontier.wgCreate_preserves history,PublicationFrontier.netnsPreExit_preserves history,
    PublicationFrontier.wgDelete_preserves onDown onUnregister history down unregister⟩

/-- The environment controls use the original product callbacks and guards,
including pending-dump deletion and namespace teardown. -/
theorem original_publication_joint_controls (mtu : Nat) :
    PublicationJoint.Preserves (Queues.RxHistory.audit Lifetimes.envWgUpAudit) ∧
    PublicationJoint.Preserves (Queues.RxHistory.audit Lifetimes.envWgDownAudit) ∧
    PublicationJoint.Preserves (Queues.RxHistory.audit Lifetimes.envWgDeleteAudit) ∧
    PublicationJoint.Preserves (Queues.RxHistory.audit Lifetimes.envNetnsCleanupAudit) ∧
    PublicationJoint.Preserves (Queues.RxHistory.audit (Lifetimes.setMtuAudit mtu)) ∧
    PublicationJoint.Preserves (Queues.RxHistory.mixed (liftWGObserver Lifetimes.wgCreatePrefix)) :=
  ⟨PublicationControls.up,PublicationControls.down,PublicationControls.delete,
    PublicationControls.netnsCleanup,PublicationControls.mtu mtu,PublicationControls.create⟩

/-- All seven dump observers retain their exact access and failed-prefix
history while carrying earlier packet publications through cursor payments. -/
theorem original_publication_joint_dump (call : Lifetimes.NetlinkDumpCall) :
    PublicationJoint.Preserves (Queues.RxHistory.mixed (liftWGObserver call.observed)) :=
  PublicationJoint.dump_checked call

/-- The seven syscall callbacks remain arbitrary actual product observers.
This is the concrete entry/dispatch/wait composition, not initialization. -/
theorem original_publication_outer_syscall (call : Syscall) (dispatch : Queues.RxHistory.Obs Int)
    (sendWorkers timers route xmit advance cleanup : Queues.RxHistory.Obs Unit)
    (hd : PublicationJoint.Preserves dispatch) (hs : PublicationJoint.Preserves sendWorkers)
    (ht : PublicationJoint.Preserves timers) (hr : PublicationJoint.Preserves route)
    (hx : PublicationJoint.Preserves xmit) (ha : PublicationJoint.Preserves advance)
    (hc : PublicationJoint.Preserves cleanup) :
    PublicationJoint.Preserves (Configuration.syscallWith (fun {_} a => liftPrefix a)
      dispatch sendWorkers timers route xmit advance cleanup call) :=
  PublicationOuter.syscallWith_preserves call dispatch sendWorkers timers route xmit advance cleanup hd hs ht hr hx ha hc

/-- The actual traffic families retain routing at each captured consume. -/
theorem original_positional_routing_traffic (initial : AllowedIps.FlatTable × AllowedIps.FlatTable)
    (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest count : Nat)
    (messages : List (List UInt8)) (items : List Env.BatchItem) :
    RoutingPosition.Callers.Focused initial (Queues.RxHistory.inject family port msg tos ll dest) ∧
    RoutingPosition.Callers.Focused initial (Queues.RxHistory.flood count port family messages) ∧
    RoutingPosition.Callers.Focused initial (Queues.RxHistory.batch items) :=
  ⟨RoutingPosition.Traffic.inject initial family port msg tos ll dest,
    RoutingPosition.Traffic.flood initial count port family messages,RoutingPosition.Traffic.batch initial items⟩

/-- Every remaining environment constructor carries publication certificates. -/
theorem original_publication_joint_remaining (call : Lifetimes.EnvRemainingCall) :
    PublicationJoint.Preserves (Queues.RxHistory.remaining call) := PublicationRemaining.remaining call

/-- All actual syscall arms and their return-to-user continuations preserve
packet and owner checks; no arbitrary callback premise remains. -/
theorem original_publication_joint_syscall (call : Syscall) :
    PublicationJoint.Preserves (Queues.RxHistory.syscall call) := PublicationSyscalls.syscall call

/-- The original fixture and complete syscall composition establish packet
publication and owner checks for every typed trace and both placeholder modes,
including the exact reached prefix of an indexed Stop. -/
theorem initialized_packet_publication (trace : Runner.Trace) (placeholders : Bool) :
    PublicationJoint.Safe ((runPrefixOuter (Queues.RoutingJoint.executeTrace trace placeholders) []).2.filterMap
      Queues.RoutingJoint.rxEvent) := PublicationRunner.joint trace placeholders

/-- This specified consumed occurrence has a strictly earlier successful
decrypt/publication with the same stored packet and historical identity witness. -/
theorem initialized_consumed_publication (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Queues.RoutingJoint.Event) (occurrence : Nat) (id : SkbId)
    (stamp : Lifetimes.PacketStamp) (receipt : Queues.RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (Queues.RoutingJoint.executeTrace trace placeholders) []).2 =
      pre ++ .rx (.consumed occurrence id stamp receipt) :: post) :
    PublicationPollChecks.Certified (pre.filterMap Queues.RoutingJoint.rxEvent) id stamp receipt :=
  PublicationRunner.joint_consumed trace placeholders pre post occurrence id stamp receipt position

open Lifetimes Queues PublicationIdentity AllowedIps in
/-- One specified Stack entry is linked to its earlier successful consume and
configured publication. Routing uses that same consume prefix; its supplied
positional premise is not replaced by a final-state or initialized claim. -/
theorem original_publication_entry_coupling {h pre post : List RoutingJoint.Event} {e : RxJoint.Entry}
    {initial : FlatTable × FlatTable}
    (linked : RxLink.HistoryLinked (h.filterMap RoutingJoint.rxEvent))
    (publication : PublicationChecks.Safe (h.filterMap RoutingJoint.rxEvent))
    (routing : RoutingPosition.Checks initial h)
    (position : h = pre ++ .rx (.entered e) :: post) :
    ∃ (receipt : RxDisposition.ConsumeReceipt), ∃ before between afterBuffer beforeDecrypt afterDecrypt,
      ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
      pre = before ++ .rx (.consumed e.tag.occurrence e.tag.skb e.stamp receipt) ::
        (between ++ .rx (.buffered e) :: afterBuffer) ∧
      before = beforeDecrypt ++ .rx (.rx (.decrypt e.tag.skb decrypt)) :: afterDecrypt ∧
      e.origin = some receipt ∧ receipt.run.value = some e.tag.bytes ∧
      Published e.tag.skb decrypt out pid published ambient ∧
      ConsumeCertificate (Origins.HistorySupport.sessions (beforeDecrypt.filterMap RoutingJoint.rxEvent))
        e.tag.skb decrypt out pid published e.stamp receipt ∧
      ∃ v4 : Bool,
        ipTunnelParseProtocol e.tag.bytes = (if v4 then 4 else 6) ∧
        ipTunnelParseProtocol receipt.packet.bytes = (if v4 then 4 else 6) ∧
        PeerWinner (rootWidth v4) (sourceAddress v4 e.tag.bytes)
          (selectedFlat v4 (completionFold (before.filterMap RoutingJoint.routingEvent) initial))
          (some receipt.peer) ∧
        sourceAddress v4 e.tag.bytes = sourceAddress v4 receipt.packet.bytes :=
  PublicationEntries.entered_authorized linked publication routing position


end PublicationClosure

section InitializedAuthorization
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues PublicationIdentity AllowedIps Configuration Packets

/-- All actual syscall callbacks retain routing at captured consume positions;
only the original configuration address-shape premise is supplied. -/
theorem original_positional_routing_syscall (initial : FlatTable × FlatTable)
    (call : Syscall) (shape : SyscallAddressShape call) :
    PrefixPreserves (RoutingPosition.Inv initial) (RoutingPosition.Safe initial)
      (RoutingJoint.syscall call) := RoutingPosition.Calls.syscall initial call shape

/-- The original initialized runner derives routing at each consume position,
including the reached journal of an indexed Stop. -/
theorem initialized_positional_routing (trace : Runner.Trace)
    (shape : TraceAddressShape trace) (placeholders : Bool) :
    RoutingPosition.Safe ([],[])
      (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2 :=
  RoutingPosition.Runner.executeTrace trace shape placeholders

/-- Successful public parsing discharges the routing shape premise. -/
theorem parsed_initialized_positional_routing (json : Lean.Json) (trace : Runner.Trace)
    (parsed : Runner.parseTrace json = .ok trace) (placeholders : Bool) :
    RoutingPosition.Safe ([],[])
      (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2 :=
  initialized_positional_routing trace (parseTrace_shape json trace parsed) placeholders

/-- An initialized Stack entry couples its actual earlier configured publication,
consume and strict-prefix source winner, without assuming normal termination. -/
theorem initialized_incoming_authorization (trace : Runner.Trace) (shape : TraceAddressShape trace) (placeholders : Bool)
    (pre post : List RoutingJoint.Event) (e : RxJoint.Entry)
    (position : (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2 =
      pre ++ .rx (.entered e) :: post) :
    ∃ (receipt : RxDisposition.ConsumeReceipt), ∃ before between afterBuffer beforeDecrypt afterDecrypt,
      ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
      pre = before ++ .rx (.consumed e.tag.occurrence e.tag.skb e.stamp receipt) ::
        (between ++ .rx (.buffered e) :: afterBuffer) ∧
      before = beforeDecrypt ++ .rx (.rx (.decrypt e.tag.skb decrypt)) :: afterDecrypt ∧
      e.origin = some receipt ∧ receipt.run.value = some e.tag.bytes ∧
      Published e.tag.skb decrypt out pid published ambient ∧
      ConsumeCertificate (Origins.HistorySupport.sessions (beforeDecrypt.filterMap RoutingJoint.rxEvent))
        e.tag.skb decrypt out pid published e.stamp receipt ∧
      ∃ v4 : Bool,
        ipTunnelParseProtocol e.tag.bytes = (if v4 then 4 else 6) ∧
        ipTunnelParseProtocol receipt.packet.bytes = (if v4 then 4 else 6) ∧
        PeerWinner (rootWidth v4) (sourceAddress v4 e.tag.bytes)
          (selectedFlat v4 (completionFold (before.filterMap RoutingJoint.routingEvent) ([],[])))
          (some receipt.peer) ∧
        sourceAddress v4 e.tag.bytes = sourceAddress v4 receipt.packet.bytes :=
  InitializedEntries.entered trace shape placeholders pre post e position

/-- The same incoming authorization for every successfully parsed public trace. -/
theorem parsed_initialized_incoming_authorization (json : Lean.Json) (trace : Runner.Trace)
    (parsed : Runner.parseTrace json = .ok trace) (placeholders : Bool)
    (pre post : List RoutingJoint.Event) (e : RxJoint.Entry)
    (position : (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2 =
      pre ++ .rx (.entered e) :: post) :
    ∃ (receipt : RxDisposition.ConsumeReceipt), ∃ before between afterBuffer beforeDecrypt afterDecrypt,
      ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
      pre = before ++ .rx (.consumed e.tag.occurrence e.tag.skb e.stamp receipt) ::
        (between ++ .rx (.buffered e) :: afterBuffer) ∧
      before = beforeDecrypt ++ .rx (.rx (.decrypt e.tag.skb decrypt)) :: afterDecrypt ∧
      e.origin = some receipt ∧ receipt.run.value = some e.tag.bytes ∧
      Published e.tag.skb decrypt out pid published ambient ∧
      ConsumeCertificate (Origins.HistorySupport.sessions (beforeDecrypt.filterMap RoutingJoint.rxEvent))
        e.tag.skb decrypt out pid published e.stamp receipt ∧
      ∃ v4 : Bool,
        ipTunnelParseProtocol e.tag.bytes = (if v4 then 4 else 6) ∧
        ipTunnelParseProtocol receipt.packet.bytes = (if v4 then 4 else 6) ∧
        PeerWinner (rootWidth v4) (sourceAddress v4 e.tag.bytes)
          (selectedFlat v4 (completionFold (before.filterMap RoutingJoint.routingEvent) ([],[])))
          (some receipt.peer) ∧
        sourceAddress v4 e.tag.bytes = sourceAddress v4 receipt.packet.bytes :=
  InitializedEntries.parsed_entered json trace parsed placeholders pre post e position

/-- The original transmit call factors through its actual completed splice. -/
theorem original_transmit_front_factor (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    wgXmit family addr pkts mtu = (do
      match ← txFront family addr pkts mtu with
      | .error err => pure err
      | .ok pid => txTail pid) :=
  wgXmit_front_factor family addr pkts mtu

/-- Local routing authorizes the completed splice independently of its later tail. -/
theorem original_transmit_handoff_front (v4 : Bool) (addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w s : WGWorld) (ambient afterSplice : Ambient) (pid : PeerId)
    (xs : FlatTable × FlatTable) (hi : RoutedView (routingView w) xs)
    (hr : ((txFront (if v4 then 4 else 6) addr pkts mtu).run w).run ambient =
      .ok ((.ok pid,s),afterSplice)) :
    TxFrontCut (if v4 then 4 else 6) addr pkts mtu w s ambient afterSplice pid ∧
      PeerWinner (rootWidth v4) addr (selectedFlat v4 xs) (some pid) ∧
      ∀ pkt ∈ pkts, destinationField (if v4 then 4 else 6) pkt.bytes = addr :=
  txFront_authorized v4 addr pkts mtu w s ambient afterSplice pid xs hi hr

/-- A later actual Stop retains the completed handoff certificate. -/
theorem original_transmit_handoff_stopped (v4 : Bool) (addr : Nat) (pkts : List Packet) (mtu : Nat)
    (w s : WGWorld) (ambient afterSplice : Ambient) (pid : PeerId)
    (xs : FlatTable × FlatTable) (stop : Stop)
    (routing : RoutedView (routingView w) xs)
    (front : ((txFront (if v4 then 4 else 6) addr pkts mtu).run w).run ambient =
      .ok ((.ok pid,s),afterSplice))
    (tail : ((txTail pid).run s).run afterSplice = .error stop) :
    ((wgXmit (if v4 then 4 else 6) addr pkts mtu).run w).run ambient = .error stop ∧
      TxFrontCut (if v4 then 4 else 6) addr pkts mtu w s ambient afterSplice pid ∧
      PeerWinner (rootWidth v4) addr (selectedFlat v4 xs) (some pid) ∧
      ∀ pkt ∈ pkts, destinationField (if v4 then 4 else 6) pkt.bytes = addr :=
  wgXmit_stopped_after_handoff v4 addr pkts mtu w s ambient afterSplice pid xs stop routing front tail
end InitializedAuthorization

section TransmitSource

open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues AllowedIps Packets

/-- The actual lifetime observer factors at the completed staging splice. -/
theorem original_transmit_observer_front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    wgXmitPrefix family addr packets mtu = (do
      match ← txFrontPrefix family addr packets mtu with
      | .error err => pure err
      | .ok pid => txTailPrefix pid) :=
  wgXmitPrefix_front_factor family addr packets mtu

/-- Removing only handoff receipts gives the old joint execution on its actual
incoming history, including every stopped prefix. -/
theorem original_transmit_handoff_projection (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateProjectsPrefix TransmitJoint.oldEvent id (TransmitJoint.transmit family addr packets mtu)
      (RoutingJoint.access (wgXmitPrefix family addr packets mtu)) :=
  TransmitJoint.transmit_projects family addr packets mtu

/-- The same single observer executes the original native WireGuard call. -/
theorem original_transmit_handoff_erasure (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ErasesStatePrefix (TransmitJoint.transmit family addr packets mtu) (wgXmit family addr packets mtu) :=
  TransmitJoint.transmit_erases family addr packets mtu

/-- Each completed handoff extends the journal even if the later tail stops. -/
theorem original_transmit_handoff_appends (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateAppends (TransmitJoint.transmit family addr packets mtu) :=
  TransmitJoint.transmit_appends family addr packets mtu

/-- A native call retains routing at every recorded handoff's strict prefix;
its normal endpoint permits the source's reference-payment deletion. -/
theorem original_transmit_positional_checks (initial : FlatTable × FlatTable)
    (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StatePrefixPreserves
      (fun h w _ => GlobalCompletionState initial (TransmitJoint.routes h) w ∧ TransmitJoint.Checks initial h)
      (TransmitJoint.Safe initial) (TransmitJoint.transmit family addr packets mtu) :=
  TransmitJoint.transmit_preserves initial family addr packets mtu

/-- Actual product callers use the canonical native lift. -/
theorem original_transmit_product_checks (initial : FlatTable × FlatTable)
    (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    PrefixPreserves (TransmitJoint.Inv initial) (TransmitJoint.Safe initial)
      (liftWGObserver (TransmitJoint.transmit family addr packets mtu)) :=
  TransmitJoint.transmit_product initial family addr packets mtu

/-- The specified occurrence, rather than a later endpoint, supplies this
longest-prefix owner and every supplied packet's destination. -/
theorem checked_transmit_handoff_winner {initial : FlatTable × FlatTable}
    {h : List TransmitJoint.Event} (checked : TransmitJoint.Checks initial h)
    (pre post : List TransmitJoint.Event) (receipt : TransmitJoint.Receipt)
    (position : h = pre ++ .transmit receipt :: post) :
    ∃ (pid : PeerId) (v4 : Bool), receipt.run.value = .ok pid ∧
      receipt.family = (if v4 then 4 else 6) ∧
      TxFrontCut (if v4 then 4 else 6) receipt.addr receipt.packets receipt.mtu receipt.run.before
        receipt.run.after receipt.run.ambientBefore receipt.run.ambientAfter pid ∧
      PeerWinner (rootWidth v4) receipt.addr
        (selectedFlat v4 (completionFold (TransmitJoint.routes pre) initial)) (some pid) ∧
      ∀ pkt ∈ receipt.packets, destinationField (if v4 then 4 else 6) pkt.bytes = receipt.addr :=
  checked.winner pre post receipt position

/-- The direct syscall retains its socket acquisition/payment and route body. -/
theorem original_direct_transmit_source (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    RxHistory.syscallDispatch (.wgXmit family addr payload opts) =
      RxHistory.audit (syscallXmitWith xmitMulticastLoopAudit
        (fun family addr packets mtu => auditFocus (liftWGObserver (wgXmitPrefix family addr packets mtu)))
        family addr payload opts) := rxDispatch_xmit_factor family addr payload opts

/-- Batch items use the original section wrapper and multicast/receive callbacks. -/
theorem original_batch_transmit_source (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    RxHistory.batchItem d cqes item =
      batchItemWith (fun msg src => RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src)))
        RxHistory.pollScheduledInline
        (fun family addr => RxHistory.audit (xmitMulticastLoopAudit family addr))
        (fun family addr packets mtu => RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu)))
        d cqes item := rxBatchItem_factor d cqes item

/-- The actual Stack callback reaches transmission through the original IPv4 reply. -/
theorem original_stack_transmit_source (packet : List UInt8) :
    stackReceivePrefix packet = stackReceiveWith (receive4With (reply4With
      (fun family addr packets mtu => liftWGObserver (wgXmitPrefix family addr packets mtu)))) packet := rfl

/-- The Stack source with the concrete handoff observer preserves all earlier
routing certificates and checks each newly reached reply handoff. -/
theorem original_stack_transmit_checks (initial : FlatTable × FlatTable) (packet : List UInt8) :
    PrefixPreserves (TransmitJoint.Inv initial) (TransmitJoint.Safe initial)
      (stackReceiveWith (receive4With (reply4With
        (fun family addr packets mtu => liftWGObserver (TransmitJoint.transmit family addr packets mtu)))) packet) :=
  TransmitJoint.stack_preserves initial _ (TransmitJoint.transmit_product initial) packet

/-- GRO entry precedes the original Stack callback, and normal completion is
recorded only when that same callback actually returns. -/
theorem original_gro_stack_source (entry : RxJoint.Entry) :
    RxJoint.enter entry = RxJoint.GroSource.enterWith id
      (fun bytes => RxJoint.access (stackReceivePrefix bytes)) entry :=
  RxJoint.GroSource.enter_factor entry

/-- The entire old poll is the shared body with its actual old atoms and GRO
callbacks; this factor changes neither input history nor callback domains. -/
theorem original_poll_transmit_source (pid : PeerId) (budget : Nat) :
    RxJoint.poll pid budget = RxJoint.PollSource.pollWith (fun {_} a => a)
      RxJoint.receive RxJoint.flushAll pid budget := RxJoint.PollSource.poll_factor pid budget

/-- Each actual observed poll starts with its fresh lifetime seed and promotes
only the new suffix, retaining the older global prefix verbatim. -/
theorem original_observed_poll_seed (pid : PeerId) (budget : Nat) :
    RxHistory.observePoll pid budget = RxHistory.ObserveSource.seededWith
      (fun h => RxJoint.seed (RxHistory.prior h)) RxHistory.promote (RxJoint.poll pid budget) :=
  RxHistory.ObserveSource.observePoll_factor pid budget

end TransmitSource


section TransmitClosure
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Packets AllowedIps Configuration
open TransmitJoint

/-- Every transmit event the outgoing observer records on an initialized run of
the trace passes the global completion checks: the outgoing history is safe from
the empty routing state. -/
theorem initialized_transmit_checks (trace : Leanux.Runner.Trace) (shape : TraceAddressShape trace) (placeholders : Bool) :
    Safe ([],[]) (runPrefixOuter (TransmitJoint.Initialized.executeTrace trace placeholders) []).2 :=
  TransmitJoint.Initialized.checks trace shape placeholders

/-- The same as `initialized_transmit_checks` for a trace obtained from a
successfully parsed JSON, which discharges the address-shape premise. -/
theorem parsed_initialized_transmit_checks (json : Lean.Json) (trace : Leanux.Runner.Trace)
    (parsed : Leanux.Runner.parseTrace json = .ok trace) (placeholders : Bool) :
    Safe ([],[]) (runPrefixOuter (TransmitJoint.Initialized.executeTrace trace placeholders) []).2 :=
  TransmitJoint.Initialized.parsed_checks json trace parsed placeholders

/-- The outgoing observer's run projects, through the global receive view, onto
the receive-history execution of the same trace: the observer adds transmit
events and changes nothing the receive history sees. -/
theorem initialized_transmit_rx_projection (trace : Leanux.Runner.Trace) (placeholders : Bool) :
    ProjectsOuter RxTransmit.globalRx id (TransmitJoint.Initialized.executeTrace trace placeholders)
      (RxHistory.executeTraceHistory trace placeholders) :=
  TransmitJoint.Initialized.projects trace placeholders

/-- The outgoing observer erases to the executable mirror: running the observed
trace and running `Runner.executeTrace` are the same computation once the
observer's events are dropped. -/
theorem initialized_transmit_executable (trace : Leanux.Runner.Trace) (placeholders : Bool) :
    ErasesOuter (TransmitJoint.Initialized.executeTrace trace placeholders) (Leanux.Runner.executeTrace trace placeholders) :=
  TransmitJoint.Initialized.erases trace placeholders

/-- Every transmit receipt in the outgoing history is valid and was issued in a
completion state consistent with the routing history before it. -/
theorem initialized_transmit_receipt (trace : Leanux.Runner.Trace) (shape : TraceAddressShape trace) (placeholders : Bool)
    (pre post : List Event) (receipt : Receipt)
    (position : (runPrefixOuter (TransmitJoint.Initialized.executeTrace trace placeholders) []).2 = pre ++ .transmit receipt :: post) :
    receipt.Valid ∧ GlobalCompletionState ([],[]) (routes pre) receipt.run.before :=
  TransmitJoint.Initialized.checked trace shape placeholders pre post receipt position

/-- R3, outgoing, over the typed trace: every completed handoff names a peer,
a family, a front cut of the transmit path, and that peer is the longest-prefix
owner of the routed address in the flat routing history before the handoff;
every supplied packet's destination equals that address. -/
theorem initialized_transmit_authorization (trace : Leanux.Runner.Trace) (shape : TraceAddressShape trace) (placeholders : Bool)
    (pre post : List Event) (receipt : Receipt)
    (position : (runPrefixOuter (TransmitJoint.Initialized.executeTrace trace placeholders) []).2 = pre ++ .transmit receipt :: post) :
    ∃ (pid : PeerId) (v4 : Bool), receipt.run.value = .ok pid ∧
      receipt.family = (if v4 then 4 else 6) ∧
      TxFrontCut (if v4 then 4 else 6) receipt.addr receipt.packets receipt.mtu receipt.run.before
        receipt.run.after receipt.run.ambientBefore receipt.run.ambientAfter pid ∧
      PeerWinner (rootWidth v4) receipt.addr
        (selectedFlat v4 (completionFold (routes pre) ([],[]))) (some pid) ∧
      ∀ pkt ∈ receipt.packets, destinationField (if v4 then 4 else 6) pkt.bytes = receipt.addr :=
  TransmitJoint.Initialized.winner trace shape placeholders pre post receipt position

/-- R3's outgoing headline: `initialized_transmit_authorization` for a trace
obtained from a successfully parsed JSON, which discharges the address-shape
premise, so the claim holds for every trace the runner accepts. -/
theorem parsed_initialized_transmit_authorization (json : Lean.Json) (trace : Leanux.Runner.Trace)
    (parsed : Leanux.Runner.parseTrace json = .ok trace) (placeholders : Bool)
    (pre post : List Event) (receipt : Receipt)
    (position : (runPrefixOuter (TransmitJoint.Initialized.executeTrace trace placeholders) []).2 = pre ++ .transmit receipt :: post) :
    ∃ (pid : PeerId) (v4 : Bool), receipt.run.value = .ok pid ∧
      receipt.family = (if v4 then 4 else 6) ∧
      TxFrontCut (if v4 then 4 else 6) receipt.addr receipt.packets receipt.mtu receipt.run.before
        receipt.run.after receipt.run.ambientBefore receipt.run.ambientAfter pid ∧
      PeerWinner (rootWidth v4) receipt.addr
        (selectedFlat v4 (completionFold (routes pre) ([],[]))) (some pid) ∧
      ∀ pkt ∈ receipt.packets, destinationField (if v4 then 4 else 6) pkt.bytes = receipt.addr :=
  TransmitJoint.Initialized.parsed_winner json trace parsed placeholders pre post receipt position

/-- Every concrete syscall preserves handoff checks through its actual
traffic and return-to-user callbacks. Only configuration shape is an input. -/
theorem original_syscall_transmit_checks (initial : FlatTable × FlatTable) (call : Syscall)
    (shape : SyscallAddressShape call) :
    PrefixPreserves (Inv initial) (Safe initial) (TransmitJoint.Actual.syscall call) :=
  TransmitJoint.Actual.syscall_preserves initial call shape

/-- The complete original RX journal, actual result and Stop are retained. -/
theorem original_syscall_transmit_projection (call : Syscall) :
    ProjectsPrefix RxTransmit.globalRx id (TransmitJoint.Actual.syscall call) (RxHistory.syscall call) :=
  TransmitJoint.Actual.syscall_projects call

/-- The direct syscall checks the original socket/route/multicast body and
records the native completed handoff before its send tail. -/
theorem original_direct_transmit_checks (initial : FlatTable × FlatTable)
    (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves (Inv initial) (Safe initial) (TransmitJoint.direct family addr payload opts) :=
  TransmitJoint.direct_preserves initial family addr payload opts

/-- A poll promotes only its new local suffix and retains the old joint
routing/RX journal at the actual incoming positions. -/
theorem original_observed_transmit_projection (pid : PeerId) (budget : Nat) :
    ProjectsPrefix oldEvent id (RxTransmit.observePoll pid budget)
      (RoutingJoint.rxAction (RxHistory.observePoll pid budget)) :=
  RxTransmit.observePoll_projects pid budget

/-- Poll-local Stack transmissions use their actual outer routing prefix. -/
theorem original_observed_transmit_checks (initial : FlatTable × FlatTable) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Inv initial) (Safe initial) (RxTransmit.observePoll pid budget) :=
  RxTransmit.observePoll_preserves initial pid budget

end TransmitClosure

end Leanux.Proofs.WG.CryptokeyRouting
