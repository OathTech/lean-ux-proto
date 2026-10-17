import Leanux.Proofs.WG.Packets.PublicationIdentity
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
Packet paths remain open. -/
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
pure-tree refinement; general configuration-history composition remains open. -/
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
owner labels are permitted. This does not yet close complete configuration histories. -/
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
theorem original_dump_routing (initial : FlatTable × FlatTable) (fd seq : Nat)
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
identity, initialized publication and later Stack/routing joins remain open. -/
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

end Leanux.Proofs.WG.CryptokeyRouting
