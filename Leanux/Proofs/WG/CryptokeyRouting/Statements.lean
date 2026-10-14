import Leanux.Proofs.WG.AllowedIps.InsertionDispatch
import Leanux.Proofs.WG.AllowedIps.ContextRemoval
import Leanux.Proofs.WG.AllowedIps.RemovalStore
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
derives all structural cases from its total placement traversal. Every normal
return is classified as success or one of two allocation refusals; successful
returns refine pure insertion and actual-root longest-prefix lookup. A supplied
opposite-family representation is preserved. Pure removal implements exact
entry filtering and preserves the structural invariants, with local compaction
laws under compression and distinct IDs. The original removal loop has an
all-input source equation; binary and root-tagged leaf/unary iterations have
total exact endpoints and local store representation facts. General removal,
configuration-history agreement, and packet admission remain separate obligations.
-/

namespace Leanux.Proofs.WG.CryptokeyRouting

open Leanux
open Leanux.Proofs.WG.AllowedIps

/-- For bounded IPv4 or IPv6 addresses, the original `commonBits` returns
their maximal common-prefix length: every bounded CIDR is at most that
length exactly when the corresponding leading address bits agree. The
execution equation includes all of the mirror's branch records. -/
theorem commonBits_correct (n : WG.AipNode) (key width : Nat) (w : World)
    (hw : width = 32 ∨ width = 128) (hn : n.bits < 2 ^ width)
    (hk : key < 2 ^ width) :
    (WG.commonBits n key width).run w =
        .ok (common width n.bits key, commonRecords w width (n.bits ^^^ key)) ∧
      common width n.bits key ≤ width ∧
      ∀ cidr, cidr ≤ width →
        (cidr ≤ common width n.bits key ↔
          prefixBits width cidr n.bits = prefixBits width cidr key) := by
  exact ⟨commonBits_run n key width w hw, common_le _ _ _,
    fun _ hc => common_ge_iff hn hk hc⟩

/-- For bounded IPv4 or IPv6 addresses and a CIDR within the family width,
the original `prefixMatches` returns true exactly when the node and query
have equal leading prefix bits, with exactly its recorded World effects. -/
theorem prefixMatches_correct (n : WG.AipNode) (key width : Nat) (w : World)
    (hw : width = 32 ∨ width = 128) (hn : n.bits < 2 ^ width)
    (hk : key < 2 ^ width) (hc : n.cidr ≤ width) :
    (WG.prefixMatches n key width).run w =
      .ok (decide (prefixBits width n.cidr n.bits = prefixBits width n.cidr key),
        commonRecords w width (n.bits ^^^ key)) :=
  prefixMatches_run n key width w hw hn hk hc

/-- Whenever the node has another address bit to inspect, the original
`choose` returns that next bit, either zero or one, and preserves the World.
This arithmetic statement is uniform in the node's address width. -/
theorem choose_correct (n : WG.AipNode) (key : Nat) (w : World) (hc : n.cidr < n.bitlen) :
    (WG.choose n key).run w =
        .ok (prefixBits n.bitlen (n.cidr + 1) key % 2, w) ∧
      prefixBits n.bitlen (n.cidr + 1) key % 2 < 2 := by
  constructor
  · simpa only [bit_eq_prefix_succ] using choose_run n key w hc
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
ID, or none when no owned prefix matches, and preserves the whole Kernel.
The representation premise describes the actual node map and backlinks;
establishing it from configuration mutations remains a separate obligation. -/
theorem original_findNode_lookup_correct (w : World) (d : WG.Device)
    (width key : Nat) (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (hd : w.k.wg = some d) (t : Tree) (parent : WG.Slot)
    (hr : RepAt d.nodes width parent t) (hv : t.Valid width) :
    ∃ w', (WG.findNode t.root width key).run w =
        .ok ((t.lookup width key).map Entry.id, w') ∧
      Winner width key t.entries (t.lookup width key) ∧ w'.k = w.k := by
  obtain ⟨w', he, hframe⟩ := findNode_run w d width key hw hk hd t parent hr hv
  exact ⟨w', he, Tree.lookup_spec hv key, hframe⟩

/-- Any successful execution of the original traversal on an exactly
represented valid IPv4 or IPv6 tree returns its longest matching owned
prefix's node ID, or none when no owned prefix matches. This theorem assumes
the structural representation at entry; it does not establish that mutations
produce it. It is the successful-run corollary of the total result above. -/
theorem original_findNode_successful_lookup_correct (w w' : World) (d : WG.Device)
    (width key : Nat) (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (hd : w.k.wg = some d) (t : Tree) (parent : WG.Slot)
    (hr : RepAt d.nodes width parent t) (hv : t.Valid width) (result : Option Nat)
    (hreturn : (WG.findNode t.root width key).run w = .ok (result, w')) :
    result = (t.lookup width key).map Entry.id ∧
      Winner width key t.entries (t.lookup width key) ∧ w'.k = w.k := by
  have h := findNode_refines w w' d width key hw hk hd t parent hr hv result hreturn
  exact ⟨h.1, Tree.lookup_spec hv key, h.2⟩

/-- Pure Patricia insertion replaces the owner of exactly the requested
canonical prefix, retaining unmasked addresses and old node identifiers on
overwrite. Lookup afterward chooses the longest match in that updated flat
binding list. This is a theorem about the intermediate recursive algorithm;
general refinement of original `add` and its allocation failures remains open. -/
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
without changing the Kernel or installs precisely the pure insertion's tree.
Whole-store freshness protects every represented node of the opposite family;
the target peer must exist. This classifies normal executions, without
asserting that missing or malformed allocation records complete normally. -/
theorem original_add_empty_root_correct (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d v4 = none)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hb : NodesBelow d) (other : Tree)
    (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (result : Int)
    (hr : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (result, w')) :
    let installed := emptyInstalled d v4 addr cidr pid p
    let tree := (Tree.empty.insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (result = -ENOMEM ∧ w'.k = w.k) ∨
      (result = 0 ∧ w'.k = { w.k with wg := some installed } ∧
        NodesBelow installed ∧ rootValue installed v4 = tree.root ∧
        RepAt installed.nodes (rootWidth v4) (rootSlot v4) tree ∧ tree.Valid (rootWidth v4) ∧
        rootValue installed (!v4) = rootValue d (!v4) ∧
        RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) := by
  apply case_add_empty_root_correct <;> assumption

/-- The original `insert` increments the table sequence on both normal
outcomes. Success into an empty selected root agrees with pure insertion;
allocation refusal preserves the device apart from that sequence increment.
The whole Kernel equation frames unrelated state. The opposite root's value
and any supplied opposite-family representation survive either outcome.
An existing caller linkage between them is preserved, not established here.
As in the original wrapper,
family 4 selects IPv4 and every other value selects IPv6. General insertion
history, owner liveness, and packet admission are not asserted here. -/
theorem original_insert_empty_root_correct (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (family addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d (family == 4) = none)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hb : NodesBelow d) (other : Tree)
    (ho : RepAt d.nodes (rootWidth (!(family == 4))) (rootSlot (!(family == 4))) other)
    (result : Int) (hr : (WG.insert family addr cidr pid).run w = .ok (result, w')) :
    let v4 := family == 4
    let tree := (Tree.empty.insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    ∃ d', w'.k = { w.k with wg := some d' } ∧
      d'.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧ NodesBelow d' ∧
      rootValue d' (!v4) = rootValue d (!v4) ∧
      RepAt d'.nodes (rootWidth (!v4)) (rootSlot (!v4)) other ∧
      ((result = -ENOMEM ∧ d' = bumpSeq d) ∨
        (result = 0 ∧ d' = emptyInstalled (bumpSeq d) v4 addr cidr pid p ∧
          rootValue d' v4 = tree.root ∧ RepAt d'.nodes (rootWidth v4) (rootSlot v4) tree ∧
          tree.Valid (rootWidth v4))) := by
  rcases insert_empty_exact w w' d hd family addr cidr pid p hp he hc result hr with hf | hs
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
theorem original_nodePlacement_correct (w : World) (d : WG.Device) (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (hd : w.k.wg = some d) (t : Tree) (base : WG.Slot)
    (hr : RepAt d.nodes width base t) (hv : t.Valid width) :
    ∃ result w', (WG.nodePlacement t.root key cidr width).run w = .ok (result, w') ∧
      w'.k = w.k ∧ PlacementWitness t width key cidr result ∧
      ∀ fresh peer, result.2 = true ↔
        (t.insertFresh width fresh key cidr peer).allocations = 0 := by
  obtain ⟨result, w', he, hf, hp⟩ := nodePlacement_run w d width key cidr hw hk hc hd t base hr hv
  exact ⟨result, w', he, hf, hp, hp.allocations⟩

/-- A nonexact original placement identifies a structurally graftable focus.
Pure insertion of any fresh node identifiers at that focus, rebuilt through
the context, is exactly the existing recursive `insertFresh` result. This
links the original traversal to the pure mutation's stopped case without
assuming an insertion-history or peer-list invariant. -/
theorem original_nodePlacement_stopped (w w' : World) (d : WG.Device) (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (hd : w.k.wg = some d) (t : Tree) (base : WG.Slot)
    (hr : RepAt d.nodes width base t) (hv : t.Valid width) (parent : Option Nat)
    (hreturn : (WG.nodePlacement t.root key cidr width).run w = .ok ((parent, false), w')) :
    w'.k = w.k ∧ ∃ (c : Context) (u : Tree), t = c.plug u ∧ c.Follows width key cidr ∧
      parent = c.lastParent none ∧ Graftable width key cidr u ∧
      ∀ fresh peer, t.insertFresh width fresh key cidr peer =
        let localResult := graft width fresh key cidr peer u
        { localResult with tree := c.plug localResult.tree } := by
  obtain ⟨hf, hp⟩ := nodePlacement_refines w w' d width key cidr hw hk hc hd t base hr hv
    (parent, false) hreturn
  exact ⟨hf, hp.stopped rfl hv hk⟩

/-- If the requested path ends at a known empty focus, the original placement
loop completes with precisely its enclosing parent and a false exact flag.
This traversal fact supplies the missing-child case for future mutation
refinement; it does not assert that the subsequent allocation completes. -/
theorem original_nodePlacement_empty_focus (w : World) (d : WG.Device) (width key cidr : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width) (hc : cidr ≤ width)
    (hd : w.k.wg = some d) (c : Context) (base : WG.Slot)
    (hr : RepAt d.nodes width base (c.plug .empty))
    (hv : (c.plug .empty).Valid width) (hf : c.Follows width key cidr) :
    ∃ w', (WG.nodePlacement (c.plug .empty).root key cidr width).run w =
      .ok ((c.lastParent none, false), w') ∧ w'.k = w.k := by
  obtain ⟨result, w', he, hp⟩ :=
    (Leanux.Proofs.Framing.total_iff_run _ _ _).mp
      (nodePlacement_empty_focus_wp w.k d width key cidr hw hk hc hd c base hr hv hf) w rfl
  rcases hp with ⟨rfl, hframe⟩
  exact ⟨w', he, hframe⟩

/-- On a represented root whose requested immediate child is empty, original
`add` either refuses allocation without a Kernel change or installs exactly
the existing pure insertion result. The exact installed state includes
the new backlink, parent slot update, and peer-list append. Whole-store freshness and explicit
parent/sibling separation support the representation; no peer-list coherence
or general insertion-history premise is assumed or concluded. Both root
values and the sequence counter are preserved, as is any supplied
opposite-family representation. Record errors remain errors. -/
theorem original_add_empty_child_correct (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : side < 2) (hbelow : NodesBelow d)
    (hparent : n.id ∉ sibling.nodeIds)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (Tree.fork n side .empty sibling))
    (hv : (Tree.fork n side .empty sibling).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4) (hlt : n.cidr < cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (hbit : bit (rootWidth v4) n.cidr addr = side)
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (result : Int)
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (result, w')) :
    let installed := gapInstalled d v4 n side sibling addr cidr pid p
    let inserted := (Tree.fork n side .empty sibling).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    (result = -ENOMEM ∧ w'.k = w.k) ∨
      (result = 0 ∧ w'.k = { w.k with wg := some installed } ∧ NodesBelow installed ∧
        rootValue installed v4 = inserted.tree.root ∧
        RepAt installed.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
        inserted.tree.Valid (rootWidth v4) ∧ installed.nextNode = d.nextNode + 1 ∧
        installed.peerAllowedips.seq = d.peerAllowedips.seq ∧
        (∀ family, rootValue installed family = rootValue d family) ∧
        RepAt installed.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) := by
  have outcome := (Leanux.Proofs.Framing.hoare_iff_triple _ _ _).mpr
    (add_root_gap_wp w.k d hd v4 n side sibling addr cidr pid p hp hroot hb hbelow hr hv ha hc hlt hm hbit)
    w result w' rfl hreturn
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
theorem original_add_empty_child_lookup (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : side < 2) (hbelow : NodesBelow d)
    (hparent : n.id ∉ sibling.nodeIds)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (Tree.fork n side .empty sibling))
    (hv : (Tree.fork n side .empty sibling).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4) (hlt : n.cidr < cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (hbit : bit (rootWidth v4) n.cidr addr = side) (key : Nat) (hk : key < 2 ^ rootWidth v4)
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w')) :
    let old := Tree.fork n side .empty sibling
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ d' final, w'.k.wg = some d' ∧
      (WG.findNode (rootValue d' v4) (rootWidth v4) key).run w' =
        .ok ((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: old.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final.k = w'.k := by
  have outcome := original_add_empty_child_correct w w' d hd v4 n side sibling addr cidr pid p
    hp hroot hb hbelow hparent hr hv ha hc hlt hm hbit .empty trivial 0 hreturn
  rcases outcome with hf | hs
  · simp [ENOMEM] at hf
  obtain ⟨_, hkernel, _, hroot', hrep, hvalid, _⟩ := hs
  have hdev : w'.k.wg = some (gapInstalled d v4 n side sibling addr cidr pid p) := by
    rw [hkernel]
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨final, he, hframe⟩ := findNode_run w'
    (gapInstalled d v4 n side sibling addr cidr pid p) (rootWidth v4) key hw hk hdev
    ((Tree.fork n side .empty sibling).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (rootSlot v4) hrep hvalid
  refine ⟨_, final, hdev, ?_, Tree.insertFresh_lookup_spec hv ha hc d.nextNode pid key, hframe⟩
  simpa only [hroot', Tree.lookupId] using he

/-- Original `add` into an empty child at any represented depth either
refuses allocation without a Kernel change or installs the existing pure
insertion result. The actual selected root, structural representation, local
validity and duplicate-free node identifiers are retained. Premises explicitly
supply the requested path, initial root linkage and whole-store freshness.
Both root values, the sequence, and any supplied opposite-family representation
are framed. Other insertion cases, ownership coherence and history remain open. -/
theorem original_add_context_empty_child_correct (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (c : Context) (n : NodeData) (side : Nat) (sibling : Tree)
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
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (result, w')) :
    let installed := gapInstalledAt d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p
    let inserted := (c.plug (Tree.fork n side .empty sibling)).insertFresh
      (rootWidth v4) d.nextNode addr cidr pid
    (result = -ENOMEM ∧ w'.k = w.k) ∨
      (result = 0 ∧ w'.k = { w.k with wg := some installed } ∧ NodesBelow installed ∧
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
theorem original_add_context_empty_child_lookup (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (c : Context) (n : NodeData) (side : Nat) (sibling : Tree)
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
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w')) :
    let old := c.plug (Tree.fork n side .empty sibling)
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ d' final, w'.k.wg = some d' ∧
      (WG.findNode (rootValue d' v4) (rootWidth v4) key).run w' =
        .ok ((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: old.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final.k = w'.k := by
  have outcome := original_add_context_empty_child_correct w w' d hd v4 c n side sibling addr cidr pid p
    hp hroot hb hbelow hnodup hr hv ha hc hf hlt hm hbit .empty trivial 0 hreturn
  rcases outcome with hfail | hs
  · simp [ENOMEM] at hfail
  obtain ⟨_, hkernel, _, hroot', hrep, hvalid, _⟩ := hs
  have hdev : w'.k.wg = some (gapInstalledAt d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p) := by
    rw [hkernel]
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨final, he, hframe⟩ := findNode_run w'
    (gapInstalledAt d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p) (rootWidth v4) key hw hk hdev
    ((c.plug (Tree.fork n side .empty sibling)).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (rootSlot v4) hrep hvalid
  refine ⟨_, final, hdev, ?_, Tree.insertFresh_lookup_spec hv ha hc d.nextNode pid key, hframe⟩
  simpa only [hroot', Tree.lookupId] using he

/-- The original configuration insertion wrapper for an empty child at any
represented depth increments the sequence once on either normal outcome.
Success retains the actual root linkage, pure insertion representation, local
validity and duplicate-free node identifiers; refusal leaves only the sequence
increment. Both root values and a supplied opposite-family representation are
preserved. This does not claim coverage of other insertion cases or histories. -/
theorem original_insert_context_empty_child_correct (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (family : Nat) (c : Context) (n : NodeData) (side : Nat) (sibling : Tree)
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
    (result : Int) (hreturn : (WG.insert family addr cidr pid).run w = .ok (result, w')) :
    let v4 := family == 4
    let inserted := (c.plug (Tree.fork n side .empty sibling)).insertFresh
      (rootWidth v4) d.nextNode addr cidr pid
    ∃ d', w'.k = { w.k with wg := some d' } ∧ d'.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧
      NodesBelow d' ∧ (∀ f, rootValue d' f = rootValue d f) ∧
      RepAt d'.nodes (rootWidth (!v4)) (rootSlot (!v4)) other ∧
      ((result = -ENOMEM ∧ d' = bumpSeq d) ∨
        (result = 0 ∧ d' = gapInstalledAt (bumpSeq d) v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p ∧
          rootValue d' v4 = inserted.tree.root ∧
          RepAt d'.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
          inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧ d'.nextNode = d.nextNode + 1)) := by
  rw [insert_run_bump w d hd family addr cidr pid] at hreturn
  have outcome := original_add_context_empty_child_correct
    { w with k := { w.k with wg := some (bumpSeq d) } } w' (bumpSeq d) rfl (family == 4)
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
theorem original_listDel_correct (w : World) (d : WG.Device) (hd : w.k.wg = some d) (id : Nat) :
    ∃ w', (WG.listDel id).run w = .ok ((), w') ∧
      w'.k = { w.k with wg := some (unlisted d id) } ∧
      (∀ pid : Nat, (unlisted d id).peers[pid]? = (d.peers[pid]?).map (unlist id)) ∧
      (∀ pid : Nat, ((unlisted d id).peers[pid]?).map WG.Peer.internalId =
        (d.peers[pid]?).map WG.Peer.internalId) ∧
      (unlisted d id).nextPeer = d.nextPeer ∧ (unlisted d id).nextNode = d.nextNode ∧
      (unlisted d id).nextKeypairId = d.nextKeypairId ∧ (unlisted d id).nextSkb = d.nextSkb := by
  obtain ⟨result, w', hr, _, hk⟩ := (Leanux.Proofs.Framing.total_iff_run _ _ _).mp
    (listDel_wp w.k d hd id) w rfl
  exact ⟨w', hr, hk, unlisted_get d id, unlisted_identity d id, rfl, rfl, rfl, rfl⟩

/-- Original exact-prefix insertion terminates at any represented depth and
refines the same pure insertion used for lookup correctness. It preserves the
old node's identifier, unmasked address and structural fields, filters every
peer list, and appends the ID once to the filtered target list. Previous
ownership and coherent peer lists are not prerequisites. Root linkage,
duplicate-free represented IDs and local validity are explicit premises;
configuration histories and packet admission are separate obligations. -/
theorem original_add_context_exact_correct (w : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (c : Context) (n : NodeData) (l r : Tree)
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
    ∃ w', (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w') ∧
      w'.k = { w.k with wg := some installed } ∧
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
theorem original_add_context_exact_lookup (w : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (c : Context) (n : NodeData) (l r : Tree)
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
    ∃ w' d' final,
      (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w') ∧
      w'.k.wg = some d' ∧
      (WG.findNode (rootValue d' v4) (rootWidth v4) key).run w' =
        .ok ((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: old.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final.k = w'.k := by
  obtain ⟨w', hrun, hkernel, hroot', hrep, hvalid, _⟩ :=
    original_add_context_exact_correct w d hd v4 c n l r addr cidr pid p hp hroot hr hv hnodup
      ha hc hf hn hm .empty trivial
  let installed := exactInstalled d n.id (encode (rootWidth v4) (c.slot (rootSlot v4)) n l r) pid p
  have hdev : w'.k.wg = some installed := by rw [hkernel]
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨final, he, hframe⟩ := findNode_run w' installed (rootWidth v4) key hw hk hdev
    ((c.plug (.node n l r)).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (rootSlot v4) hrep hvalid
  refine ⟨w', installed, final, hrun, hdev, ?_, Tree.insertFresh_lookup_spec hv ha hc d.nextNode pid key, hframe⟩
  change rootValue installed v4 = _ at hroot'
  rw [hroot']
  simpa only [Tree.lookupId] using he

/-- The original family wrapper increments the sequence exactly once, then
completes the exact-prefix update without allocating a node. The endpoint is
the same owner replacement and peer-list movement used by the add theorem. -/
theorem original_insert_context_exact_correct (w : World) (d : WG.Device)
    (hd : w.k.wg = some d) (family : Nat) (c : Context) (n : NodeData) (l r : Tree)
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
    ∃ w', (WG.insert family addr cidr pid).run w = .ok (0, w') ∧
      w'.k = { w.k with wg := some installed } ∧
      installed.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧ installed.nextNode = d.nextNode ∧
      rootValue installed v4 = inserted.tree.root ∧
      RepAt installed.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup := by
  obtain ⟨w', hrun, hkernel, hroot', hrep, hvalid, _, hnodup', _⟩ :=
    original_add_context_exact_correct { w with k := { w.k with wg := some (bumpSeq d) } }
      (bumpSeq d) rfl (family == 4) c n l r addr cidr pid p hp hroot hr hv hnodup ha hc hf hn hm .empty trivial
  refine ⟨w', ?_, hkernel, rfl, rfl, hroot', hrep, hvalid, hnodup'⟩
  rw [insert_run_bump w d hd family addr cidr pid]
  exact hrun

/-- Every normal return of original add at a nonempty selected root is one of:
first allocation refusal, second allocation refusal with source rollback, or
installation of the source-shaped one-node or two-node graft. The represented
input and actual root link justify traversal; the separate success theorem proves
that either successful endpoint represents the pure inserted tree. A missing or
rejected choice record may Stop and is not a normal allocation refusal. -/
theorem original_add_root_graft_endpoints (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hv : (Tree.node n l r).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr =
      prefixBits (rootWidth v4) n.cidr addr)) (result : Int)
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (result, w')) :
    (result = -ENOMEM ∧ w'.k = w.k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) n.addr addr) ≠ cidr ∧
        w'.k = { w.k with wg := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w'.k = { w.k with wg := some (graftInstalled d v4 n.id
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
theorem original_insert_root_graft_endpoints (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (family : Nat) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d (family == 4) = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) (.node n l r))
    (hv : (Tree.node n l r).Valid (rootWidth (family == 4)))
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth (family == 4)) n.cidr n.addr =
      prefixBits (rootWidth (family == 4)) n.cidr addr)) (result : Int)
    (hreturn : (WG.insert family addr cidr pid).run w = .ok (result, w')) :
    let v4 := family == 4
    ∃ d', w'.k = { w.k with wg := some d' } ∧ d'.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧
      ((result = -ENOMEM ∧ d' = bumpSeq d) ∨
        (result = -ENOMEM ∧ min cidr (common (rootWidth v4) n.addr addr) ≠ cidr ∧
          d' = graftRolledBack (bumpSeq d) (rootWidth v4) addr cidr pid p) ∨
        (result = 0 ∧ d' = graftInstalled (bumpSeq d) v4 n.id
          (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p)) := by
  rw [insert_run_bump w d hd family addr cidr pid] at hreturn
  have outcome := original_add_root_graft_endpoints
    { w with k := { w.k with wg := some (bumpSeq d) } } w' (bumpSeq d) rfl
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
theorem original_add_root_graft_correct (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup)
    (hv : (Tree.node n l r).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr =
      prefixBits (rootWidth v4) n.cidr addr))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other)
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w')) :
    let inserted := (Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    let installed := graftInstalled d v4 n.id (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p
    w'.k = { w.k with wg := some installed } ∧ NodesBelow installed ∧
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
theorem original_add_root_graft_lookup (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup)
    (hv : (Tree.node n l r).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr =
      prefixBits (rootWidth v4) n.cidr addr)) (key : Nat) (hk : key < 2 ^ rootWidth v4)
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w')) :
    let old := Tree.node n l r
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ d' final, w'.k.wg = some d' ∧
      (WG.findNode (rootValue d' v4) (rootWidth v4) key).run w' =
        .ok ((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: old.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final.k = w'.k := by
  obtain ⟨hkernel, _, hroot', hrep, hvalid, _⟩ := original_add_root_graft_correct
    w w' d hd v4 n l r addr cidr pid p hp hroot hb hr hn hv ha hc hstop .empty trivial hreturn
  have hdev : w'.k.wg = some (graftInstalled d v4 n.id
      (encode (rootWidth v4) (rootSlot v4) n l r) addr cidr pid p) := by rw [hkernel]
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨final, he, hframe⟩ := findNode_run w' _ (rootWidth v4) key hw hk hdev
    ((Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (rootSlot v4) hrep hvalid
  refine ⟨_, final, hdev, ?_, Tree.insertFresh_lookup_spec hv ha hc d.nextNode pid key, hframe⟩
  simpa only [hroot', Tree.lookupId] using he

/-- A successful original configuration insert that grafts before the nonempty
selected root increments the sequence once, implements pure insertion with its
exact allocation count, and preserves a supplied opposite-family representation.
The premise is an actual successful original run. Both normal allocation refusals
are classified separately by the endpoint theorem. Rejected or missing records
may Stop and are outside these normal-return contracts. -/
theorem original_insert_root_graft_correct (w w' : World) (d : WG.Device)
    (hd : w.k.wg = some d) (family : Nat) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d (family == 4) = some n.id) (hb : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup)
    (hv : (Tree.node n l r).Valid (rootWidth (family == 4)))
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth (family == 4)) n.cidr n.addr =
      prefixBits (rootWidth (family == 4)) n.cidr addr))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!(family == 4))) (rootSlot (!(family == 4))) other)
    (hreturn : (WG.insert family addr cidr pid).run w = .ok (0, w')) :
    let v4 := family == 4
    let inserted := (Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ d', w'.k = { w.k with wg := some d' } ∧
      d'.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧ NodesBelow d' ∧
      rootValue d' v4 = inserted.tree.root ∧
      RepAt d'.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧
      ((Tree.node n l r).Compressed → inserted.tree.Compressed) ∧
      d'.nextNode = d.nextNode + inserted.allocations ∧
      rootValue d' (!v4) = rootValue d (!v4) ∧
      RepAt d'.nodes (rootWidth (!v4)) (rootSlot (!v4)) other := by
  rw [insert_run_bump w d hd family addr cidr pid] at hreturn
  obtain ⟨hk, hb', hroot', hr', hv', hn', hcomp, hnext, hotherRoot, hseq, hother⟩ :=
    original_add_root_graft_correct
      { w with k := { w.k with wg := some (bumpSeq d) } } w' (bumpSeq d) rfl
      (family == 4) n l r addr cidr pid p hp hroot hb hr hn hv ha hc hstop other ho hreturn
  exact ⟨_, hk, hseq, hb', hroot', hr', hv', hn', hcomp, hnext, hotherRoot, hother⟩

/-- Every normal return of original add whose placement stops at a nonempty
child below an arbitrary represented path has the exact source endpoint: first
allocation refusal, second refusal with frontier advance and all-peer filtering,
or the installed child graft. Missing/rejected records can Stop and are outside
this normal-return classification. Existing node owners need not be resident;
the requested target peer is resident, and no peer-list coherence is assumed. -/
theorem original_add_context_graft_endpoints (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
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
    (ret : Int) (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (ret, w')) :
    (ret = -ENOMEM ∧ w'.k = w.k) ∨
      (ret = -ENOMEM ∧ min cidr (common (rootWidth v4) n.addr addr) ≠ cidr ∧
        w'.k = { w.k with wg := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (ret = 0 ∧ w'.k = { w.k with wg := some (contextGraftInstalled d v4
        (c.slot (rootSlot v4)) parent side sibling n l r addr cidr pid p) }) := by
  apply case_add_context_graft_endpoints <;> assumption

/-- A successful original nonempty child graft at arbitrary depth implements
the existing pure insertion, with exact allocation count, both root values,
whole-store freshness and a supplied opposite-family representation preserved.
Validity and distinct node identifiers are structural input premises; orphan
owner labels are permitted. This does not yet close complete configuration histories. -/
theorem original_add_context_graft_correct (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
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
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w')) :
    let old := c.plug (Tree.fork parent side (.node n l r) sibling)
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    let installed := contextGraftInstalled d v4 (c.slot (rootSlot v4)) parent side sibling n l r addr cidr pid p
    w'.k = { w.k with wg := some installed } ∧ NodesBelow installed ∧
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
theorem original_add_context_graft_lookup (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
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
    (hreturn : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (0, w')) :
    let old := c.plug (Tree.fork parent side (.node n l r) sibling)
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ d' final, w'.k.wg = some d' ∧
      (WG.findNode (rootValue d' v4) (rootWidth v4) key).run w' =
        .ok ((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: old.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final.k = w'.k := by
  obtain ⟨hkernel, _, hroot', hrep, hvalid, _⟩ := original_add_context_graft_correct
    w w' d hd v4 c parent side sibling n l r addr cidr pid p hp hroot hb hbelow hr hv hn ha hc hf hlt hm hbit hstop .empty trivial hreturn
  have hdev : w'.k.wg = some (contextGraftInstalled d v4
      (c.slot (rootSlot v4)) parent side sibling n l r addr cidr pid p) := by rw [hkernel]
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  obtain ⟨final, he, hframe⟩ := findNode_run w' _ (rootWidth v4) key hw hk hdev
    ((c.plug (Tree.fork parent side (.node n l r) sibling)).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree
    (rootSlot v4) hrep hvalid
  refine ⟨_, final, hdev, ?_, Tree.insertFresh_lookup_spec hv ha hc d.nextNode pid key, hframe⟩
  simpa only [hroot', Tree.lookupId] using he

/-- Original insert below an arbitrary represented path has the same successful
graft refinement and advances the allowed-IP sequence once. The run premise is
original normal success; records that Stop are not classified as allocation refusals. -/
theorem original_insert_context_graft_correct (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
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
    (hreturn : (WG.insert family addr cidr pid).run w = .ok (0, w')) :
    let v4 := family == 4
    let old := c.plug (Tree.fork parent side (.node n l r) sibling)
    let inserted := old.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ d', w'.k = { w.k with wg := some d' } ∧
      d'.peerAllowedips.seq = d.peerAllowedips.seq + 1 ∧ NodesBelow d' ∧
      rootValue d' v4 = inserted.tree.root ∧
      RepAt d'.nodes (rootWidth v4) (rootSlot v4) inserted.tree ∧
      inserted.tree.Valid (rootWidth v4) ∧ inserted.tree.nodeIds.Nodup ∧
      (old.Compressed → inserted.tree.Compressed) ∧
      d'.nextNode = d.nextNode + inserted.allocations ∧
      rootValue d' (!v4) = rootValue d (!v4) ∧
      RepAt d'.nodes (rootWidth (!v4)) (rootSlot (!v4)) other := by
  rw [insert_run_bump w d hd family addr cidr pid] at hreturn
  obtain ⟨hk, hb', hroot', hr', hv', hn', hcomp, hnext, hotherRoot, hseq, hother⟩ :=
    original_add_context_graft_correct
      { w with k := { w.k with wg := some (bumpSeq d) } } w' (bumpSeq d) rfl
      (family == 4) c parent side sibling n l r addr cidr pid p hp hroot hb hbelow hr hv hn ha hc hf hlt hm hbit hstop other ho hreturn
  exact ⟨_, hk, hseq, hb', hroot', hr', hv', hn', hcomp, hnext, hotherRoot, hother⟩

/-- Every normal original add return on a represented IPv4/IPv6 tree is
classified without caller-supplied placement/path premises. First refusal leaves
the Kernel unchanged; second refusal retains the exact rollback device, one
consumed node identifier and peer-list filtering. Success supplies the common
structural pure-insertion consequences in Inserted, not a unified exact Device
update. Old owner labels may be orphaned; the requested target peer is resident.
Missing/rejected records may Stop and are outside this normal-return claim. -/
theorem original_add_all_cases (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (t other : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d v4 = t.root)
    (hbelow : NodesBelow d) (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (hv : t.Valid (rootWidth v4)) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) (ret : Int)
    (hrun : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (ret, w')) :
    AddOutcome w.k w'.k d v4 t other addr cidr pid p ret := by
  apply add_outcome <;> assumption

/-- Either normal allocator refusal preserves every node lookup and both
root values. Its frontier/peer-map effects are exactly unchanged values or one
consumed identifier with all-peer filtering of that identifier. No peer-list
freshness, structural TreeMap equality, or full-World rollback is asserted. -/
theorem original_add_allocation_refusal (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (t : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d v4 = t.root)
    (hbelow : NodesBelow d) (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (hv : t.Valid (rootWidth v4)) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hrun : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (-ENOMEM, w')) :
    ∃ out, w'.k = { w.k with wg := some out } ∧ NodesBelow out ∧
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
theorem original_insert_all_cases (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (family : Nat) (t other : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d (family == 4) = t.root)
    (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) t)
    (hv : t.Valid (rootWidth (family == 4))) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (ho : RepAt d.nodes (rootWidth (!(family == 4))) (rootSlot (!(family == 4))) other)
    (ret : Int) (hrun : (WG.insert family addr cidr pid).run w = .ok (ret, w')) :
    AddOutcome { w.k with wg := some (bumpSeq d) } w'.k (bumpSeq d) (family == 4)
      t other addr cidr pid p ret := by
  apply insert_outcome <;> assumption

/-- Any actual original insert return of zero represents the one existing
pure insertion algorithm, with exact allocation count, sequence increment,
validity, distinct node identifiers and conditional compression. The actual
selected root is linked to that tree; the opposite root value and any supplied
opposite-family RepAt are preserved. The latter relation does not itself assert
that the supplied tree was linked to the opposite root. No configuration-history,
peer-list coherence, old-owner residency or packet-path premise is inferred. -/
theorem original_insert_success (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (family : Nat) (t other : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d (family == 4) = t.root)
    (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) t)
    (hv : t.Valid (rootWidth (family == 4))) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (ho : RepAt d.nodes (rootWidth (!(family == 4))) (rootSlot (!(family == 4))) other)
    (hrun : (WG.insert family addr cidr pid).run w = .ok (0, w')) :
    let inserted := t.insertFresh (rootWidth (family == 4)) d.nextNode addr cidr pid
    ∃ out, w'.k = { w.k with wg := some out } ∧
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
theorem original_insert_longest_prefix (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (family : Nat) (t : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hroot : rootValue d (family == 4) = t.root)
    (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth (family == 4)) (rootSlot (family == 4)) t)
    (hv : t.Valid (rootWidth (family == 4))) (hn : t.nodeIds.Nodup)
    (ha : addr < 2 ^ rootWidth (family == 4)) (hc : cidr ≤ rootWidth (family == 4))
    (key : Nat) (hk : key < 2 ^ rootWidth (family == 4))
    (hrun : (WG.insert family addr cidr pid).run w = .ok (0, w')) :
    let v4 := family == 4
    let inserted := t.insertFresh (rootWidth v4) d.nextNode addr cidr pid
    ∃ out final, w'.k.wg = some out ∧
      (WG.findNode (rootValue out v4) (rootWidth v4) key).run w' =
        .ok ((inserted.tree.lookup (rootWidth v4) key).map Entry.id, final) ∧
      Winner (rootWidth v4) key
        (inserted.binding :: t.entries.filter
          (fun e => e.prefixKey (rootWidth v4) != (cidr, prefixBits (rootWidth v4) cidr addr)))
        (inserted.tree.lookup (rootWidth v4) key) ∧ final.k = w'.k := by
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
theorem original_removal_binary_step (w : World) (d : WG.Device)
    (hd : w.k.wg = some d) (id left right : Nat) (n : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hbits : n.bit = #[some left, some right]) :
    ∃ w', (removeStep id).run w = .ok (.yield (), w') ∧
      w'.k = { w.k with wg := some (removalCleared (unlisted d id) id n) } := by
  obtain ⟨result, w', he, hx, hk⟩ := (Leanux.Proofs.Framing.total_iff_run _ _ _).mp
    (removeStep_binary_wp w.k d hd id left right n hn hbits) w rfl
  subst result
  exact ⟨w', he, hk⟩

/-- A leaf whose saved parent tag selects a device root terminates with that
root cleared and the target freed. The input root need not point at the target;
this raw endpoint is not a whole-tree selection or configuration-history claim. -/
theorem original_removal_root_leaf_step (w : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 : Bool) (id : Nat) (n : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hbits : n.bit = #[none, none])
    (hparent : n.parent = rootSlot v4) :
    ∃ w', (removeStep id).run w = .ok (.yield (), w') ∧
      w'.k = { w.k with wg := some (removalRootLeaf (unlisted d id) v4 id n) } := by
  obtain ⟨result, w', he, hx, hk⟩ := (Leanux.Proofs.Framing.total_iff_run _ _ _).mp
    (removeStep_root_leaf_wp w.k d hd v4 id n hn hbits hparent) w rfl
  subst result
  exact ⟨w', he, hk⟩

/-- A root-tagged unary target terminates when its distinct child is resident.
The exact endpoint promotes that child and changes only its backlink. Owners
remain raw labels, including any orphan labels. -/
theorem original_removal_root_unary_step (w : World) (d : WG.Device)
    (hd : w.k.wg = some d) (v4 left : Bool) (id child : Nat) (n cn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hc : d.nodes[child]? = some cn) (hne : id ≠ child)
    (hbits : n.bit = if left then #[some child, none] else #[none, some child])
    (hparent : n.parent = rootSlot v4) :
    ∃ w', (removeStep id).run w = .ok (.yield (), w') ∧
      w'.k = { w.k with wg := some (removalRootUnary (unlisted d id) v4 id n child cn) } := by
  obtain ⟨result, w', he, hx, hk⟩ := (Leanux.Proofs.Framing.total_iff_run _ _ _).mp
    (removeStep_root_unary_wp w.k d hd v4 left id child n cn hn hc hne hbits hparent) w rfl
  subst result
  exact ⟨w', he, hk⟩

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

end Leanux.Proofs.WG.CryptokeyRouting
