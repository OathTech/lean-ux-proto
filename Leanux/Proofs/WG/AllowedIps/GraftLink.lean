import Leanux.Proofs.WG.AllowedIps.GraftSuccess
import Leanux.Proofs.WG.AllowedIps.DeepChildStore

/-! The final parent edge of a nonempty graft. Endpoint expressions retain
original node-write order; contexts are structural evidence only. -/
set_option maxHeartbeats 1000000
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

def forkNode (width : Nat) (base : WG.Slot) (n : NodeData)
    (side : Nat) (chosen sibling : Tree) : WG.AipNode :=
  if side = 0 then encode width base n chosen sibling else encode width base n sibling chosen

@[simp] theorem forkNode_cidr : (forkNode width base n side chosen sibling).cidr = n.cidr := by
  unfold forkNode; split <;> rfl
@[simp] theorem forkNode_bitlen : (forkNode width base n side chosen sibling).bitlen = width := by
  unfold forkNode; split <;> rfl

theorem fork_rep_parts (hb : side < 2)
    (hr : RepAt nodes width base (Tree.fork n side chosen sibling)) :
    nodes[n.id]? = some (forkNode width base n side chosen sibling) ∧
      RepAt nodes width (.child n.id side) chosen ∧
      RepAt nodes width (.child n.id (1-side)) sibling := by
  have hs : side = 0 ∨ side = 1 := by omega
  rcases hs with rfl | rfl
  · exact hr
  · exact ⟨hr.1, hr.2.2, hr.2.1⟩

theorem fork_rep_intro (hb : side < 2)
    (hn : nodes[n.id]? = some (forkNode width base n side chosen sibling))
    (hc : RepAt nodes width (.child n.id side) chosen)
    (hs : RepAt nodes width (.child n.id (1-side)) sibling) :
    RepAt nodes width base (Tree.fork n side chosen sibling) := by
  have h : side = 0 ∨ side = 1 := by omega
  rcases h with rfl | rfl
  · exact ⟨hn, hc, hs⟩
  · exact ⟨hn, hs, hc⟩

/-- The one-allocation attachment followed by the original parent connection. -/
def graftOneChild (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (id : Nat) (old : WG.AipNode) (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let side := bit (rootWidth v4) cidr old.bits
  let attached := connectedChild (graftListed d (rootWidth v4) addr cidr pid p)
    d.nextNode side id leaf old
  connectedChild attached parent (bit pn.bitlen pn.cidr addr) d.nextNode pn
    { leaf with bit := leaf.bit.set! side (some id) }

/-- The two-allocation attachment followed by the original parent connection. -/
def graftTwoChild (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (id : Nat) (old : WG.AipNode) (addr cidr pid split : Nat) (p : WG.Peer) : WG.Device :=
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let mid := WG.newNode addr split (rootWidth v4) none
  let sd := bit (rootWidth v4) split old.bits
  let sn := bit (rootWidth v4) split addr
  let a := allocated (graftListed d (rootWidth v4) addr cidr pid p) mid
  let b := connectedChild a (d.nextNode + 1) sd id mid old
  let mid' := { mid with bit := mid.bit.set! sd (some id) }
  let c := connectedChild b (d.nextNode + 1) sn d.nextNode mid' leaf
  connectedChild c parent (bit pn.bitlen pn.cidr addr) (d.nextNode + 1) pn
    { mid' with bit := mid'.bit.set! sn (some d.nextNode) }

def graftChildInstalled (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (id : Nat) (old : WG.AipNode) (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let split := min cidr (common (rootWidth v4) old.bits addr)
  if split = cidr then graftOneChild d v4 parent pn id old addr cidr pid p
  else graftTwoChild d v4 parent pn id old addr cidr pid split p

theorem graftOneChild_compare (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (id : Nat) (old : WG.AipNode) (addr cidr pid : Nat) (p : WG.Peer) (q : Nat)
    (hp : parent ≠ q) (hf : d.nextNode ≠ q) :
    (graftOneChild d v4 parent pn id old addr cidr pid p).nodes[q]? =
      (graftOne d v4 id old addr cidr pid p).nodes[q]? := by
  simp [graftOneChild, graftOne, connectedChild, connectedRoot, rootWrite,
    Std.TreeMap.getElem?_insert, hp, hf]

theorem graftTwoChild_compare (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (id : Nat) (old : WG.AipNode) (addr cidr pid split : Nat) (p : WG.Peer) (q : Nat)
    (hp : parent ≠ q) (hm : d.nextNode + 1 ≠ q) :
    (graftTwoChild d v4 parent pn id old addr cidr pid split p).nodes[q]? =
      (graftTwo d v4 id old addr cidr pid split p).nodes[q]? := by
  simp [graftTwoChild, graftTwo, connectedChild, connectedRoot, rootWrite,
    Std.TreeMap.getElem?_insert, hp, hm]

theorem graftChildInstalled_nodes_other (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (id : Nat) (old : WG.AipNode) (addr cidr pid : Nat) (p : WG.Peer) (q : Nat)
    (hp : parent ≠ q) (hf : d.nextNode ≠ q) (hm : d.nextNode + 1 ≠ q) (ho : id ≠ q) :
    (graftChildInstalled d v4 parent pn id old addr cidr pid p).nodes[q]? = d.nodes[q]? := by
  unfold graftChildInstalled
  dsimp only
  split
  · rw [graftOneChild_compare _ _ _ _ _ _ _ _ _ _ _ hp hf]
    exact graftOne_nodes_other _ _ _ _ _ _ _ _ _ hf ho
  · rw [graftTwoChild_compare _ _ _ _ _ _ _ _ _ _ _ _ hp hm]
    exact graftTwo_nodes_other _ _ _ _ _ _ _ _ _ _ hf hm ho

/-- Reuse the selected-root structural proof, changing only the new root's
backlink. The parent is outside every retained node of the old focus. -/
theorem graftOneChild_rep (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (base : WG.Slot) (n : NodeData) (l r : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hb : NodesBelow d) (hp : parent < d.nextNode)
    (hdis : parent ∉ (Tree.node n l r).nodeIds)
    (hr : RepAt d.nodes (rootWidth v4) base (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup) :
    RepAt (graftOneChild d v4 parent pn n.id (encode (rootWidth v4) base n l r)
      addr cidr pid p).nodes (rootWidth v4) (.child parent (bit pn.bitlen pn.cidr addr))
      (Tree.fork (requestedNode d.nextNode addr cidr pid)
        (bit (rootWidth v4) cidr n.addr) (.node n l r) .empty) := by
  have hs := graftOne_rep_at d v4 base n l r addr cidr pid p hb hr hn
  have hf : ∀ q ∈ (Tree.node n l r).nodeIds,
      (graftOneChild d v4 parent pn n.id (encode (rootWidth v4) base n l r) addr cidr pid p).nodes[q]? =
      (graftOne d v4 n.id (encode (rootWidth v4) base n l r) addr cidr pid p).nodes[q]? := by
    intro q hq
    exact graftOneChild_compare _ _ _ _ _ _ _ _ _ _ _
      (fun he => hdis (he ▸ hq)) (Nat.ne_of_gt (hr.ids_below hb q hq))
  have hne : parent ≠ d.nextNode := Nat.ne_of_lt hp
  have hb' := bit_lt_two (rootWidth v4) cidr n.addr
  have hcases : bit (rootWidth v4) cidr n.addr = 0 ∨ bit (rootWidth v4) cidr n.addr = 1 := by omega
  rcases hcases with hside | hside
  all_goals simp only [Tree.fork, hside, ↓reduceIte] at hs ⊢
  all_goals apply hs.root_reparent
  all_goals solve
    | simp [graftOneChild, connectedChild, requestedNode, encode, WG.newNode, Tree.root,
        Std.TreeMap.getElem?_insert, Std.TreeMap.getElem_insert, hne, hside]
    | simpa only [Tree.nodeIds, List.nil_append, List.append_nil] using hf

theorem graftTwoChild_rep (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (base : WG.Slot) (n : NodeData) (l r : Tree) (addr cidr pid split : Nat) (p : WG.Peer)
    (hb : NodesBelow d) (hp : parent < d.nextNode)
    (hdis : parent ∉ (Tree.node n l r).nodeIds)
    (hr : RepAt d.nodes (rootWidth v4) base (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup)
    (hbits : bit (rootWidth v4) split n.addr ≠ bit (rootWidth v4) split addr) :
    RepAt (graftTwoChild d v4 parent pn n.id (encode (rootWidth v4) base n l r)
      addr cidr pid split p).nodes (rootWidth v4) (.child parent (bit pn.bitlen pn.cidr addr))
      (Tree.fork ⟨d.nextNode + 1, addr, split, none⟩
        (bit (rootWidth v4) split n.addr) (.node n l r) (requestedLeaf d.nextNode addr cidr pid)) := by
  have hs := graftTwo_rep_at d v4 base n l r addr cidr pid split p hb hr hn hbits
  have hf : ∀ q ∈ (Tree.node n l r).nodeIds ++ (requestedLeaf d.nextNode addr cidr pid).nodeIds,
      (graftTwoChild d v4 parent pn n.id (encode (rootWidth v4) base n l r) addr cidr pid split p).nodes[q]? =
      (graftTwo d v4 n.id (encode (rootWidth v4) base n l r) addr cidr pid split p).nodes[q]? := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact graftTwoChild_compare _ _ _ _ _ _ _ _ _ _ _ _
        (fun he => hdis (he ▸ hq)) (Nat.ne_of_gt (Nat.lt_succ_of_lt (hr.ids_below hb q hq)))
    · have he : q = d.nextNode := by simpa [requestedLeaf, requestedNode, Tree.nodeIds] using hq
      subst q
      exact graftTwoChild_compare d v4 parent pn n.id (encode (rootWidth v4) base n l r)
        addr cidr pid split p d.nextNode (Nat.ne_of_lt hp) (Nat.succ_ne_self _)
  have hne : parent ≠ d.nextNode + 1 := by omega
  have h0 := bit_lt_two (rootWidth v4) split n.addr
  have h1 := bit_lt_two (rootWidth v4) split addr
  have hcases : (bit (rootWidth v4) split n.addr = 0 ∧ bit (rootWidth v4) split addr = 1) ∨
      (bit (rootWidth v4) split n.addr = 1 ∧ bit (rootWidth v4) split addr = 0) := by omega
  rcases hcases with ⟨h0,h1⟩ | ⟨h0,h1⟩
  all_goals simp only [Tree.fork, h0, ↓reduceIte] at hs ⊢
  all_goals apply hs.root_reparent
  all_goals solve
    | simp [graftTwoChild, connectedChild, requestedNode, requestedLeaf, encode, WG.newNode, Tree.root,
        Std.TreeMap.getElem?_insert, Std.TreeMap.getElem_insert, hne, h0, h1]
    | exact hf
    | intro q hq; exact hf q (by simpa only [List.mem_append, or_comm] using hq)

theorem graftChildInstalled_rep (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (base : WG.Slot) (n : NodeData) (l r : Tree) (addr cidr pid : Nat) (p : WG.Peer)
    (hb : NodesBelow d) (hp : parent < d.nextNode)
    (hdis : parent ∉ (Tree.node n l r).nodeIds)
    (hr : RepAt d.nodes (rootWidth v4) base (.node n l r))
    (hn : (Tree.node n l r).nodeIds.Nodup) (hv : (Tree.node n l r).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)) :
    RepAt (graftChildInstalled d v4 parent pn n.id (encode (rootWidth v4) base n l r)
      addr cidr pid p).nodes (rootWidth v4) (.child parent (bit pn.bitlen pn.cidr addr))
      ((Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree := by
  rw [root_graft_insertFresh _ _ _ _ _ _ _ _ hstop]
  by_cases hs : min cidr (common (rootWidth v4) n.addr addr) = cidr
  · simpa [graftChildInstalled, encode, graft, hs] using
      graftOneChild_rep d v4 parent pn base n l r addr cidr pid p hb hp hdis hr hn
  · obtain ⟨he, _, _, hbits⟩ := graft_split_properties hv ha (graftable_of_stopped hv ha hstop) hs
    have hbits' : bit (rootWidth v4) (min cidr (common (rootWidth v4) n.addr addr)) n.addr ≠
        bit (rootWidth v4) (min cidr (common (rootWidth v4) n.addr addr)) addr := by
      simpa only [he] using hbits
    simpa [graftChildInstalled, encode, graft, hs] using
      graftTwoChild_rep d v4 parent pn base n l r addr cidr pid _ p hb hp hdis hr hn hbits'

theorem graftChildInstalled_parent (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (id : Nat) (old : WG.AipNode) (addr cidr pid : Nat) (p : WG.Peer) :
    let split := min cidr (common (rootWidth v4) old.bits addr)
    (graftChildInstalled d v4 parent pn id old addr cidr pid p).nodes[parent]? =
      some { pn with bit := pn.bit.set! (bit pn.bitlen pn.cidr addr) (some (if split = cidr then d.nextNode else d.nextNode+1)) } := by
  dsimp only
  unfold graftChildInstalled
  dsimp only
  split <;> simp_all [graftOneChild, graftTwoChild, connectedChild]

theorem graftChildInstalled_metadata (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (id : Nat) (old : WG.AipNode) (addr cidr pid : Nat) (p : WG.Peer) :
    let split := min cidr (common (rootWidth v4) old.bits addr)
    let installed := graftChildInstalled d v4 parent pn id old addr cidr pid p
    installed.nextNode = d.nextNode + (if split = cidr then 1 else 2) ∧
      (∀ family, rootValue installed family = rootValue d family) ∧
      installed.peerAllowedips.seq = d.peerAllowedips.seq := by
  dsimp only
  unfold graftChildInstalled
  dsimp only
  split <;> simp_all [graftOneChild, graftTwoChild, connectedChild, allocated, graftListed, rootValue]

theorem graftChildInstalled_below (d : WG.Device) (v4 : Bool) (parent : Nat) (pn : WG.AipNode)
    (id : Nat) (old : WG.AipNode) (addr cidr pid : Nat) (p : WG.Peer)
    (hb : NodesBelow d) (hp : parent < d.nextNode) (hi : id < d.nextNode) :
    NodesBelow (graftChildInstalled d v4 parent pn id old addr cidr pid p) := by
  unfold graftChildInstalled
  dsimp only
  split
  · intro q node hget
    change q < d.nextNode + 1
    by_cases h1 : parent = q
    · subst q; exact Nat.lt_succ_of_lt hp
    by_cases h2 : d.nextNode = q
    · subst q; exact Nat.lt_succ_self _
    by_cases h3 : id = q
    · subst q; exact Nat.lt_succ_of_lt hi
    rw [graftOneChild_compare _ _ _ _ _ _ _ _ _ _ _ h1 h2,
      graftOne_nodes_other _ _ _ _ _ _ _ _ _ h2 h3] at hget
    exact Nat.lt_succ_of_lt (hb _ _ hget)
  · intro q node hget
    change q < (d.nextNode + 1) + 1
    by_cases h1 : parent = q
    · subst q; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hp)
    by_cases h2 : d.nextNode = q
    · subst q; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
    by_cases h3 : id = q
    · subst q; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hi)
    by_cases h4 : d.nextNode + 1 = q
    · subst q; exact Nat.lt_succ_self _
    rw [graftTwoChild_compare _ _ _ _ _ _ _ _ _ _ _ _ h1 h4,
      graftTwo_nodes_other _ _ _ _ _ _ _ _ _ _ h2 h4 h3] at hget
    exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt (hb _ _ hget))

def contextGraftInstalled (d : WG.Device) (v4 : Bool) (base : WG.Slot)
    (parent : NodeData) (side : Nat) (sibling : Tree) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  graftChildInstalled d v4 parent.id (forkNode (rootWidth v4) base parent side (.node n l r) sibling)
    n.id (encode (rootWidth v4) (.child parent.id side) n l r) addr cidr pid p

theorem forkNode_replace (hb : side < 2) :
    { forkNode width base n side before sibling with
      bit := (forkNode width base n side before sibling).bit.set! side after.root } =
      forkNode width base n side after sibling := by
  have h : side = 0 ∨ side = 1 := by omega
  rcases h with rfl | rfl <;> rfl

theorem contextGraftInstalled_local_rep (d : WG.Device) (v4 : Bool) (base : WG.Slot)
    (parent : NodeData) (side : Nat) (sibling : Tree) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) base (Tree.fork parent side (.node n l r) sibling))
    (hn : (Tree.fork parent side (.node n l r) sibling).nodeIds.Nodup)
    (hv : (Tree.node n l r).Valid (rootWidth v4)) (ha : addr < 2 ^ rootWidth v4)
    (hbit : bit (rootWidth v4) parent.cidr addr = side)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)) :
    RepAt (contextGraftInstalled d v4 base parent side sibling n l r addr cidr pid p).nodes
      (rootWidth v4) base (Tree.fork parent side
        ((Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree sibling) := by
  obtain ⟨hparent, hfocus, hsibling⟩ := fork_rep_parts hb hr
  have hnd := (Tree.fork_nodeIds_perm parent side (.node n l r) sibling).nodup hn
  change (parent.id :: ((Tree.node n l r).nodeIds ++ sibling.nodeIds)).Nodup at hnd
  obtain ⟨hpar, hrest⟩ := List.nodup_cons.mp hnd
  obtain ⟨hfn, hsn, hsep⟩ := List.nodup_append.mp hrest
  have hpf : parent.id ∉ (Tree.node n l r).nodeIds := fun h => hpar (List.mem_append_left _ h)
  have hps : parent.id ∉ sibling.nodeIds := fun h => hpar (List.mem_append_right _ h)
  have hns : n.id ∉ sibling.nodeIds := fun h => hsep _ (by simp [Tree.nodeIds]) _ h rfl
  let out := contextGraftInstalled d v4 base parent side sibling n l r addr cidr pid p
  apply fork_rep_intro hb
  · have h := graftChildInstalled_parent d v4 parent.id (forkNode (rootWidth v4) base parent side (.node n l r) sibling)
      n.id (encode (rootWidth v4) (.child parent.id side) n l r) addr cidr pid p
    have hg := root_graft_insertFresh (rootWidth v4) d.nextNode addr cidr pid n l r hstop
    have hroot : ((Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree.root =
        some (if min cidr (common (rootWidth v4) n.addr addr) = cidr then d.nextNode else d.nextNode+1) := by
      rw [hg]; simp only [graft]; split <;> simp_all [Tree.fork_root, requestedNode]
    have hcases : side = 0 ∨ side = 1 := by omega
    rcases hcases with rfl | rfl
    all_goals simp only [forkNode, ↓reduceIte, encode, hbit] at h
    all_goals by_cases he : min cidr (common (rootWidth v4) n.addr addr) = cidr
    all_goals simpa [contextGraftInstalled, forkNode, encode, hroot, he, hbit] using h
  · have h := graftChildInstalled_rep d v4 parent.id (forkNode (rootWidth v4) base parent side (.node n l r) sibling)
      (.child parent.id side) n l r addr cidr pid p hbelow (hbelow _ _ hparent) hpf hfocus hfn hv ha hstop
    simpa only [contextGraftInstalled, forkNode_bitlen, forkNode_cidr, hbit] using h
  · apply hsibling.congr
    intro q hq
    have hqbelow := hsibling.ids_below hbelow q hq
    exact graftChildInstalled_nodes_other _ _ _ _ _ _ _ _ _ _ _
      (fun he => hps (he ▸ hq)) (Nat.ne_of_gt hqbelow) (Nat.ne_of_gt (Nat.lt_succ_of_lt hqbelow))
      (fun he => hns (he ▸ hq))

theorem contextGraftInstalled_context_rep (d : WG.Device) (v4 : Bool) (c : Context)
    (parent : NodeData) (side : Nat) (sibling : Tree) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork parent side (.node n l r) sibling)))
    (hn : (c.plug (Tree.fork parent side (.node n l r) sibling)).nodeIds.Nodup)
    (hv : (Tree.node n l r).Valid (rootWidth v4)) (ha : addr < 2 ^ rootWidth v4)
    (hbit : bit (rootWidth v4) parent.cidr addr = side)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)) :
    RepAt (contextGraftInstalled d v4 (c.slot (rootSlot v4)) parent side sibling n l r addr cidr pid p).nodes
      (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork parent side
        ((Tree.node n l r).insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree sibling)) := by
  have hfocus := c.focus_rep _ _ hr
  have hlocal := contextGraftInstalled_local_rep d v4 (c.slot (rootSlot v4)) parent side sibling n l r
    addr cidr pid p hb hbelow hfocus (c.focus_nodup _ hn) hv ha hbit hstop
  apply c.rep_replace_sameRoot _ _ _ hr hlocal (by simp only [Tree.fork_root])
  intro q hq
  have hqwhole := (c.mem_plug_nodeIds (Tree.fork parent side (.node n l r) sibling) q).mpr (.inl hq)
  have hqbelow := hr.ids_below hbelow q hqwhole
  have hpar := c.focus_disjoint _ hn parent.id (by simp [Tree.mem_fork_nodeIds])
  have hold := c.focus_disjoint _ hn n.id (by simp [Tree.mem_fork_nodeIds, Tree.nodeIds])
  exact graftChildInstalled_nodes_other _ _ _ _ _ _ _ _ _ _ _
    (fun he => hpar (he ▸ hq)) (Nat.ne_of_gt hqbelow) (Nat.ne_of_gt (Nat.lt_succ_of_lt hqbelow))
    (fun he => hold (he ▸ hq))

theorem context_graft_insertFresh (c : Context) (parent : NodeData) (side : Nat) (sibling : Tree)
    (n : NodeData) (l r : Tree) (width fresh addr cidr pid : Nat)
    (hf : c.Follows width addr cidr) (hb : side < 2) (hlt : parent.cidr < cidr)
    (hm : prefixBits width parent.cidr parent.addr = prefixBits width parent.cidr addr)
    (hbit : bit width parent.cidr addr = side) :
    (c.plug (Tree.fork parent side (.node n l r) sibling)).insertFresh width fresh addr cidr pid =
      let localResult := (Tree.node n l r).insertFresh width fresh addr cidr pid
      { localResult with tree := c.plug (Tree.fork parent side localResult.tree sibling) } := by
  have h := (c.append (gapContext parent side sibling)).insertFresh (.node n l r) fresh pid
    (hf.append (gapContext_follows parent side sibling hb hlt hm hbit))
  simpa only [Context.plug_append, gapContext_plug] using h

theorem contextGraftInstalled_other_rep (d : WG.Device) (v4 : Bool) (base : WG.Slot)
    (parent : NodeData) (side : Nat) (sibling : Tree) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) base (Tree.fork parent side (.node n l r) sibling))
    (other : Tree) (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) :
    RepAt (contextGraftInstalled d v4 base parent side sibling n l r addr cidr pid p).nodes
      (rootWidth (!v4)) (rootSlot (!v4)) other := by
  obtain ⟨hparent, hfocus, _⟩ := fork_rep_parts hb hr
  have hpar : parent.id ∉ other.nodeIds := by
    intro hi
    obtain ⟨node, hn, hw⟩ := ho.resident_bitlen hi
    have he := Option.some.inj (hn.symm.trans hparent)
    rw [he, forkNode_bitlen] at hw
    cases v4 <;> simp [rootWidth] at hw
  have hnode : n.id ∉ other.nodeIds := by
    intro hi
    obtain ⟨node, hn, hw⟩ := ho.resident_bitlen hi
    have he := Option.some.inj (hn.symm.trans hfocus.1)
    rw [he] at hw
    cases v4 <;> simp [encode, rootWidth] at hw
  apply ho.congr
  intro q hq
  have hqbelow := ho.ids_below hbelow q hq
  exact graftChildInstalled_nodes_other _ _ _ _ _ _ _ _ _ _ _
    (fun he => hpar (he ▸ hq)) (Nat.ne_of_gt hqbelow) (Nat.ne_of_gt (Nat.lt_succ_of_lt hqbelow))
    (fun he => hnode (he ▸ hq))

theorem contextGraftInstalled_insert_metadata (d : WG.Device) (v4 : Bool) (c : Context)
    (parent : NodeData) (side : Nat) (sibling : Tree) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer)
    (hroot : rootValue d v4 = (c.plug (Tree.fork parent side (.node n l r) sibling)).root)
    (hf : c.Follows (rootWidth v4) addr cidr) (hb : side < 2) (hlt : parent.cidr < cidr)
    (hm : prefixBits (rootWidth v4) parent.cidr parent.addr = prefixBits (rootWidth v4) parent.cidr addr)
    (hbit : bit (rootWidth v4) parent.cidr addr = side)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)) :
    let inserted := (c.plug (Tree.fork parent side (.node n l r) sibling)).insertFresh
      (rootWidth v4) d.nextNode addr cidr pid
    let installed := contextGraftInstalled d v4 (c.slot (rootSlot v4)) parent side sibling n l r addr cidr pid p
    installed.nextNode = d.nextNode + inserted.allocations ∧
      rootValue installed v4 = inserted.tree.root ∧
      rootValue installed (!v4) = rootValue d (!v4) ∧
      installed.peerAllowedips.seq = d.peerAllowedips.seq := by
  dsimp only
  rw [context_graft_insertFresh c parent side sibling n l r _ _ _ _ _ hf hb hlt hm hbit]
  dsimp only
  have hmeta := graftChildInstalled_metadata d v4 parent.id
    (forkNode (rootWidth v4) (c.slot (rootSlot v4)) parent side (.node n l r) sibling)
    n.id (encode (rootWidth v4) (.child parent.id side) n l r) addr cidr pid p
  refine ⟨?_, ?_, hmeta.2.1 (!v4), hmeta.2.2⟩
  · rw [root_graft_insertFresh _ _ _ _ _ _ _ _ hstop]
    by_cases he : min cidr (common (rootWidth v4) n.addr addr) = cidr
    all_goals simpa [graft, contextGraftInstalled, encode, he] using hmeta.1
  · simp only [contextGraftInstalled]
    rw [hmeta.2.1 v4, hroot]
    exact c.root_congr (by simp only [Tree.fork_root])

end Leanux.Proofs.WG.AllowedIps
