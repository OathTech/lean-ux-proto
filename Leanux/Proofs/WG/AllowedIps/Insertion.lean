import Leanux.Proofs.WG.AllowedIps.Tree
import Init.Data.List.Perm
import Init.Data.List.Nat.Range

/-!
# Pure Patricia insertion

The subtree below an insertion position is either empty, covered by the new
prefix, or separated from it by a new ownerless branch. The requested node
uses the first fresh identifier; an intermediate branch, when needed, uses
the next one. Recursive insertion descends to this local graft or overwrites
an exact prefix. Addresses remain unmasked. This is an intermediate algorithm;
correspondence with the original mutations and their allocation outcomes is
a separate obligation.
-/

namespace Leanux.Proofs.WG.AllowedIps

/-- Put `chosen` on `side` and `other` on the opposite side. -/
def Tree.fork (n : NodeData) (side : Nat) (chosen other : Tree) : Tree :=
  if side = 0 then .node n chosen other else .node n other chosen

theorem Tree.fork_valid {n : NodeData} {chosen other : Tree} {side : Nat}
    (ha : n.addr < 2 ^ width) (hc : n.cidr ≤ width) (hb : side < 2)
    (hv : chosen.Valid width) (hu : other.Valid width)
    (he : Child width n side chosen) (hf : Child width n (1 - side) other) :
    (Tree.fork n side chosen other).Valid width := by
  unfold Tree.fork
  split <;> rename_i h
  · subst side
    exact ⟨ha, hc, hv, hu, he, hf⟩
  · have hs : side = 1 := by omega
    subst side
    exact ⟨ha, hc, hu, hv, hf, he⟩

theorem Tree.fork_compressed {n : NodeData} {chosen other : Tree} {side : Nat}
    (hc : chosen.Compressed) (ho : other.Compressed)
    (hn : n.peer = none → chosen.root.isSome ∧ other.root.isSome) :
    (Tree.fork n side chosen other).Compressed := by
  unfold Tree.fork
  split
  · exact ⟨hc, ho, hn⟩
  · exact ⟨ho, hc, fun h => ⟨(hn h).2, (hn h).1⟩⟩

@[simp] theorem Tree.fork_root (n : NodeData) (side : Nat) (chosen other : Tree) :
    (Tree.fork n side chosen other).root = some n.id := by
  unfold Tree.fork
  split <;> rfl

@[simp] theorem Child.fork {parent n : NodeData} {chosen other : Tree} {side branchBit : Nat} :
    Child width parent branchBit (Tree.fork n side chosen other) ↔
      parent.cidr < n.cidr ∧
      prefixBits width parent.cidr n.addr = prefixBits width parent.cidr parent.addr ∧
      bit width parent.cidr n.addr = branchBit := by
  unfold Tree.fork
  split <;> rfl

theorem Tree.fork_entries_perm (n : NodeData) (side : Nat) (chosen other : Tree) :
    (Tree.fork n side chosen other).entries.Perm
      (n.entries ++ chosen.entries ++ other.entries) := by
  unfold Tree.fork
  split
  · exact List.Perm.refl _
  · simpa only [Tree.entries, List.append_assoc] using
      (List.perm_append_comm (l₁ := other.entries) (l₂ := chosen.entries)).append_left n.entries

def requestedNode (fresh addr cidr peer : Nat) : NodeData :=
  ⟨fresh, addr, cidr, some peer⟩

def requestedEntry (fresh addr cidr peer : Nat) : Entry :=
  ⟨fresh, addr, cidr, peer⟩

def requestedLeaf (fresh addr cidr peer : Nat) : Tree :=
  .node (requestedNode fresh addr cidr peer) .empty .empty

@[simp] theorem requestedNode_entries (fresh addr cidr peer : Nat) :
    (requestedNode fresh addr cidr peer).entries = [requestedEntry fresh addr cidr peer] := rfl

@[simp] theorem requestedLeaf_entries (fresh addr cidr peer : Nat) :
    (requestedLeaf fresh addr cidr peer).entries = [requestedEntry fresh addr cidr peer] := rfl

theorem requestedLeaf_valid {addr cidr : Nat} (fresh peer : Nat)
    (ha : addr < 2 ^ width) (hc : cidr ≤ width) :
    (requestedLeaf fresh addr cidr peer).Valid width :=
  ⟨ha, hc, trivial, trivial, trivial, trivial⟩

@[simp] theorem requestedLeaf_compressed (fresh addr cidr peer : Nat) :
    (requestedLeaf fresh addr cidr peer).Compressed := by
  exact ⟨trivial, trivial, by simp [requestedNode]⟩

/-- Successful shape, before modeling allocation outcomes. -/
structure InsertResult where
  tree : Tree
  binding : Entry
  allocations : Nat

/-- Local insertion after placement has stopped before the old subtree. -/
def graft (width fresh addr cidr peer : Nat) (down : Tree) : InsertResult :=
  let owned := requestedNode fresh addr cidr peer
  let leaf := requestedLeaf fresh addr cidr peer
  let binding := requestedEntry fresh addr cidr peer
  match down with
  | .empty => ⟨leaf, binding, 1⟩
  | .node n l r =>
      let split := min cidr (common width n.addr addr)
      if split = cidr then
        ⟨Tree.fork owned (bit width cidr n.addr) (.node n l r) .empty, binding, 1⟩
      else
        let mid : NodeData := ⟨fresh + 1, addr, split, none⟩
        ⟨Tree.fork mid (bit width split n.addr) (.node n l r) leaf, binding, 2⟩

/-- Placement stopped strictly above a nonempty subtree's root. -/
def Graftable (width addr cidr : Nat) : Tree → Prop
  | .empty => True
  | .node n _ _ => min cidr (common width n.addr addr) < n.cidr

theorem graftable_of_stopped {n : NodeData} {l r : Tree}
    (hv : (Tree.node n l r).Valid width) (ha : addr < 2 ^ width)
    (hstop : ¬ (n.cidr ≤ cidr ∧
      prefixBits width n.cidr n.addr = prefixBits width n.cidr addr)) :
    Graftable width addr cidr (.node n l r) := by
  have hp := common_ge_iff hv.1 ha hv.2.1
  change min cidr (common width n.addr addr) < n.cidr
  omega

@[simp] theorem graft_binding (width fresh addr cidr peer : Nat) (down : Tree) :
    (graft width fresh addr cidr peer down).binding = requestedEntry fresh addr cidr peer := by
  cases down <;> simp [graft]
  split <;> rfl

theorem graft_allocations (width fresh addr cidr peer : Nat) (down : Tree) :
    (graft width fresh addr cidr peer down).allocations = 1 ∨
      (graft width fresh addr cidr peer down).allocations = 2 := by
  cases down <;> simp [graft]
  split <;> simp

/-- The two children of a genuine split have opposite branch bits. -/
theorem graft_split_properties {n : NodeData} {l r : Tree}
    (hv : (Tree.node n l r).Valid width) (ha : addr < 2 ^ width)
    (hg : Graftable width addr cidr (.node n l r))
    (hne : min cidr (common width n.addr addr) ≠ cidr) :
    min cidr (common width n.addr addr) = common width n.addr addr ∧
      common width n.addr addr < cidr ∧ common width n.addr addr < n.cidr ∧
      bit width (common width n.addr addr) n.addr ≠ bit width (common width n.addr addr) addr := by
  change min cidr (common width n.addr addr) < n.cidr at hg
  have hc : common width n.addr addr < cidr := by omega
  have hm : min cidr (common width n.addr addr) = common width n.addr addr := by omega
  have hn : n.addr ≠ addr := by
    intro he
    rw [he, common_self] at hg
    rw [he, common_self] at hc
    have := hv.2.1
    omega
  exact ⟨hm, hc, by omega, (common_split hv.1 ha hn).2.2⟩

theorem graft_valid {down : Tree} (hv : down.Valid width)
    (ha : addr < 2 ^ width) (hc : cidr ≤ width)
    (hg : Graftable width addr cidr down) (fresh peer : Nat) :
    (graft width fresh addr cidr peer down).tree.Valid width := by
  cases down with
  | empty => exact requestedLeaf_valid fresh peer ha hc
  | node n l r =>
      change min cidr (common width n.addr addr) < n.cidr at hg
      by_cases hm : min cidr (common width n.addr addr) = cidr
      · simp only [graft]
        rw [ite_eq_left hm]
        refine Tree.fork_valid (n := requestedNode fresh addr cidr peer)
          (other := .empty) ha hc (bit_lt_two _ _ _) hv trivial ?_ ?_
        · change cidr < n.cidr ∧ _ ∧ _
          exact ⟨by omega, (common_ge_iff hv.1 ha hc).mp (by omega), rfl⟩
        · trivial
      · obtain ⟨he, hnew, hold, hbit⟩ := graft_split_properties hv ha hg hm
        simp only [graft]
        rw [ite_eq_right hm]
        simp only [he]
        refine Tree.fork_valid (n := ⟨fresh + 1, addr, common width n.addr addr, none⟩)
          ha (common_le _ _ _) (bit_lt_two _ _ _) hv
          (requestedLeaf_valid fresh peer ha hc) ?_ ?_
        · exact ⟨hold, prefix_common hv.1 ha, rfl⟩
        · change common width n.addr addr < cidr ∧ _ ∧ _
          refine ⟨hnew, rfl, ?_⟩
          have h0 := bit_lt_two width (common width n.addr addr) n.addr
          have h1 := bit_lt_two width (common width n.addr addr) addr
          change bit width (common width n.addr addr) addr = 1 - bit width (common width n.addr addr) n.addr
          omega

theorem graft_compressed {down : Tree} (h : down.Compressed)
    (width fresh addr cidr peer : Nat) :
    (graft width fresh addr cidr peer down).tree.Compressed := by
  cases down with
  | empty => exact requestedLeaf_compressed _ _ _ _
  | node n l r =>
      simp only [graft]
      split
      · exact Tree.fork_compressed (n := requestedNode fresh addr cidr peer)
          (other := .empty) h trivial (by simp [requestedNode])
      · exact Tree.fork_compressed h (requestedLeaf_compressed fresh addr cidr peer) (by
          simp [Tree.root, requestedLeaf])

/-- Every old owned entry is retained once, and the requested entry is added
once. Traversal order can change when the two children swap sides. -/
theorem graft_entries (width fresh addr cidr peer : Nat) (down : Tree) :
    (graft width fresh addr cidr peer down).tree.entries.Perm
      (requestedEntry fresh addr cidr peer :: down.entries) := by
  cases down with
  | empty => exact List.Perm.refl _
  | node n l r =>
      simp only [graft]
      split
      · simpa only [requestedNode_entries, Tree.entries, List.append_nil, List.singleton_append]
          using Tree.fork_entries_perm (requestedNode fresh addr cidr peer)
          (bit width cidr n.addr) (.node n l r) .empty
      · have h := Tree.fork_entries_perm
          (NodeData.mk (fresh + 1) addr (min cidr (common width n.addr addr)) none)
          (bit width (min cidr (common width n.addr addr)) n.addr) (.node n l r)
          (requestedLeaf fresh addr cidr peer)
        simp only [NodeData.entries, NodeData.own, Option.map_none, Option.toList_none,
          List.nil_append, requestedLeaf_entries] at h
        exact h.trans (List.perm_append_singleton _ _)

/-- A graft remains in the enclosing branch when both its old subtree and
the requested prefix belong there. This is the context lemma for recursion. -/
theorem graft_child {down : Tree} {parent : NodeData} {branchBit fresh peer : Nat}
    (hv : down.Valid width) (ha : addr < 2 ^ width) (hc : cidr ≤ width)
    (hold : Child width parent branchBit down)
    (hnew : Child width parent branchBit (requestedLeaf fresh addr cidr peer)) :
    Child width parent branchBit (graft width fresh addr cidr peer down).tree := by
  change parent.cidr < cidr ∧
    prefixBits width parent.cidr addr = prefixBits width parent.cidr parent.addr ∧
    bit width parent.cidr addr = branchBit at hnew
  cases down with
  | empty => exact hnew
  | node n l r =>
      have hp : parent.cidr < width := by omega
      have hs : prefixBits width (parent.cidr + 1) n.addr =
          prefixBits width (parent.cidr + 1) addr :=
        (prefix_succ_eq_iff hp).mpr
          ⟨hold.2.1.trans hnew.2.1.symm, hold.2.2.trans hnew.2.2.symm⟩
      have hcommon := (common_ge_iff hv.1 ha (by omega)).mpr hs
      simp only [graft]
      split
      · exact Child.fork.mpr hnew
      · apply Child.fork.mpr
        exact ⟨by dsimp; omega, hnew.2.1, hnew.2.2⟩

@[simp] theorem graft_prefixKey (width fresh addr cidr peer : Nat) (down : Tree) :
    (graft width fresh addr cidr peer down).binding.prefixKey width =
      (cidr, prefixBits width cidr addr) := by
  rw [graft_binding]
  rfl

/-- Every reachable node identifier, including ownerless branch nodes. -/
def Tree.nodeIds : Tree → List Nat
  | .empty => []
  | .node n l r => n.id :: (l.nodeIds ++ r.nodeIds)

theorem Tree.mem_fork_nodeIds (n : NodeData) (side : Nat) (chosen other : Tree) (id : Nat) :
    id ∈ (Tree.fork n side chosen other).nodeIds ↔
      id = n.id ∨ id ∈ chosen.nodeIds ∨ id ∈ other.nodeIds := by
  unfold Tree.fork
  split <;> simp only [Tree.nodeIds, List.mem_cons, List.mem_append] <;> grind

/-- Exact identifier accounting; identifiers are slots, not lifetime stamps. -/
theorem graft_nodeIds (width fresh addr cidr peer : Nat) (down : Tree) (id : Nat) :
    id ∈ (graft width fresh addr cidr peer down).tree.nodeIds ↔
      id ∈ down.nodeIds ∨ id = fresh ∨
        ((graft width fresh addr cidr peer down).allocations = 2 ∧ id = fresh + 1) := by
  cases down with
  | empty => simp [graft, requestedLeaf, requestedNode, Tree.nodeIds]
  | node n l r =>
      simp only [graft]
      split <;> simp only [Tree.mem_fork_nodeIds, requestedNode, requestedLeaf,
        Tree.nodeIds, List.mem_cons, List.mem_append, List.not_mem_nil] <;> grind

theorem Tree.fork_nodeIds_nodup {n : NodeData} {chosen other : Tree} {side : Nat}
    (hc : chosen.nodeIds.Nodup) (ho : other.nodeIds.Nodup)
    (hnc : n.id ∉ chosen.nodeIds) (hno : n.id ∉ other.nodeIds)
    (hd : ∀ id ∈ chosen.nodeIds, id ∉ other.nodeIds) :
    (Tree.fork n side chosen other).nodeIds.Nodup := by
  unfold Tree.fork
  split <;> simp only [Tree.nodeIds, List.nodup_cons, List.mem_append, not_or, List.nodup_append]
  · exact ⟨⟨hnc, hno⟩, hc, ho, fun a ha b hb he => hd a ha (he ▸ hb)⟩
  · exact ⟨⟨hno, hnc⟩, ho, hc, fun a ha b hb he => hd b hb (he ▸ ha)⟩

theorem graft_nodeIds_nodup {down : Tree} (hn : down.nodeIds.Nodup)
    (hf : ∀ id ∈ down.nodeIds, id < fresh) (width addr cidr peer : Nat) :
    (graft width fresh addr cidr peer down).tree.nodeIds.Nodup := by
  have h0 : fresh ∉ down.nodeIds := fun h => Nat.lt_irrefl _ (hf _ h)
  have h1 : fresh + 1 ∉ down.nodeIds := by
    intro h
    have := hf _ h
    omega
  cases down with
  | empty => simp [graft, requestedLeaf, Tree.nodeIds]
  | node n l r =>
      simp only [graft]
      split
      · apply Tree.fork_nodeIds_nodup (other := .empty) hn (by simp [Tree.nodeIds]) h0
        · simp [Tree.nodeIds]
        · simp [Tree.nodeIds]
      · apply Tree.fork_nodeIds_nodup hn
          (show (requestedLeaf fresh addr cidr peer).nodeIds.Nodup by
            simp [requestedLeaf, Tree.nodeIds]) h1
        · simp [requestedLeaf, requestedNode, Tree.nodeIds]
        · intro id hi
          have := hf id hi
          simp only [requestedLeaf, requestedNode, Tree.nodeIds, List.append_nil,
            List.mem_cons, List.not_mem_nil, or_false]
          omega

theorem graft_nodeIds_bounded {down : Tree} (hf : ∀ id ∈ down.nodeIds, id < fresh)
    (width addr cidr peer : Nat) :
    ∀ id ∈ (graft width fresh addr cidr peer down).tree.nodeIds,
      id < fresh + (graft width fresh addr cidr peer down).allocations := by
  intro id hi
  have ha := graft_allocations width fresh addr cidr peer down
  rcases (graft_nodeIds width fresh addr cidr peer down id).mp hi with hi | rfl | ⟨he, rfl⟩
  · have := hf id hi
    omega
  · omega
  · omega

/-- One recursive insertion algorithm. Exact-prefix overwrite retains the
old node's identifier and unmasked address, changing only its owner. Fresh
identifiers are consumed at the stopped position, after the descent. -/
def Tree.insertFresh (width fresh addr cidr peer : Nat) : Tree → InsertResult
  | .empty => graft width fresh addr cidr peer .empty
  | .node n l r =>
      if n.cidr ≤ cidr ∧ prefixBits width n.cidr n.addr = prefixBits width n.cidr addr then
        if n.cidr = cidr then
          ⟨.node { n with peer := some peer } l r, n.entry peer, 0⟩
        else if bit width n.cidr addr = 0 then
          let result := l.insertFresh width fresh addr cidr peer
          { result with tree := .node n result.tree r }
        else
          let result := r.insertFresh width fresh addr cidr peer
          { result with tree := .node n l result.tree }
      else graft width fresh addr cidr peer (.node n l r)

theorem Tree.insertFresh_child {t : Tree} {parent : NodeData} {branchBit fresh peer : Nat}
    (hv : t.Valid width) (ha : addr < 2 ^ width) (hc : cidr ≤ width)
    (hold : Child width parent branchBit t)
    (hnew : Child width parent branchBit (requestedLeaf fresh addr cidr peer)) :
    Child width parent branchBit (t.insertFresh width fresh addr cidr peer).tree := by
  cases t with
  | empty => exact hnew
  | node n l r =>
      rw [Tree.insertFresh]
      split
      · split
        · exact hold
        · split <;> exact hold
      · exact graft_child hv ha hc hold hnew

theorem Tree.insertFresh_valid {t : Tree} (hv : t.Valid width)
    (ha : addr < 2 ^ width) (hc : cidr ≤ width) (fresh peer : Nat) :
    (t.insertFresh width fresh addr cidr peer).tree.Valid width := by
  induction t with
  | empty => exact requestedLeaf_valid fresh peer ha hc
  | node n l r ihl ihr =>
      have hl := hv.2.2.1
      have hr := hv.2.2.2.1
      have el := hv.2.2.2.2.1
      have er := hv.2.2.2.2.2
      rw [Tree.insertFresh]
      split
      next hcover =>
        split
        · exact hv
        next hne =>
          have hlt : n.cidr < cidr := by omega
          split
          next hb =>
            exact ⟨hv.1, hv.2.1, ihl hl, hr,
              Tree.insertFresh_child hl ha hc el ⟨hlt, hcover.2.symm, hb⟩, er⟩
          next hb =>
            have hone : bit width n.cidr addr = 1 := by
              have := bit_lt_two width n.cidr addr
              omega
            exact ⟨hv.1, hv.2.1, hl, ihr hr, el,
              Tree.insertFresh_child hr ha hc er ⟨hlt, hcover.2.symm, hone⟩⟩
      next hstop =>
        exact graft_valid hv ha hc (graftable_of_stopped hv ha hstop) fresh peer

theorem Tree.insertFresh_nonempty (t : Tree) (width fresh addr cidr peer : Nat) :
    (t.insertFresh width fresh addr cidr peer).tree.root.isSome := by
  cases t with
  | empty => rfl
  | node n l r =>
      rw [Tree.insertFresh]
      split
      · split
        · rfl
        · split <;> rfl
      · simp only [graft]
        split <;> simp

theorem Tree.insertFresh_compressed {t : Tree} (h : t.Compressed)
    (width fresh addr cidr peer : Nat) :
    (t.insertFresh width fresh addr cidr peer).tree.Compressed := by
  induction t with
  | empty => exact requestedLeaf_compressed _ _ _ _
  | node n l r ihl ihr =>
      rw [Tree.insertFresh]
      split
      · split
        · exact ⟨h.1, h.2.1, by simp⟩
        · split
          · exact ⟨ihl h.1, h.2.1, fun hn =>
              ⟨Tree.insertFresh_nonempty _ _ _ _ _ _, (h.2.2 hn).2⟩⟩
          · exact ⟨h.1, ihr h.2.1, fun hn =>
              ⟨(h.2.2 hn).1, Tree.insertFresh_nonempty _ _ _ _ _ _⟩⟩
      · exact graft_compressed h _ _ _ _ _

theorem Tree.insertFresh_allocations (t : Tree) (width fresh addr cidr peer : Nat) :
    (t.insertFresh width fresh addr cidr peer).allocations ≤ 2 := by
  induction t with
  | empty => change 1 ≤ 2; decide
  | node n l r ihl ihr =>
      rw [Tree.insertFresh]
      split
      · split
        · change 0 ≤ 2; decide
        · split
          · exact ihl
          · exact ihr
      · have := graft_allocations width fresh addr cidr peer (.node n l r)
        omega

theorem Tree.insertFresh_prefixKey (t : Tree) (width fresh addr cidr peer : Nat) :
    (t.insertFresh width fresh addr cidr peer).binding.prefixKey width =
      (cidr, prefixBits width cidr addr) := by
  induction t with
  | empty => rfl
  | node n l r ihl ihr =>
      rw [Tree.insertFresh]
      split
      next hcover =>
        split
        next he =>
          apply Prod.ext
          · exact he
          · change prefixBits width n.cidr n.addr = prefixBits width cidr addr
            simpa only [he] using hcover.2
        · split
          · exact ihl
          · exact ihr
      · exact graft_prefixKey _ _ _ _ _ _

theorem Tree.insertFresh_peer (t : Tree) (width fresh addr cidr peer : Nat) :
    (t.insertFresh width fresh addr cidr peer).binding.peer = peer := by
  induction t with
  | empty => rfl
  | node n l r ihl ihr =>
      rw [Tree.insertFresh]
      split
      · split
        · rfl
        · split
          · exact ihl
          · exact ihr
      · rw [graft_binding]; rfl

theorem NodeData.prefixKey_ne_request {width addr cidr : Nat} {n : NodeData} {e : Entry}
    (he : e ∈ n.entries) (hne : n.cidr ≠ cidr) :
    e.prefixKey width ≠ (cidr, prefixBits width cidr addr) := by
  intro h
  have := NodeData.mem_entries_fields he
  have := congrArg Prod.fst h
  change e.cidr = cidr at this
  omega

theorem Child.prefixKey_ne_request {t : Tree} (hv : t.Valid width)
    (he : Child width parent branchBit t) (hc : cidr ≤ width)
    (hb : bit width parent.cidr addr ≠ branchBit) {e : Entry} (hm : e ∈ t.entries) :
    e.prefixKey width ≠ (cidr, prefixBits width cidr addr) := by
  intro h
  have hp := he.entries_properties hv hm
  have hcidr := congrArg Prod.fst h
  have hprefix := congrArg Prod.snd h
  change e.cidr = cidr at hcidr
  change prefixBits width e.cidr e.addr = prefixBits width cidr addr at hprefix
  rw [hcidr] at hprefix
  have hbit := bit_eq_of_prefix_eq (by omega : parent.cidr < cidr) hc hprefix
  exact hb (hbit.symm.trans hp.2.2)

theorem graft_prefix_absent {down : Tree} (hv : down.Valid width)
    (ha : addr < 2 ^ width) (hc : cidr ≤ width)
    (hg : Graftable width addr cidr down) (fresh peer : Nat) :
    ∀ e ∈ down.entries, e.prefixKey width ≠ (cidr, prefixBits width cidr addr) := by
  have hn := Tree.prefixKeys_nodup (graft_valid hv ha hc hg fresh peer)
  have hp := (graft_entries width fresh addr cidr peer down).map (Entry.prefixKey width)
  have hnot := (List.nodup_cons.mp (hp.nodup hn)).1
  intro e he heq
  exact hnot (List.mem_map.mpr ⟨e, he, heq⟩)

/-- Exact last-writer semantics on canonical prefixes: add the requested
owner and remove every former entry for that prefix, retaining all others. -/
theorem Tree.insertFresh_entries {t : Tree} (hv : t.Valid width)
    (ha : addr < 2 ^ width) (hc : cidr ≤ width) (fresh peer : Nat) (e : Entry) :
    e ∈ (t.insertFresh width fresh addr cidr peer).tree.entries ↔
      e = (t.insertFresh width fresh addr cidr peer).binding ∨
        (e ∈ t.entries ∧ e.prefixKey width ≠ (cidr, prefixBits width cidr addr)) := by
  induction t with
  | empty => simp [Tree.insertFresh, graft, requestedLeaf, Tree.entries]
  | node n l r ihl ihr =>
      have hl := hv.2.2.1
      have hr := hv.2.2.2.1
      have el := hv.2.2.2.2.1
      have er := hv.2.2.2.2.2
      rw [Tree.insertFresh]
      split
      next hcover =>
        split
        next he =>
          have hlne : e ∈ l.entries → e.prefixKey width ≠ (cidr, prefixBits width cidr addr) := by
            intro hm heq
            have hp := el.entries_properties hl hm
            have hcidr := congrArg Prod.fst heq
            change e.cidr = cidr at hcidr
            omega
          have hrne : e ∈ r.entries → e.prefixKey width ≠ (cidr, prefixBits width cidr addr) := by
            intro hm heq
            have hp := er.entries_properties hr hm
            have hcidr := congrArg Prod.fst heq
            change e.cidr = cidr at hcidr
            omega
          have hone : e ∈ n.entries → e.prefixKey width = (cidr, prefixBits width cidr addr) := by
            intro hm
            obtain ⟨hae, hce⟩ := NodeData.mem_entries_fields hm
            apply Prod.ext
            · exact hce.trans he
            · change prefixBits width e.cidr e.addr = prefixBits width cidr addr
              rw [hae, hce]
              simpa only [he] using hcover.2
          have heown : ({ n with peer := some peer } : NodeData).entries = [n.entry peer] := rfl
          simp only [Tree.entries, heown, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          grind only
        next hne =>
          have hon := NodeData.prefixKey_ne_request (width := width) (addr := addr)
            (cidr := cidr) (n := n) (e := e)
          split
          next hb =>
            have hother := Child.prefixKey_ne_request hr er hc (by omega : bit width n.cidr addr ≠ 1)
              (e := e)
            have hchosen := ihl hl
            simp only [Tree.entries, List.mem_append]
            grind
          next hb =>
            have hother := Child.prefixKey_ne_request hl el hc hb (e := e)
            have hchosen := ihr hr
            simp only [Tree.entries, List.mem_append]
            grind
      next hstop =>
        have hg := graftable_of_stopped hv ha hstop
        have hnot := graft_prefix_absent hv ha hc hg fresh peer e
        have hp := (graft_entries width fresh addr cidr peer (.node n l r)).mem_iff (a := e)
        rw [graft_binding]
        simpa only [List.mem_cons] using hp.trans (by grind)

theorem Tree.fork_nodeIds_perm (n : NodeData) (side : Nat) (chosen other : Tree) :
    (Tree.fork n side chosen other).nodeIds.Perm
      (n.id :: (chosen.nodeIds ++ other.nodeIds)) := by
  unfold Tree.fork
  split
  · exact List.Perm.refl _
  · exact List.perm_append_comm.cons _

theorem Tree.fork_replace_nodeIds {n : NodeData} {side : Nat} {old new other : Tree}
    {added : List Nat} (h : new.nodeIds.Perm (added ++ old.nodeIds)) :
    (Tree.fork n side new other).nodeIds.Perm
      (added ++ (Tree.fork n side old other).nodeIds) := by
  apply (Tree.fork_nodeIds_perm n side new other).trans
  apply ((h.append_right other.nodeIds).cons n.id).trans
  have hm : (n.id :: ((added ++ old.nodeIds) ++ other.nodeIds)).Perm
      (added ++ n.id :: (old.nodeIds ++ other.nodeIds)) := by
    simpa only [List.append_assoc] using (List.perm_middle
      (a := n.id) (l₁ := added) (l₂ := old.nodeIds ++ other.nodeIds)).symm
  exact hm.trans ((Tree.fork_nodeIds_perm n side old other).symm.append_left added)

theorem graft_nodeIds_perm (width fresh addr cidr peer : Nat) (down : Tree) :
    (graft width fresh addr cidr peer down).tree.nodeIds.Perm
      (List.range' fresh (graft width fresh addr cidr peer down).allocations ++ down.nodeIds) := by
  cases down with
  | empty => exact List.Perm.refl _
  | node n l r =>
      simp only [graft]
      split
      · simpa only [requestedNode, Tree.nodeIds, List.append_nil, List.range'_succ,
          List.range'_zero, List.cons_append, List.nil_append] using
          Tree.fork_nodeIds_perm (requestedNode fresh addr cidr peer) (bit width cidr n.addr)
            (.node n l r) .empty
      · have h := Tree.fork_nodeIds_perm
          (NodeData.mk (fresh + 1) addr (min cidr (common width n.addr addr)) none)
          (bit width (min cidr (common width n.addr addr)) n.addr) (.node n l r)
          (requestedLeaf fresh addr cidr peer)
        have hm := (List.perm_append_singleton fresh (Tree.node n l r).nodeIds).cons (fresh + 1)
        exact h.trans (hm.trans (List.Perm.swap _ _ _))

/-- Existing identifiers retain their multiplicity; the successful insertion
adds exactly its consecutive allocation interval. -/
theorem Tree.insertFresh_nodeIds_perm (t : Tree) (width fresh addr cidr peer : Nat) :
    (t.insertFresh width fresh addr cidr peer).tree.nodeIds.Perm
      (List.range' fresh (t.insertFresh width fresh addr cidr peer).allocations ++ t.nodeIds) := by
  induction t with
  | empty => exact List.Perm.refl _
  | node n l r ihl ihr =>
      rw [Tree.insertFresh]
      split
      · split
        · exact List.Perm.refl _
        · split
          · exact Tree.fork_replace_nodeIds (n := n) (side := 0) (other := r) ihl
          · exact Tree.fork_replace_nodeIds (n := n) (side := 1) (other := l) ihr
      · exact graft_nodeIds_perm _ _ _ _ _ _

theorem Tree.insertFresh_nodeIds {t : Tree} (width fresh addr cidr peer id : Nat) :
    id ∈ (t.insertFresh width fresh addr cidr peer).tree.nodeIds ↔
      id ∈ t.nodeIds ∨
        (fresh ≤ id ∧ id < fresh + (t.insertFresh width fresh addr cidr peer).allocations) := by
  rw [(Tree.insertFresh_nodeIds_perm t width fresh addr cidr peer).mem_iff]
  simp only [List.mem_append, List.mem_range'_1, or_comm]

theorem Tree.insertFresh_nodeIds_nodup {t : Tree} (hn : t.nodeIds.Nodup)
    (hf : ∀ id ∈ t.nodeIds, id < fresh) (width addr cidr peer : Nat) :
    (t.insertFresh width fresh addr cidr peer).tree.nodeIds.Nodup := by
  apply (Tree.insertFresh_nodeIds_perm t width fresh addr cidr peer).symm.nodup
  apply List.nodup_append.mpr
  refine ⟨List.nodup_range' _, hn, ?_⟩
  intro a ha b hb he
  obtain ⟨i, hi, hai⟩ := List.mem_range'.mp ha
  have := hf b hb
  omega

theorem Tree.insertFresh_nodeIds_bounded {t : Tree}
    (hf : ∀ id ∈ t.nodeIds, id < fresh) (width addr cidr peer : Nat) :
    ∀ id ∈ (t.insertFresh width fresh addr cidr peer).tree.nodeIds,
      id < fresh + (t.insertFresh width fresh addr cidr peer).allocations := by
  intro id hi
  rcases (Tree.insertFresh_nodeIds width fresh addr cidr peer id).mp hi with ho | hn
  · have := hf id ho
    omega
  · exact hn.2

/-- Longest-prefix lookup after insertion agrees with the old flat bindings
after replacing the requested canonical prefix with its new owner. -/
theorem Tree.insertFresh_lookup_spec {t : Tree} (hv : t.Valid width)
    (ha : addr < 2 ^ width) (hc : cidr ≤ width) (fresh peer key : Nat) :
    let result := t.insertFresh width fresh addr cidr peer
    Winner width key
      (result.binding :: t.entries.filter
        (fun e => e.prefixKey width != (cidr, prefixBits width cidr addr)))
      (result.tree.lookup width key) := by
  apply (Tree.lookup_spec (Tree.insertFresh_valid hv ha hc fresh peer) key).congr_entries
  intro e
  simpa using Tree.insertFresh_entries hv ha hc fresh peer e

end Leanux.Proofs.WG.AllowedIps
