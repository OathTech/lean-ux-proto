import Leanux.Kernel.Defs

/-!
# The IPv4 FIB trie: the C's functions (net/ipv4/fib_trie.c)

Lane C (docs/2026-10-15-design-c-fib-trie.md, section 3.2). Every function
mirrors its C counterpart's choice points in order, with the operands the
kernel records at them (the design note, 9.2). The trie lives in the kernel
state (`Kernel.fib4.trie`); a walk addresses a node by its path from the
root vector (the C's parent pointers read backwards), and the functions
that the C writes through a parent pointer (`put_child_root`, `resize`,
`collapse`) take the parent and return it updated, as the C returns `tp`.

Allocation outcomes are the environment's (`envOk`) in this landing: the
sites are `GFP_KERNEL` in task context (the design note, section 5) and
constant successes on the fixture; the record-only `AllocSite` entries that
make them exact when armed are the follow-on named in the C1 report.
-/

namespace Leanux.Net.Fib

open Leanux

/-- A node's address: the child indices from the root vector down. The root
    vector's one child is index 0 (`get_index` at the root, :221-229), so
    the trie's top node is `[0]`. -/
abbrev Path := List Nat

namespace KeyVector

/-- The subtree at `p` below `n`, without effects. -/
def nodeAt : KeyVector → Path → Option KeyVector
  | n, [] => some n
  | n, i :: rest => match n.child i with
    | some c => nodeAt c rest
    | none => none

/-- Replace the subtree at `p` below `n` by `c`, as the C's pointer
    assignment: no count or suffix update (those are `put_child`'s). -/
def setRaw : KeyVector → Path → Option KeyVector → KeyVector
  | n, [], _ => n
  | n, [i], c => n.withChildren (n.children.setIfInBounds i c)
  | n, i :: rest, c => match n.child i with
    | some ch => n.withChildren (n.children.setIfInBounds i (some (setRaw ch rest c)))
    | none => n

end KeyVector

namespace Trie

def nodeAt (t : Trie) (p : Path) : Option KeyVector := t.rootVector.nodeAt p

/-- The raw replacement of the node at `p` (`[0]` is the top node). -/
def setRaw (t : Trie) (p : Path) (c : Option KeyVector) : Trie :=
  match p with
  -- the root vector itself: its one child and its `slen`
  | [] => match c with
    | some v => { t with root := v.child 0, rootSlen := v.slen }
    | none => t
  | [0] => { t with root := c }
  | 0 :: rest => { t with root := t.root.map (·.setRaw rest c) }
  | _ => t

end Trie

/-- The IPv4 table of the namespace the current path addresses: the device
    namespace, or the creating namespace C while `World.fibCreatorNs` is set
    (the foreign-creator mode's socket paths and C's teardown). -/
def getTable : M Table := do
  let w ← get
  return if w.fibCreatorNs then w.fib4C else w.fib4
def modifyTable (f : Table → Table) : M Unit := do
  let w ← get
  if w.fibCreatorNs then set { w with fib4C := f w.fib4C }
  else set { w with fib4 := f w.fib4 }
/-- Run `act` with the creating namespace's table addressed (restored after). -/
def inCreatorNs (act : M α) : M α := do
  let was := (← get).fibCreatorNs
  modify fun w => { w with fibCreatorNs := true }
  let r ← act
  modify fun w => { w with fibCreatorNs := was }
  return r
/-- Run `act` in the namespace WireGuard's sockets bind in: C in the
    foreign-creator mode, else the device namespace. -/
def inSocketNs (act : M α) : M α := do
  if (← get).foreignCreator then inCreatorNs act else act

/-- The trie of the addressed namespace's one IPv4 table. -/
def getTrie : M Trie := return (← getTable).trie
def setTrie (t : Trie) : M Unit := modifyTable fun tb => { tb with trie := t }

def nodeAt (p : Path) : M KeyVector := do
  match (← getTrie).nodeAt p with
  | some n => return n
  | none => invariant s!"no trie node at {repr p}"

def setNode (p : Path) (n : Option KeyVector) : M Unit := do
  setTrie ((← getTrie).setRaw p n)

/-- `__fls(x)`: the index of the highest set bit (x > 0). -/
def fls (x : Nat) : Nat := Nat.log2 x

/-- `tnode_full(tn, n)` (:410-413): `n && (n->pos + n->bits) == tn->pos &&
    IS_TNODE(n)`, three decisions in the C's short-circuit order. -/
def tnodeFull (tn : KeyVector) (n : Option KeyVector) : M Bool := do
  if !(← branch .tfNonNull n.isSome) then return false
  let some c := n | invariant "tnode_full: unreachable"
  if !(← branchCmp .tfNoSkip (c.pos + c.bits == tn.pos) (c.pos + c.bits) tn.pos) then return false
  branch .tfTnode (c.bits != 0)

/-- `empty_child_inc` (:338-344): the `t_key` counter wraps at `2^32`. -/
def emptyChildInc (tn : KeyVector) : M KeyVector := do
  let e : Nat := (tn.emptyChildren + 1) % 2 ^ 32
  let wrapped ← branchCmp .eciWrap (e == 0) e 0
  return tn.withCounts e (if wrapped then (tn.fullChildren + 1) % 2 ^ 32 else tn.fullChildren)

/-- `empty_child_dec` (:346-352). -/
def emptyChildDec (tn : KeyVector) : M KeyVector := do
  let zero ← branchCmp .ecdWrap (tn.emptyChildren == 0) tn.emptyChildren 0
  let f := if zero then (tn.fullChildren + 2 ^ 32 - 1) % 2 ^ 32 else tn.fullChildren
  return tn.withCounts ((tn.emptyChildren + 2 ^ 32 - 1) % 2 ^ 32) f

/-- `put_child(tn, i, n)` (:418-445): the counts, the suffix and the slot. -/
def putChild (tn : KeyVector) (i : Nat) (n : Option KeyVector) : M KeyVector := do
  let chi := tn.child i
  let mut tn := tn
  -- `if (!n && chi) empty_child_inc(tn);`
  if ← branch .pcNull n.isNone then
    if ← branch .pcHad chi.isSome then tn ← emptyChildInc tn
  -- `if (n && !chi) empty_child_dec(tn);`
  if ← branch .pcHasNew n.isSome then
    if ← branch .pcWasEmpty chi.isNone then tn ← emptyChildDec tn
  let wasfull ← tnodeFull tn chi
  let isfull ← tnodeFull tn n
  -- `if (wasfull && !isfull) full--; else if (!wasfull && isfull) full++;`
  if ← branch .pcWasFull wasfull then
    if ← branch .pcNotIsFull !isfull then
      tn := tn.withCounts tn.emptyChildren ((tn.fullChildren + 2 ^ 32 - 1) % 2 ^ 32)
  else if ← branch .pcNotWasFull true then
    if ← branch .pcIsFull isfull then
      tn := tn.withCounts tn.emptyChildren ((tn.fullChildren + 1) % 2 ^ 32)
  -- `if (n && (tn->slen < n->slen)) tn->slen = n->slen;`
  if ← branch .pcHasN n.isSome then
    let some c := n | invariant "put_child: unreachable"
    if ← branchCmp .pcSlen (tn.slen < c.slen) tn.slen c.slen then tn := tn.withSlen c.slen
  return tn.withChildren (tn.children.setIfInBounds i n)

/-- `put_child_root(tp, key, n)` (:469-476): at the root vector a plain
    assignment of its one child, else `put_child` at `get_index`. -/
def putChildRoot (tp : KeyVector) (key : Nat) (n : Option KeyVector) : M KeyVector := do
  if ← branchCmp .pcrRoot tp.isTrie tp.pos KEYLENGTH then
    return tp.withChildren (tp.children.setIfInBounds 0 n)
  else putChild tp (KeyVector.getIndex key tp) n

/-- `tnode_alloc(bits)` (:321-336) and `tnode_new(key, pos, bits)` (:377-402):
    `none` on an allocation failure. The `vzalloc` arm (more than 511
    children) is out of reach on this fixture and stops. -/
def tnodeNew (key pos bits : Nat) : M (Option KeyVector) := do
  if bits == 0 || pos + bits > KEYLENGTH then invariant "tnode_new: bits or shift out of range (BUG_ON)"
  -- tnode_alloc: `bits > TNODE_VMALLOC_MAX` (never: 32 < 60), the size against PAGE_SIZE
  if ← branch .taBitsMax false then invariant "tnode_alloc: unreachable"
  let size := 8 * 2 ^ bits + 32   -- TNODE_SIZE(1 << bits): the header and the pointers
  if ← branch .taPage (size ≤ 4096) then
    if ← branch .tnAllocFail !(← envOk .fibTnodeAlloc) then return none
  else unsupported "a tnode of more than 511 children (vzalloc)"
  let shift := pos + bits
  let fullChildren := if ← branch .tnKeylength (bits == KEYLENGTH) then 1 else 0
  let emptyChildren := if bits == KEYLENGTH then 0 else 2 ^ bits
  let key' := if ← branch .tnShift (shift < KEYLENGTH) then (key >>> shift) <<< shift else 0
  return some (.tnode key' pos bits pos (Array.replicate (2 ^ bits) none) emptyChildren fullChildren true)

/-- `leaf_new(key, fa)` (:354-375). -/
def leafNew (key : Nat) (fa : FibAlias) : M (Option KeyVector) := do
  if ← branch .lnAllocFail !(← envOk .fibLeafAlloc) then return none
  return some (.leaf key fa.slen [fa])

/-- `update_suffix(tn)` (:709-743): the strided scan over the children. -/
def updateSuffix (tn : KeyVector) : M KeyVector := do
  let mut slen : Nat := tn.pos
  let slenMax : Nat := min (tn.pos + tn.bits - 1) tn.slen
  let mut i : Nat := 0
  let mut stride : Nat := 2
  for _ in [0:4097] do
    if !(← branch .usIterate (i < tn.childLength)) then break
    let n := tn.child i
    -- `if (!n || (n->slen <= slen)) continue;`
    let skip ← do
      if ← branch .usNull n.isNone then pure true
      else
        let some c := n | invariant "update_suffix: unreachable"
        branchCmp .usSlenLe (c.slen ≤ slen) c.slen slen
    if skip then
      i := i + stride
      continue
    let some c := n | invariant "update_suffix: unreachable"
    stride := stride <<< (c.slen - slen)
    slen := c.slen
    i := i &&& (0xffffffffffffffff - (stride - 1))   -- `i &= ~(stride - 1)`
    if ← branchCmp .usMax (slen ≥ slenMax) slen slenMax then break
    i := i + stride
  return tn.withSlen slen

/-- `should_inflate(tp, tn)` (:804-817). -/
def shouldInflate (tp tn : KeyVector) : M Bool := do
  let used0 : Nat := tn.childLength
  let threshold : Nat := used0 * (if tp.isTrie then 30 else 50)
  let used : Nat := used0 - tn.emptyChildren + tn.fullChildren
  if !(← branchCmp .siUsed (used > 1) used 1) then return false
  if !(← branchCmp .siPos (tn.pos != 0) tn.pos 0) then return false
  branchCmp .siRatio (50 * used ≥ threshold) (50 * used) threshold

/-- `should_halve(tp, tn)` (:819-831). -/
def shouldHalve (tp tn : KeyVector) : M Bool := do
  let used0 : Nat := tn.childLength
  let threshold : Nat := used0 * (if tp.isTrie then 15 else 25)
  let used : Nat := used0 - tn.emptyChildren
  if !(← branchCmp .shUsed (used > 1) used 1) then return false
  if !(← branchCmp .shBits (tn.bits > 1) tn.bits 1) then return false
  branchCmp .shRatio (100 * used < threshold) (100 * used) threshold

/-- `should_collapse(tn)` (:833-845): the outcome and `used`; the `used < 2`
    compare is recorded at the caller's line (`resize:906`, `.rszCollapse`). -/
def shouldCollapse (tn : KeyVector) : M (Bool × Nat) := do
  let mut used : Nat := tn.childLength - tn.emptyChildren
  if ← branchCmp .scKeylength (tn.bits == KEYLENGTH) tn.bits KEYLENGTH then
    if tn.fullChildren != 0 then used := used - KEY_MAX
  let r ← branch .scUsed (used < 2)
  return (r, used)

/-- `update_children(tn)` (:447-468): the parent pointers of the new node's
    children. A child created in this resize step (`fresh`) already names
    the new node and is recursed into; another is re-parented. The mirror
    carries no parent pointer, so the effect is the decisions and the
    recursion; the marks are cleared when the step ends. -/
def updateChildren : Nat → KeyVector → M Unit
  | 0, _ => budgetExhausted "update_children"
  | fuel + 1, tn => do
    let mut i : Nat := tn.childLength
    for _ in [0:4097] do
      if !(← branch .ucIterate (i != 0)) then break
      i := i - 1
      let inode := tn.child i
      if ← branch .ucNull inode.isNone then continue
      let some c := inode | invariant "update_children: unreachable"
      if ← branch .ucParentIs c.fresh then updateChildren fuel c
      -- else `node_set_parent(inode, tn)`: no mirror state

/-- `tnode_free(tn)` (:490-506): the `call_rcu` frees of a step's old nodes
    and the global memory threshold, neither observable; `count` nodes. -/
def tnodeFree (count : Nat) : M Unit := do
  for _ in [0:count] do
    _ ← branch .tfrLoop true
  _ ← branch .tfrLoop false
  if ← branch .tfrSync false then invariant "tnode_free: the global sync threshold (never in a trace)"

/-- Clear the `fresh` marks of a subtree's new nodes once the step is over. -/
def clearFresh : Nat → KeyVector → KeyVector
  | 0, n => n
  | fuel + 1, n => match n with
    | .leaf .. => n
    | .tnode k p b s c e f _ => .tnode k p b s (c.map (·.map (clearFresh fuel))) e f false

/-- The recursion of `resize` through `replace` into a node's children is
    bounded by the trie's depth and `MAX_WORK`; the fuel is the bound. -/
abbrev RESIZE_FUEL : Nat := 3 * (2 * KEYLENGTH + 8)

mutual

/-- `resize(t, tn)` (:848-911) on the child `cindex` of `tp`: returns the
    parent, updated as the C's pointer writes update it. -/
def resizeAt : Nat → KeyVector → Nat → M KeyVector
  | 0, _, _ => budgetExhausted "resize"
  | fuel + 1, tp, cindex => do
  let some tn0 := tp.child cindex | invariant "resize: no node at cindex"
  let mut tp := tp
  let mut tn := tn0
  let mut maxWork : Nat := 10
  -- `while (should_inflate(tp, tn) && max_work)`
  for _ in [0:11] do
    if !(← shouldInflate tp tn) then break
    if !(← branch .rszInflateWork (maxWork != 0)) then break
    match ← inflate fuel tp cindex tn with
    | none =>
      _ ← branch .rszInflateFailed true
      break
    | some tp' =>
      _ ← branch .rszInflateFailed false
      tp := tp'
      maxWork := maxWork - 1
      let some tn' := tp.child cindex | invariant "resize: the inflated node is gone"
      tn := tn'
  -- `tp = node_parent(tn)`: tp already names the current parent
  if ← branchCmp .rszInflated (maxWork != 10) maxWork 10 then return tp
  for _ in [0:11] do
    if !(← shouldHalve tp tn) then break
    if !(← branch .rszHalveWork (maxWork != 0)) then break
    match ← halve fuel tp cindex tn with
    | none =>
      _ ← branch .rszHalveFailed true
      break
    | some tp' =>
      _ ← branch .rszHalveFailed false
      tp := tp'
      maxWork := maxWork - 1
      let some tn' := tp.child cindex | invariant "resize: the halved node is gone"
      tn := tn'
  let (sc, used) ← shouldCollapse tn
  if ← branchCmp .rszCollapse sc used 2 then collapse tp cindex tn
  else return tp

/-- `replace(t, oldtnode, tn)` (:508-535): link the new node in the old one's
    place, `update_children`, free the old nodes, then resize every full
    child of the new node. `freed` counts the nodes of the old node's free
    list (the old node and the full children it absorbed). -/
def replace : Nat → KeyVector → Nat → KeyVector → KeyVector → Nat → M KeyVector
  | 0, _, _, _, _, _ => budgetExhausted "replace"
  | fuel + 1, tp, cindex, old, tn, freed => do
  let tp ← putChildRoot tp tn.key (some tn)
  updateChildren (KEYLENGTH + 2) tn
  tnodeFree freed
  let mut tn := tn
  let mut i : Nat := tn.childLength
  for _ in [0:4097] do
    if !(← branch .replIterate (i != 0)) then break
    i := i - 1
    let inode := tn.child i
    if ← branch .replFull (← tnodeFull tn inode) then
      tn ← resizeAt fuel tn i
  let _ := old
  -- the resized children are in `tn`; the parent holds `tn` by its slot
  return tp.withChildren (tp.children.setIfInBounds cindex (some (clearFresh (KEYLENGTH + 2) tn)))

/-- `inflate(t, oldtnode)` (:537-631): `none` on an allocation failure
    (`tnode_free(tn)` frees what was allocated; the C returns NULL). -/
def inflate : Nat → KeyVector → Nat → KeyVector → M (Option KeyVector)
  | 0, _, _, _ => budgetExhausted "inflate"
  | fuel + 1, tp, cindex, old => do
  let some tn0 ← tnodeNew old.key (old.pos - 1) (old.bits + 1) | do
    _ ← branch .inflNoTnode true
    return none
  _ ← branch .inflNoTnode false
  let mut tn := tn0
  let m : Nat := (1 <<< tn.pos) % 2 ^ 32
  let mut i : Nat := old.childLength
  let mut freed := 1      -- oldtnode itself (tnode_free_init)
  let mut allocated := 0  -- the nodes on tn's free list, freed on nomem
  for _ in [0:4097] do
    if !(← branch .inflIterate (i != 0)) then break
    i := i - 1
    let inode := old.child i
    if ← branch .inflNull inode.isNone then continue
    let some c := inode | invariant "inflate: unreachable"
    if ← branch .inflNotFull !(← tnodeFull old (some c)) then
      tn ← putChild tn (KeyVector.getIndex c.key tn) (some c)
      continue
    -- `tnode_free_append(oldtnode, inode)`: the full child goes with the old node
    freed := freed + 1
    if ← branch .inflBits1 (c.bits == 1) then
      tn ← putChild tn (2 * i + 1) (c.child 1)
      tn ← putChild tn (2 * i) (c.child 0)
      continue
    let node1? ← tnodeNew (c.key ||| m) c.pos (c.bits - 1)
    if ← branch .inflNode1Fail node1?.isNone then
      tnodeFree allocated
      return none
    let some node1 := node1? | invariant "inflate: unreachable"
    let node0? ← tnodeNew c.key c.pos (c.bits - 1)
    allocated := allocated + 1   -- tnode_free_append(tn, node1)
    if ← branch .inflNode0Fail node0?.isNone then
      tnodeFree allocated
      return none
    let some node0 := node0? | invariant "inflate: unreachable"
    allocated := allocated + 1   -- tnode_free_append(tn, node0)
    -- `for (k = child_length(inode), j = k / 2; j;)`: the children split
    let mut node0 := node0
    let mut node1 := node1
    let mut k := c.childLength
    let mut j := k / 2
    for _ in [0:4097] do
      if !(← branch .inflSplit (j != 0)) then break
      j := j - 1; k := k - 1
      node1 ← putChild node1 j (c.child k)
      node0 ← putChild node0 j (c.child j)
      j := j - 1; k := k - 1
      node1 ← putChild node1 j (c.child k)
      node0 ← putChild node0 j (c.child j)
    tn ← putChild tn (2 * i + 1) (some node1)
    tn ← putChild tn (2 * i) (some node0)
  return some (← replace fuel tp cindex old tn freed)

/-- `halve(t, oldtnode)` (:633-686). -/
def halve : Nat → KeyVector → Nat → KeyVector → M (Option KeyVector)
  | 0, _, _, _ => budgetExhausted "halve"
  | fuel + 1, tp, cindex, old => do
  let some tn0 ← tnodeNew old.key (old.pos + 1) (old.bits - 1) | do
    _ ← branch .hvNoTnode true
    return none
  _ ← branch .hvNoTnode false
  let mut tn := tn0
  let mut i : Nat := old.childLength
  let mut allocated : Nat := 0
  for _ in [0:4097] do
    if !(← branch .hvIterate (i != 0)) then break
    i := i - 1
    let node1 := old.child i
    i := i - 1
    let node0 := old.child i
    -- `if (!node1 || !node0) { put_child(tn, i / 2, node1 ? : node0); continue; }`
    if ← branch .hvOneEmpty (node1.isNone || node0.isNone) then
      tn ← putChild tn (i / 2) (node1 <|> node0)
      continue
    let some n0 := node0 | invariant "halve: unreachable"
    let inode? ← tnodeNew n0.key old.pos 1
    if ← branch .hvNoInode inode?.isNone then
      tnodeFree allocated
      return none
    let some inode := inode? | invariant "halve: unreachable"
    allocated := allocated + 1
    let inode ← putChild inode 1 node1
    let inode ← putChild inode 0 node0
    tn ← putChild tn (i / 2) (some inode)
  return some (← replace fuel tp cindex old tn 1)

/-- `collapse(t, oldtnode)` (:688-707): the one remaining child takes the
    node's slot in the parent; `node_free` of the old node is a `call_rcu`. -/
def collapse (tp : KeyVector) (cindex : Nat) (old : KeyVector) : M KeyVector := do
  let mut n : Option KeyVector := none
  let mut i : Nat := old.childLength
  for _ in [0:4097] do
    -- `for (n = NULL, i = child_length(oldtnode); !n && i;)`
    if !(← branch .collNull n.isNone) then break
    if !(← branchCmp .collIndex (i != 0) i 0) then break
    i := i - 1
    n := old.child i
  let _ := cindex
  putChildRoot tp old.key n

end

/-- `trie_rebalance(t, tn)` (:1104-1108): resize the node at `p` and every
    ancestor up to the root's child, each within its parent. -/
def trieRebalance (p : Path) : M Unit := do
  let mut path := p
  for _ in [0:KEYLENGTH + 2] do
    -- `while (!IS_TRIE(tn))`: the node at `path`, the root vector at `[]`
    let tn ← nodeAt path
    if ← branchCmp .trbLoop (!tn.isTrie) tn.pos KEYLENGTH then
      match path.getLast?, path.dropLast with
      | some cindex, parentPath =>
        let parent ← nodeAt parentPath
        let parent' ← resizeAt RESIZE_FUEL parent cindex
        setNode parentPath (some parent')
        path := parentPath
      | none, _ => invariant "trie_rebalance: a non-root node without a parent"
    else break

/-- `node_push_suffix(tn, slen)` (:927-933) from the node at `p` upward. -/
def nodePushSuffix (p : Path) (slen : Nat) : M Unit := do
  let mut path := p
  for _ in [0:KEYLENGTH + 2] do
    let tn ← nodeAt path
    if !(← branchCmp .nphLoop (tn.slen < slen) tn.slen slen) then break
    setNode path (some (tn.withSlen slen))
    if path.isEmpty then break
    path := path.dropLast

/-- `node_pull_suffix(tn, slen)` (:913-925) from the node at `p` upward. -/
def nodePullSuffix (p : Path) (slen0 : Nat) : M Unit := do
  let mut path := p
  let mut slen : Nat := slen0
  let mut tn ← nodeAt path
  let mut nodeSlen : Nat := tn.slen
  for _ in [0:KEYLENGTH + 2] do
    if !(← branchCmp .npsSlenGtPos (nodeSlen > tn.pos) nodeSlen tn.pos) then break
    -- at the 1647 site (`slen = tp->pos`) the compiler folds this compare into the first
    if !(← branch .npsSlenGt (nodeSlen > slen)) then break
    let tn' ← updateSuffix tn
    setNode path (some tn')
    slen := tn'.slen
    if ← branchCmp .npsSame (nodeSlen == slen) nodeSlen slen then break
    if path.isEmpty then break
    path := path.dropLast
    tn ← nodeAt path
    nodeSlen := tn.slen

/-- `fib_find_node(t, &tp, key)` (:936-976): the leaf for `key` with the
    path of its parent, or `none` with the parent where the walk stopped. -/
def findNode (key : Nat) : M (Path × Option (Path × KeyVector)) := do
  let t ← getTrie
  let mut pnPath : Path := []
  let mut pn := t.rootVector
  let mut index : Nat := 0
  let mut found : Option (Path × KeyVector) := none
  for _ in [0:KEYLENGTH + 2] do
    let nPath := pnPath ++ [index]
    let n := pn.child index
    if ← branch .ffnNull n.isNone then break
    let some c := n | invariant "fib_find_node: unreachable"
    index := KeyVector.getCindex key c
    if ← branchCmp .ffnIndexMismatch (index ≥ 2 ^ c.bits) index (2 ^ c.bits) then break
    if !(← branchCmp .ffnTnode (c.bits != 0) c.bits 0) then
      found := some (nPath, c)
      break
    pnPath := nPath
    pn := c
  return (pnPath, found)

/-- `fib_find_alias(fah, slen, dscp, prio, tb_id, find_first)` (:983-1013):
    the index of the alias in the leaf's list, or `none`. -/
def findAlias (aliases : Option (List FibAlias)) (slen dscp prio tbId : Nat) (findFirst : Bool)
    : M (Option Nat) := do
  if ← branch .ffaNull aliases.isNone then return none
  let some fas := aliases | invariant "fib_find_alias: unreachable"
  let mut i : Nat := 0
  for fa in fas do
    _ ← branch .ffaIterate true
    if ← branchCmp .ffaSlenLess (fa.slen < slen) fa.slen slen then i := i + 1; continue
    if ← branchCmp .ffaSlenNe (fa.slen != slen) fa.slen slen then return none
    if ← branchCmp .ffaTbGreater (fa.tbId > tbId) fa.tbId tbId then i := i + 1; continue
    if ← branchCmp .ffaTbNe (fa.tbId != tbId) fa.tbId tbId then return none
    if ← branchCmp .ffaFindFirst findFirst (if findFirst then 1 else 0) 0 then return some i
    if ← branchCmp .ffaDscpGreater (fa.dscp > dscp) fa.dscp dscp then i := i + 1; continue
    let infoPrio : Nat := ((← getTable).infos.get? fa.info).map (·.priority) |>.getD 0
    if ← branchCmp .ffaPrio (infoPrio ≥ prio) infoPrio prio then return some i
    if ← branchCmp .ffaDscpLess (fa.dscp < dscp) fa.dscp dscp then return some i
    i := i + 1
  _ ← branch .ffaIterate false
  return none

/-- `fib_insert_node(t, tp, new, key)` (:1110-1158): `tpPath` names the parent
    `fib_find_node` returned. -/
def insertNode (tpPath : Path) (fa : FibAlias) (key : Nat) : M Int := do
  let l? ← leafNew key fa
  if ← branch .finNoLeaf l?.isNone then return -12   -- -ENOMEM
  let some l := l? | invariant "fib_insert_node: unreachable"
  let tp ← nodeAt tpPath
  let slot := KeyVector.getIndex key tp
  let n := tp.child slot
  let mut leafParent := tpPath
  if ← branch .finSlotTaken n.isSome then
    let some c := n | invariant "fib_insert_node: unreachable"
    let tn? ← tnodeNew key (fls (key ^^^ c.key)) 1
    if ← branch .finNoTnode tn?.isNone then return -12   -- node_free(l)
    let some tn := tn? | invariant "fib_insert_node: unreachable"
    -- `put_child(tn, get_index(key, tn) ^ 1, n)`
    let tn ← putChild tn ((KeyVector.getIndex key tn) ^^^ 1) (some c)
    -- `put_child_root(tp, key, tn)`
    let tp' ← putChildRoot tp key (some tn)
    setNode tpPath (some tp')
    leafParent := tpPath ++ [slot]
  -- `node_push_suffix(tp, new->fa_slen)`
  nodePushSuffix leafParent fa.slen
  -- `put_child_root(tp, key, l)`
  let tp ← nodeAt leafParent
  let tp' ← putChildRoot tp key (some l)
  setNode leafParent (some tp')
  trieRebalance leafParent
  -- the step's `fresh` marks end with it
  setTrie { (← getTrie) with root := (← getTrie).root.map (clearFresh (KEYLENGTH + 2)) }
  return 0

/-- `fib_insert_alias(t, tp, l, new, fa, key)` (:1160-1194): `l` is the
    leaf's path when it exists, `before` the index `fib_find_alias` gave. -/
def insertAlias (tpPath : Path) (l : Option Path) (new : FibAlias) (before : Option Nat) (key : Nat)
    : M Int := do
  if ← branch .fiaNoLeaf l.isNone then return ← insertNode tpPath new key
  let some lPath := l | invariant "fib_insert_alias: unreachable"
  let leaf ← nodeAt lPath
  let fas := leaf.aliases
  let mut fas' := fas
  if ← branch .fiaBefore before.isSome then
    let some b := before | invariant "fib_insert_alias: unreachable"
    fas' := fas.take b ++ [new] ++ fas.drop b
  else
    -- the placement loop: after the last alias with a smaller or equal
    -- `slen` and, at equal `slen`, a not-smaller `tb_id`
    let mut fa : Option Nat := none
    let mut i : Nat := 0
    let mut stopped := false
    for last in fas do
      _ ← branch .fiaIterate true
      if ← branch .fiaSlenLess (new.slen < last.slen) then stopped := true; break
      if ← branch .fiaSlenEq (new.slen == last.slen) then
        if ← branch .fiaTbGreater (new.tbId > last.tbId) then stopped := true; break
      fa := some i
      i := i + 1
    if !stopped then _ ← branch .fiaIterate false
    if ← branch .fiaFound fa.isSome then
      let some b := fa | invariant "fib_insert_alias: unreachable"
      fas' := fas.take (b + 1) ++ [new] ++ fas.drop (b + 1)   -- hlist_add_behind
    else
      fas' := new :: fas   -- hlist_add_head
  let mut leaf' := leaf.withAliases fas'
  -- `if (l->slen < new->fa_slen) { l->slen = new->fa_slen; node_push_suffix(tp, new->fa_slen); }`
  if ← branch .fiaSuffix (leaf.slen < new.slen) then
    leaf' := leaf'.withSlen new.slen
    setNode lPath (some leaf')
    nodePushSuffix tpPath new.slen
  else
    setNode lPath (some leaf')
  return 0

/-- `fib_remove_alias(t, tp, l, old)` (:1632-1661): `index` is the alias's
    position in the leaf at `lPath`. -/
def removeAlias (tpPath lPath : Path) (index : Nat) : M Unit := do
  let leaf ← nodeAt lPath
  let fas := leaf.aliases
  let rest := fas.take index ++ fas.drop (index + 1)
  let leaf' := leaf.withAliases rest
  setNode lPath (some leaf')
  if ← branch .fraEmpty rest.isEmpty then
    let tp ← nodeAt tpPath
    if ← branchCmp .fraSuffixEq (tp.slen == leaf.slen) tp.slen leaf.slen then
      nodePullSuffix tpPath tp.pos
    let tp ← nodeAt tpPath
    let tp' ← putChildRoot tp leaf.key none
    setNode tpPath (some tp')
    trieRebalance tpPath
    setTrie { (← getTrie) with root := (← getTrie).root.map (clearFresh (KEYLENGTH + 2)) }
    return
  -- `if (*pprev) return;`: the removed alias was not the list's last
  if ← branch .fraLast (index < rest.length) then return
  -- the leaf's `slen` follows its new last alias
  let some last := rest.getLast? | invariant "fib_remove_alias: unreachable"
  setNode lPath (some (leaf'.withSlen last.slen))
  nodePullSuffix tpPath last.slen

/-- The flow of a lookup: `flowi4_daddr` (host order), `flowi4_scope`,
    `flowi4_oif`, `flowi4_tos`, and the lookup flags. -/
structure Flow where
  daddr : Nat
  scope : Nat := RT_SCOPE_UNIVERSE
  oif : Nat := 0
  dscp : Nat := 0
  /-- `FIB_LOOKUP_NOREF` (always set by `fib_lookup`, ip_fib.h:324). -/
  noref : Bool := true
  /-- `FIB_LOOKUP_IGNORE_LINKSTATE`. -/
  ignoreLinkstate : Bool := false
  deriving Repr, Inhabited

/-- `struct fib_result`: what the lookup fills (:1606-1615). -/
structure Result where
  prefixKey : Nat
  prefixlen : Nat
  type : RouteType
  scope : Nat
  dscp : Nat
  info : FibInfoId
  tbId : Nat
  /-- The leaf's path and the alias's index: `res->fa_head` and the alias
      whose `FA_S_ACCESSED` bit the lookup set. -/
  leaf : Path
  alias : Nat
  deriving Repr, Inhabited

/-- `fib_lookup_good_nhc(nhc, fib_flags, flp)` (:1409-1423). The
    `ignore_routes_with_linkdown` sysctl is 0 on the fixture, so the
    `ip_ignore_linkdown` operand is false at once. -/
def lookupGoodNhc (fi : FibInfo) (flow : Flow) : M Bool := do
  if ← branchCmp .nhcDead (fi.nhFlags &&& RTNH_F_DEAD != 0) (fi.nhFlags &&& RTNH_F_DEAD) 0 then return false
  if ← branch .nhcIgnoreLinkdown false then
    if ← branch .nhcLinkdownFlag (fi.nhFlags &&& RTNH_F_LINKDOWN != 0) then
      if ← branch .nhcLinkstate !flow.ignoreLinkstate then return false
  if ← branchCmp .nhcOif (flow.oif != 0) flow.oif 0 then
    if ← branch .nhcOifMismatch (flow.oif != fi.oif) then return false
  return true

/-- `fib_table_lookup(tb, flp, res, fib_flags)` (:1426-1629): the result or
    the negative errno (`-EAGAIN` for no route, a type's error), and the
    accessed alias's `FA_S_ACCESSED` write applied to the trie. -/
def tableLookup (flow : Flow) : M (Except Int Result) := do
  let t ← getTrie
  let key := flow.daddr
  -- `pn = t->kv; cindex = 0; n = get_child_rcu(pn, cindex);`
  let mut pnPath : Path := []
  let mut pn := t.rootVector
  let mut cindex : Nat := 0
  let mut nPath : Path := [0]
  let n0 := pn.child 0
  if ← branch .ftlEmptyTrie n0.isNone then return .error (-11)   -- -EAGAIN
  let some first := n0 | invariant "fib_table_lookup: unreachable"
  let mut n := first
  let mut index : Nat := 0
  -- Step 1: travel to the longest prefix match
  let mut leafFound := false
  let mut backtrace := false
  for _ in [0:KEYLENGTH + 2] do
    index := KeyVector.getCindex key n
    if ← branchCmp .ftlIndexMismatch (index ≥ 2 ^ n.bits) index (2 ^ n.bits) then break
    if ← branchCmp .ftlLeaf (n.bits == 0) n.bits 0 then leafFound := true; break
    if ← branchCmp .ftlSlenGtPos (n.slen > n.pos) n.slen n.pos then
      pnPath := nPath
      pn := n
      cindex := index
    let child := n.child index
    if ← branch .ftlNullChild child.isNone then backtrace := true; break
    let some c := child | invariant "fib_table_lookup: unreachable"
    n := c
    nPath := nPath ++ [index]
  -- Step 2 and 3, with the backtrace
  let mut result : Option (Except Int Result) := none
  let mut leafPath := nPath
  for _ in [0:4 * KEYLENGTH + 8] do
    if result.isSome then break
    if !leafFound then
      -- Step 2: at `n`, unless we arrived by backtrace
      let mut toBacktrace := backtrace
      backtrace := false
      if !toBacktrace then
        let mism := KeyVector.prefixMismatch key n
        let m ← branchCmp .ftlPrefixMismatch (mism != 0) mism 0
        if m then toBacktrace := true
        else if ← branchCmp .ftlSlenEqPos (n.slen == n.pos) n.slen n.pos then toBacktrace := true
        else if ← branchCmp .ftlStep2Leaf (n.bits == 0) n.bits 0 then
          leafFound := true
          leafPath := nPath
      if !leafFound then
        -- `while ((n = rcu_dereference(*cptr)) == NULL)`, entered directly
        -- by `goto backtrace`
        let mut cptr := 0
        let mut cptrFrom := nPath   -- the node whose child `cptr` names
        let mut haveChild := false
        if !toBacktrace then
          let child := n.child 0
          if ← branch .ftlChildNull child.isNone then toBacktrace := true
          else
            let some c := child | invariant "fib_table_lookup: unreachable"
            n := c; nPath := nPath ++ [0]; haveChild := true
        for _ in [0:4 * KEYLENGTH + 8] do
          if haveChild then break
          -- backtrace: climb while cindex is 0
          let mut climbed := false
          for _ in [0:KEYLENGTH + 2] do
            if !(← branchCmp .ftlBacktraceAscend (cindex == 0) cindex 0) then break
            let pkey := pn.key
            if ← branchCmp .ftlRoot pn.isTrie pn.pos KEYLENGTH then
              result := some (.error (-11))
              climbed := true
              break
            pnPath := pnPath.dropLast
            pn ← nodeAt pnPath
            cindex := KeyVector.getIndex pkey pn
          if result.isSome then break
          let _ := climbed
          -- `cindex &= cindex - 1; cptr = &pn->tnode[cindex];`
          cindex := cindex &&& (cindex - 1)
          cptr := cindex
          cptrFrom := pnPath
          let child := pn.child cptr
          if ← branch .ftlChildNull child.isNone then continue
          let some c := child | invariant "fib_table_lookup: unreachable"
          n := c; nPath := cptrFrom ++ [cptr]; haveChild := true
        if result.isSome then break
        continue
    -- Step 3: process the leaf at `n`
    leafFound := false
    index := key ^^^ n.key
    let fas := n.aliases
    let mut i : Nat := 0
    let mut matched := false
    for fa in fas do
      _ ← branch .ftlAliasIterate true
      -- `if (index >= (1ul << fa->fa_slen)) continue;`
      if ← branchCmp .ftlAliasSuffix (index ≥ 2 ^ fa.slen) index (2 ^ fa.slen) then i := i + 1; continue
      if ← branchCmp .ftlAliasDscp (fa.dscp != 0) fa.dscp 0 then
        if ← branch .ftlDscpMismatch (fa.dscp != flow.dscp) then i := i + 1; continue
      let some fi := (← getTable).infos.get? fa.info | invariant "fib_table_lookup: an alias without its info"
      if ← branchCmp .ftlInfoDead fi.dead (if fi.dead then 1 else 0) 0 then i := i + 1; continue
      if ← branchCmp .ftlScope (fi.scope < flow.scope) fi.scope flow.scope then i := i + 1; continue
      -- `fib_alias_accessed(fa)`: `if (!(fa->fa_state & FA_S_ACCESSED)) fa->fa_state |= FA_S_ACCESSED;`
      if ← branch .ftlNotAccessed (!fa.accessed) then
        let leaf ← nodeAt leafPath
        let fas' := leaf.aliases.set i { fa with accessed := true }
        setNode leafPath (some (leaf.withAliases fas'))
      let err : Int := fa.type.error
      if ← branchCmp .ftlErrorType (err < 0) err 0 then
        result := some (.error err); matched := true; break
      if ← branchCmp .ftlInfoFlagsDead (fi.flags &&& RTNH_F_DEAD != 0) (fi.flags &&& RTNH_F_DEAD) 0 then
        i := i + 1; continue
      if ← branch .ftlNhObject false then invariant "fib_table_lookup: a nexthop object (CONFIG_NEXTHOP ids are not used)"
      -- `for (nhsel = 0; nhsel < fib_info_num_path(fi); nhsel++)`: one path
      let mut nhsel : Nat := 0
      let mut set := false
      for _ in [0:2] do
        if !(← branchCmp .ftlNhIterate (nhsel < 1) nhsel 1) then break
        let good ← lookupGoodNhc fi flow
        if ← branchCmp .ftlNhGood (!good) (if good then 1 else 0) 0 then nhsel := nhsel + 1; continue
        -- set_result
        let noref : Nat := if flow.noref then 1 else 0
        if ← branchCmp .ftlNoref (noref == 0) noref 0 then pure ()   -- refcount_inc(&fi->fib_clntref)
        result := some (.ok { prefixKey := n.key, prefixlen := KEYLENGTH - fa.slen, type := fa.type,
                              scope := fi.scope, dscp := fa.dscp, info := fa.info, tbId := fa.tbId,
                              leaf := leafPath, alias := i })
        set := true
        break
      if set then matched := true; break
      i := i + 1
    if matched then break
    _ ← branch .ftlAliasIterate false
    -- miss: `goto backtrace`
    backtrace := true
  match result with
  | some r => return r
  | none => budgetExhausted "fib_table_lookup"

end Leanux.Net.Fib
