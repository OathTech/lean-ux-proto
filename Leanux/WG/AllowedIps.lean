import Leanux.WG.State

/-!
# drivers/net/wireguard/allowedips.c — the cryptokey-routing trie

`swap_endian` turns an address into the integer the trie stores (big-endian
value), and `choose(node, key)`'s byte/bit arithmetic selects bit
`bitlen - 1 - cidr` of that integer; `common_bits` counts leading equal bits
(`bitlen - fls(xor)`). Nodes live in an identity-keyed store; a node's
`parent_bit_packed` is `Slot`. Nodes handed to `call_rcu` are removed from the
store at once (a cut point: they are unreachable). List heads are ordered
lists of node identities (`peer->allowedips_list`).
-/

namespace Leanux.WG
open Leanux

/-- `fls(x)`: the 1-based position of the most significant set bit, 0 for 0. -/
def fls (x : Nat) : Nat := if x == 0 then 0 else Nat.log2 x + 1

/-- choose (allowedips.c:36-39). -/
def choose (node : AipNode) (key : Nat) : M Nat := do
  if node.cidr ≥ node.bitlen then invariant "choose on a full-length node"
  return key / 2 ^ (node.bitlen - 1 - node.cidr) % 2

/-- common_bits (allowedips.c:87-97), with `fls128` (82-85) for 128 bits. -/
def commonBits (node : AipNode) (key : Nat) (bits : Nat) : M Nat := do
  if ← branch .commonBits32 (bits == 32) then
    return 32 - fls (node.bits ^^^ key)
  if ← branch .commonBits128 (bits == 128) then
    let x := node.bits ^^^ key
    let high := x / 2 ^ 64
    let n ← do
      if ← branch .fls128High (high != 0) then pure (fls high + 64) else pure (fls (x % 2 ^ 64))
    return 128 - n
  return 0

/-- prefix_matches (allowedips.c:99-109). -/
def prefixMatches (node : AipNode) (key bits : Nat) : M Bool := do
  let common ← commonBits node key bits
  return common ≥ node.cidr

/-- find_node (allowedips.c:111-124): the deepest node on the key's path
    that has a peer. -/
def findNode (trie : Option NodeId) (bits key : Nat) : M (Option NodeId) := do
  let mut node := trie
  let mut found : Option NodeId := none
  for _ in [0:130] do   -- MAX_ALLOWEDIPS_DEPTH bounds the path
    -- while (node && prefix_matches(node, key, bits))
    let id ← match node with
      | none => do _ ← branch .findNodeNode false; return found
      | some id => do _ ← branch .findNodeNode true; pure id
    let n ← getNode id
    if !(← branch .findNodePrefixMatches (← prefixMatches n key bits)) then return found
    if ← branch .findNodeHasPeer n.peer.isSome then found := some id
    if ← branch .findNodeFullLength (n.cidr == bits) then return found
    node ← n.bitAt (← choose n key)
  invariant "find_node deeper than MAX_ALLOWEDIPS_DEPTH"

/-- copy_and_assign_cidr (allowedips.c:23-34): the key is copied unmasked. -/
def newNode (key cidr bits : Nat) (peer : Option PeerId) : AipNode :=
  { peer, bit := #[none, none], cidr, bitlen := bits, bits := key, parent := .root4 }

/-- connect_node (allowedips.c:169-173). -/
def connectNode (slot : Slot) (id : NodeId) : M Unit := do
  setNode id { (← getNode id) with parent := slot }
  slotSet slot (some id)

/-- choose_and_connect_node (allowedips.c:175-179). -/
def chooseAndConnectNode (parent node : NodeId) : M Unit := do
  let bit ← choose (← getNode parent) (← getNode node).bits
  connectNode (.child parent bit) node

/-- A zeroed allocation from `node_cache` at one of `add`'s three
    `kmem_cache_zalloc` calls (`site`: allowedips.c:190, :205 or :234), an
    allocation outcome. -/
def allocNode (site : AllocSite) (n : AipNode) : M (Option NodeId) := do
  if !(← hiddenAlloc site) then return none   -- kmem_cache_zalloc(node_cache)
  let id := (← getDev).nextNode
  modifyDev fun d => { d with nextNode := id + 1, nodes := d.nodes.insert id n }
  return some id

def listRemove (l : List NodeId) (id : NodeId) : List NodeId := l.filter (· != id)

/-- `list_add_tail(&node->peer_list, &peer->allowedips_list)`. -/
def listAddTail (peer : PeerId) (id : NodeId) : M Unit := do
  let p ← getPeer peer
  setPeer peer { p with allowedipsList := p.allowedipsList ++ [id] }

/-- `list_del(&node->peer_list)` from whichever peer's list holds it. -/
def listDel (id : NodeId) : M Unit := do
  for (pid, p) in (← getDev).peers.toList do
    if p.allowedipsList.contains id then
      setPeer pid { p with allowedipsList := listRemove p.allowedipsList id }

/-- node_placement (allowedips.c:149-167): the deepest node on the key's path
    whose prefix covers `cidr`, and whether it is exact. -/
def nodePlacement (trie : Option NodeId) (key cidr bits : Nat) : M (Option NodeId × Bool) := do
  let mut node := trie
  let mut parent : Option NodeId := none
  for _ in [0:130] do   -- MAX_ALLOWEDIPS_DEPTH bounds the path
    -- while (node && node->cidr <= cidr && prefix_matches(node, key, bits))
    let id ← match node with
      | none => do _ ← branch .placementNode false; return (parent, false)
      | some id => do _ ← branch .placementNode true; pure id
    let n ← getNode id
    if !(← branchCmp .placementCidrLe (n.cidr ≤ cidr) n.cidr cidr) then return (parent, false)
    if !(← branch .placementPrefixMatches (← prefixMatches n key bits)) then return (parent, false)
    parent := some id
    if ← branchCmp .placementExact (n.cidr == cidr) n.cidr cidr then return (parent, true)
    node ← n.bitAt (← choose n key)
  invariant "node_placement deeper than MAX_ALLOWEDIPS_DEPTH"

/-- add (allowedips.c:181-250). -/
def add (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) : M Int := do
  -- `unlikely(cidr > bits || !peer)`
  if ← branchCmp .addCidrTooLong (cidr > bits) cidr bits then return -EINVAL
  if ← branch .addNoPeer peer.isNone then return -EINVAL
  let some pid := peer | invariant "unreachable"
  let trie ← slotGet root
  if ← branch .addEmptyTrie trie.isNone then
    let some id ← (do
        let r ← allocNode .allocNode190 (newNode key cidr bits (some pid))
        if ← branch .addRootNoMem r.isNone then return none
        pure r) | return -ENOMEM
    listAddTail pid id
    connectNode root id
    return 0
  let (placed, exact) ← nodePlacement trie key cidr bits
  if ← branch .addExact exact then
    let some id := placed | invariant "exact placement without a node"
    setNode id { (← getNode id) with peer := some pid }
    listDel id              -- list_move_tail
    listAddTail pid id
    return 0
  let newnodeAlloc ← allocNode .allocNode205 (newNode key cidr bits (some pid))
  if ← branch .addNewnodeNoMem newnodeAlloc.isNone then return -ENOMEM
  let some newnode := newnodeAlloc | invariant "unreachable"
  listAddTail pid newnode
  let down ← do
    if ← branch .addNoParentNode placed.isNone then slotGet root
    else
      let some node := placed | invariant "unreachable"
      let bit ← choose (← getNode node) key
      let down ← (← getNode node).bitAt bit
      if ← branch .addNoDown down.isNone then
        connectNode (.child node bit) newnode
        return 0
      pure down
  let some downId := down | invariant "add: no node below the placement"
  let common ← commonBits (← getNode downId) key bits
  let cidr := min cidr common   -- branch-free
  let parent := placed
  -- the compiler compares `cidr` with `common` rather than the source operands
  if ← branch .addNewnodeCoversDown ((← getNode newnode).cidr == cidr) then
    chooseAndConnectNode newnode downId
    if ← branch .addNewnodeAtRoot parent.isNone then connectNode root newnode
    else if let some p := parent then chooseAndConnectNode p newnode
    return 0
  let nodeAlloc ← allocNode .allocNode234 (newNode (← getNode newnode).bits cidr bits none)
  if ← branch .addIntermediateNoMem nodeAlloc.isNone then
    listDel newnode
    freeNode newnode
    return -ENOMEM
  let some node := nodeAlloc | invariant "unreachable"
  chooseAndConnectNode node downId
  chooseAndConnectNode node newnode
  if ← branch .addIntermediateAtRoot parent.isNone then connectNode root node
  else if let some p := parent then chooseAndConnectNode p node
  return 0

/-- swap_endian (allowedips.c:13-21): the stored integer is the big-endian
    value of the address bytes, so only the choice is modeled. -/
def swapEndian (bits : Nat) : M Unit := do
  if ← branch .swapEndian32 (bits == 32) then return
  _ ← branch .swapEndian128 (bits == 128)

/-- wg_allowedips_insert_v4 / _v6 (allowedips.c:281-301). The address is the
    big-endian integer of its bytes (what `swap_endian` stores). -/
def insert (family : Nat) (addr cidr : Nat) (peer : PeerId) : M Int := do
  modifyDev fun d => { d with peerAllowedips := { d.peerAllowedips with seq := d.peerAllowedips.seq + 1 } }
  -- swap_endian(key, ip, 32 or 128): the constant argument folds the choice
  if family == 4 then add .root4 32 addr cidr (some peer)
  else add .root6 128 addr cidr (some peer)

/-- wg_allowedips_remove_by_peer (allowedips.c:303-341). -/
def removeByPeer (pid : PeerId) : M Unit := do
  let p ← getPeer pid
  if ← branch .removeListEmpty p.allowedipsList.isEmpty then return
  modifyDev fun d => { d with peerAllowedips := { d.peerAllowedips with seq := d.peerAllowedips.seq + 1 } }
  for id in p.allowedipsList do   -- list_for_each_entry_safe over the peer's list
    _ ← branch .removeListIter true
    listDel id                    -- list_del_init(&node->peer_list)
    let n ← getNode id
    setNode id { n with peer := none }
    -- `if (node->bit[0] && node->bit[1]) continue;`
    if ← branch .removeHasBit0 (← n.bitAt 0).isSome then
      if ← branch .removeHasBit1 (← n.bitAt 1).isSome then continue
    let child ← if (← n.bitAt 0).isNone then n.bitAt 1 else n.bitAt 0   -- bit[!bit[0]]
    if ← branch .removeChildExists child.isSome then
      if let some c := child then setNode c { (← getNode c) with parent := n.parent }
    slotSet n.parent child   -- *parent_bit = child
    -- free_parent = !bit[0] && !bit[1] && (parent_bit_packed & 3) <= 1 && !parent->peer
    let freeParent ← do
      if !(← branch .removeLeafBit0 (← n.bitAt 0).isNone) then pure false
      else if !(← branch .removeLeafBit1 (← n.bitAt 1).isNone) then pure false
      else match n.parent with
        | .child parent _ => do
          _ ← branch .removeParentIsNode true
          branch .removeParentNoPeer (← getNode parent).peer.isNone
        | _ => do
          _ ← branch .removeParentIsNode false
          pure false
    let mut sibling := child
    if ← branch .removeFreeParent freeParent then
      let .child parent bit := n.parent | invariant "free_parent without a parent node"
      sibling ← (← getNode parent).bitAt (1 - bit)   -- parent->bit[!(parent_bit_packed & 1)]
    freeNode id   -- call_rcu(&node->rcu, node_free_rcu)
    if ← branch .removeNotFreeParent !freeParent then continue
    let .child parent _ := n.parent | invariant "free_parent without a parent node"
    let pn ← getNode parent
    if ← branch .removeSiblingExists sibling.isSome then
      if let some c := sibling then setNode c { (← getNode c) with parent := pn.parent }
    slotSet pn.parent sibling
    freeNode parent   -- call_rcu(&parent->rcu, node_free_rcu)
  _ ← branch .removeListIter false

/-- The node and all nodes below it (root_free_rcu's walk, a cut point), in
    the recursion's order: the node, then bit[0]'s subtree, then bit[1]'s. An
    explicit stack, fuel-bounded (future-proof-paths note, 3(d)). -/
def subtree (id : NodeId) : M (List NodeId) := do
  let mut out := #[]
  let mut stack := [id]
  for _ in [0:1 <<< 20] do
    match stack with
    | [] => return out.toList
    | n :: rest =>
      stack := rest
      out := out.push n
      let node ← getNode n
      -- bit[1] goes under bit[0] on the stack, so bit[0]'s subtree is listed first
      for c in node.bit.toList.reverse do
        if let some c := c then stack := c :: stack
  invariant "the trie walk did not terminate"

/-- root_remove_peer_lists (allowedips.c:69-80): a depth-first walk with an
    explicit stack, pushing bit[0] then bit[1]. -/
def rootRemovePeerLists (root : NodeId) : M Unit := do
  let mut stack := [root]
  for _ in [0:1 <<< 20] do
    -- while (len > 0 && (node = stack[--len]))
    match stack with
    | [] => do _ ← branch .rootRemoveLenPositive false; return
    | id :: rest =>
      _ ← branch .rootRemoveLenPositive true
      _ ← branch .rootRemovePopped true   -- push_rcu stores only non-NULL nodes
      stack := rest
      let n ← getNode id
      for c in n.bit.toList do   -- push_rcu(stack, node->bit[0/1], &len)
        if ← branch .pushRcuNonNull c.isSome then
          if let some c := c then stack := c :: stack
      if ← branch .rootRemoveHasPeer n.peer.isSome then
        -- list_del presumes the node is on its peer's list
        let some pid := n.peer | invariant "unreachable"
        if !(← getPeer pid).allowedipsList.contains id then invariant "trie node missing from its peer's list"
        listDel id
  invariant "root_remove_peer_lists did not terminate"

/-- wg_allowedips_free (allowedips.c:258-279). -/
def free : M Unit := do
  let t := (← getDev).peerAllowedips
  modifyDev fun d => { d with peerAllowedips := { root4 := none, root6 := none, seq := t.seq + 1 } }
  for (old, d) in [(t.root4, Decision.freeHasRoot4), (t.root6, Decision.freeHasRoot6)] do
    if ← branch d old.isSome then
      if let some root := old then
        rootRemovePeerLists root
        for id in ← subtree root do freeNode id   -- call_rcu(&node->rcu, root_free_rcu)

/-- wg_allowedips_read_node (allowedips.c:343-353): the prefix, masked to
    `cidr` bits, and the address family. -/
def readNode (n : AipNode) : M (Nat × Nat × Nat) := do
  swapEndian n.bitlen   -- swap_endian(ip, node->bits, node->bitlen)
  let hasCidr ← branch .readNodeHasCidr (n.cidr != 0)
  let masked := if hasCidr then n.bits / 2 ^ (n.bitlen - n.cidr) * 2 ^ (n.bitlen - n.cidr) else 0
  return (if n.bitlen == 32 then 4 else 6, masked, n.cidr)

end Leanux.WG
