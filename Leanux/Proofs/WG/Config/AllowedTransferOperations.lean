import Leanux.Proofs.WG.Config.AllowedPlacementSource

/-! Exact factors of original add. The allocation fallback is retained verbatim
and stays opaque in the exact-root proof. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

def addPlacedSourceWith
    (allocate : AllocSite → AipNode → AipM (Option NodeId)) (root : Slot) (bits key cidr : Nat) (pid : PeerId)
    (placed : Option NodeId) (exact : Bool) : WG.M Int := do
  if ← branch .addExact exact then
    let some id := placed | invariant "exact placement without a node"
    setNode id { (← getNode id) with peer := some pid }
    listDel id              -- list_move_tail
    listAddTail pid id
    return 0
  let newnodeAlloc ← allocate .allocNode205 (newNode key cidr bits (some pid))
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
  let nodeAlloc ← allocate .allocNode234 (newNode (← getNode newnode).bits cidr bits none)
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

def addPlacedSource (root : Slot) (bits key cidr : Nat) (pid : PeerId)
    (placed : Option NodeId) (exact : Bool) : WG.M Int :=
  addPlacedSourceWith WG.allocNode root bits key cidr pid placed exact

def addRootSourceWith
    (allocate : AllocSite → AipNode → AipM (Option NodeId)) (root : Slot) (bits key cidr : Nat) (pid : PeerId)
    (trie : Option NodeId) : WG.M Int := do
  if ← branch .addEmptyTrie trie.isNone then
    let some id ← (do
        let r ← allocate .allocNode190 (newNode key cidr bits (some pid))
        if ← branch .addRootNoMem r.isNone then return none
        pure r) | return -ENOMEM
    listAddTail pid id
    connectNode root id
    return 0
  let (placed, exact) ← nodePlacement trie key cidr bits
  addPlacedSourceWith allocate root bits key cidr pid placed exact

def addRootSource (root : Slot) (bits key cidr : Nat) (pid : PeerId)
    (trie : Option NodeId) : WG.M Int :=
  addRootSourceWith WG.allocNode root bits key cidr pid trie

theorem add_transfer_source (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    add root bits key cidr peer = (do
    -- `unlikely(cidr > bits || !peer)`
    if ← branchCmp .addCidrTooLong (cidr > bits) cidr bits then return -EINVAL
    if ← branch .addNoPeer peer.isNone then return -EINVAL
    let some pid := peer | invariant "unreachable"
    let trie ← slotGet root
    addRootSource root bits key cidr pid trie
    ) := rfl

end Leanux.Proofs.WG.Config
