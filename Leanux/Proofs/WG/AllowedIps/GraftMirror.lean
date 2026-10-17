import Leanux.Proofs.WG.AllowedIps.ChildMutation
import Leanux.Proofs.WG.AllowedIps.ListsMirror

/-! Original selected-root grafts, retaining both allocation refusals and the
source's intermediate writes. A missing allocation record remains a Stop. -/
set_option pp.structureInstances false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

theorem commonBits_wp {σ : Type} (k : σ) (n : WG.AipNode) (key width : Nat)
    (hw : width = 32 ∨ width = 128) :
    ⦃fun w => ⌜w = k⌝⦄ (WG.commonBits n key width : StateT σ AmbientM Nat)
    ⦃⇓ x w => ⌜x = common width n.bits key ∧ w = k⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient h
  refine ⟨_, w, commonRecords ambient width (n.bits ^^^ key), ?_, rfl, h⟩
  have hlift : (WG.commonBits n key width : StateT σ AmbientM Nat) =
      StateT.lift (WG.commonBits (m := AmbientM) n key width) := by
    change (WG.commonBits n key width : StateT σ AmbientM Nat) =
      monadLift (WG.commonBits (m := AmbientM) n key width)
    simp only [WG.commonBits, branch, monadLift_self,
      monadLift_bind, monadLift_pure, apply_ite] <;> rfl
  rw [hlift, stateLiftAmbient_run, commonBits_run n key width ambient hw]
  rfl

theorem freeNode_wp (k : WG.AipStore) (id : Nat) (n : WG.AipNode)
    (hn : k.nodes[id]? = some n) :
    ⦃fun w => ⌜w = k⌝⦄ WG.freeNode id
    ⦃⇓ x w => ⌜x = () ∧ w = { k with nodes := k.nodes.erase id }⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hw
  subst w
  refine ⟨(), _, ambient, ?_, rfl, rfl⟩
  simp [WG.freeNode, WG.getNode, hn]

theorem chooseAndConnectNode_wp (k : WG.AipStore)
    (parent id : Nat) (pn n : WG.AipNode) (hp : k.nodes[parent]? = some pn)
    (hn : k.nodes[id]? = some n) (hne : id ≠ parent) (hc : pn.cidr < pn.bitlen) :
    ⦃fun w => ⌜w = k⌝⦄ WG.chooseAndConnectNode parent id
    ⦃⇓ x w => ⌜x = () ∧ w = { k with nodes :=
      (k.nodes.insert id { n with parent := .child parent (bit pn.bitlen pn.cidr n.bits) }).insert parent { pn with bit := pn.bit.set! (bit pn.bitlen pn.cidr n.bits) (some id) } }⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hkw
  subst w
  let side := bit pn.bitlen pn.cidr n.bits
  have hb : ¬ side > 1 := by have := bit_lt_two pn.bitlen pn.cidr n.bits; omega
  refine ⟨(), { k with nodes := (k.nodes.insert id { n with parent := .child parent side }).insert parent { pn with bit := pn.bit.set! side (some id) } }, ambient, ?_, rfl, rfl⟩
  simp [WG.chooseAndConnectNode, WG.getNode, WG.choose,
    WG.connectNode, WG.setNode, WG.slotSet, hp, hn,
    show ¬ pn.cidr ≥ pn.bitlen from by omega, Std.TreeMap.getElem?_insert, hne,
    side, bit] at hb ⊢
  simp only [show ¬ 1 < n.bits / 2 ^ (pn.bitlen - 1 - pn.cidr) % 2 from by omega, ↓reduceIte]
  rfl

theorem PlacementWitness.root_stopped_result {n : NodeData} {l r : Tree}
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits width n.cidr n.addr = prefixBits width n.cidr key))
    (h : PlacementWitness (.node n l r) width key cidr result) : result = (none, false) := by
  obtain ⟨c, u, ht, hf, he⟩ := h
  cases c with
  | here =>
    change Tree.node n l r = u at ht
    subst u
    rcases he with ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨hc, hm, _⟩
    · exact he
    · exact he
    · exact False.elim (hstop ⟨by omega, hm⟩)
  | left m c right =>
    have hn := (Tree.node.inj ht).1
    subst m
    exact False.elim (hstop ⟨by have := hf.1; omega, hf.2.1⟩)
  | right m left c =>
    have hn := (Tree.node.inj ht).1
    subst m
    exact False.elim (hstop ⟨by have := hf.1; omega, hf.2.1⟩)

theorem nodePlacement_root_stopped_wp (k : WG.AipStore)
    (width key cidr : Nat) (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (hc : cidr ≤ width) (base : WG.Slot) (n : NodeData) (l r : Tree)
    (hr : RepAt k.nodes width base (.node n l r)) (hv : (Tree.node n l r).Valid width)
    (hstop : ¬ (n.cidr ≤ cidr ∧ prefixBits width n.cidr n.addr = prefixBits width n.cidr key)) :
    ⦃fun w => ⌜w = k⌝⦄ WG.nodePlacement (some n.id) key cidr width
    ⦃⇓ x w => ⌜x = (none, false) ∧ w = k⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hkw
  obtain ⟨x, v, finalAmbient, he, hf, hp⟩ :=
    nodePlacement_run w ambient width key cidr hw hk hc (.node n l r) base (hkw ▸ hr) hv
  exact ⟨x, v, finalAmbient, he, hp.root_stopped_result hstop, hf.trans hkw⟩

def graftListed (d : WG.Device) (width addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  { allocated d (WG.newNode addr cidr width (some pid)) with
    peers := d.peers.insert pid { p with allowedipsList := p.allowedipsList ++ [d.nextNode] } }

def connectedRoot (d : WG.Device) (v4 : Bool) (id : Nat) (n : WG.AipNode) : WG.Device :=
  rootWrite { d with nodes := d.nodes.insert id { n with parent := rootSlot v4 } } v4 (some id)

def graftOne (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let side := bit (rootWidth v4) cidr old.bits
  let attached := connectedChild (graftListed d (rootWidth v4) addr cidr pid p)
    d.nextNode side id leaf old
  connectedRoot attached v4 d.nextNode { leaf with bit := leaf.bit.set! side (some id) }

def graftTwo (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid split : Nat) (p : WG.Peer) : WG.Device :=
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let mid := WG.newNode addr split (rootWidth v4) none
  let sd := bit (rootWidth v4) split old.bits
  let sn := bit (rootWidth v4) split addr
  let a := allocated (graftListed d (rootWidth v4) addr cidr pid p) mid
  let b := connectedChild a (d.nextNode + 1) sd id mid old
  let mid' := { mid with bit := mid.bit.set! sd (some id) }
  let c := connectedChild b (d.nextNode + 1) sn d.nextNode mid' leaf
  connectedRoot c v4 (d.nextNode + 1) { mid' with bit := mid'.bit.set! sn (some d.nextNode) }

def graftRolledBack (d : WG.Device) (width addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let dl := unlisted (graftListed d width addr cidr pid p) d.nextNode
  { dl with nodes := dl.nodes.erase d.nextNode }

def graftInstalled (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let split := min cidr (common (rootWidth v4) old.bits addr)
  if split = cidr then graftOne d v4 id old addr cidr pid p
  else graftTwo d v4 id old addr cidr pid split p


/-- The original final recorded root/parent choice, shared by both graft arms. -/
def finishGraft (decision : Decision) (root : WG.Slot) (placed : Option Nat) (id : Nat) : WG.M Int := do
  if ← branch decision placed.isNone then WG.connectNode root id
  else if let some parent := placed then WG.chooseAndConnectNode parent id
  return 0

/-- The exact source suffix after a nonempty node below placement is known. -/
def graftTail (root : WG.Slot) (bits key cidr : Nat) (placed : Option Nat)
    (newnode downId : Nat) : WG.M Int := do
  let common ← WG.commonBits (← WG.getNode downId) key bits
  let cidr := min cidr common
  if ← branch .addNewnodeCoversDown ((← WG.getNode newnode).cidr == cidr) then
    WG.chooseAndConnectNode newnode downId
    return ← finishGraft .addNewnodeAtRoot root placed newnode
  let nodeAlloc ← WG.allocNode .allocNode234 (WG.newNode (← WG.getNode newnode).bits cidr bits none)
  if ← branch .addIntermediateNoMem nodeAlloc.isNone then
    WG.listDel newnode
    WG.freeNode newnode
    return -ENOMEM
  let some node := nodeAlloc | invariant "unreachable"
  WG.chooseAndConnectNode node downId
  WG.chooseAndConnectNode node newnode
  finishGraft .addIntermediateAtRoot root placed node

open WG in
def addWithTail (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) : WG.M Int := do
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
  graftTail root bits key cidr placed newnode downId

/-- Exact source equality retains all original prefix choices and Stops. -/
theorem addWithTail_eq (root : WG.Slot) (bits key cidr : Nat) (peer : Option Nat) :
    addWithTail root bits key cidr peer = WG.add root bits key cidr peer := by
  rfl

def graftOneReady (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  connectedChild (graftListed d (rootWidth v4) addr cidr pid p) d.nextNode
    (bit (rootWidth v4) cidr old.bits) id (WG.newNode addr cidr (rootWidth v4) (some pid)) old

def graftOneHead (v4 : Bool) (id : Nat) (old : WG.AipNode) (addr cidr pid : Nat) : WG.AipNode :=
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  { leaf with bit := leaf.bit.set! (bit (rootWidth v4) cidr old.bits) (some id) }

def graftTwoReady (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr cidr pid split : Nat) (p : WG.Peer) : WG.Device :=
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let mid := WG.newNode addr split (rootWidth v4) none
  let sd := bit (rootWidth v4) split old.bits
  let sn := bit (rootWidth v4) split addr
  let a := allocated (graftListed d (rootWidth v4) addr cidr pid p) mid
  let b := connectedChild a (d.nextNode + 1) sd id mid old
  connectedChild b (d.nextNode + 1) sn d.nextNode { mid with bit := mid.bit.set! sd (some id) } leaf

def graftTwoHead (d : WG.Device) (v4 : Bool) (id : Nat) (old : WG.AipNode)
    (addr split : Nat) : WG.AipNode :=
  let mid := WG.newNode addr split (rootWidth v4) none
  { mid with bit := (mid.bit.set! (bit (rootWidth v4) split old.bits) (some id)).set! (bit (rootWidth v4) split addr) (some d.nextNode) }

theorem finishGraft_root_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (decision : Decision) (v4 : Bool) (id : Nat) (n : WG.AipNode) (hn : d.nodes[id]? = some n) :
    ⦃fun w => ⌜w = k⌝⦄ finishGraft decision (rootSlot v4) none id
    ⦃⇓ x w => ⌜x = 0 ∧ w = { k with dev := some (connectedRoot d v4 id n) }⌝⦄ := by
  let store (d : WG.Device) : WG.AipStore :=
    {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}
  have adapt {α : Type} (g : WGWorld) (d : WG.Device) (hd : g.dev = some d)
      (a : WG.AipM α) (Q : α → WGWorld → Prop)
      (h : ⦃fun s => ⌜s = store d⌝⦄ a
        ⦃⇓ x s => ⌜Q x {g with dev := some {d with nodes := s.nodes, nextNode := s.nextNode, peerAllowedips := s.trie}}⌝⦄) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓ x w => ⌜Q x w⌝⦄ := by
    apply total_liftAip_of
    · intro w hw; subst w; exact ⟨d, hd⟩
    · intro w d' hw hd'
      subst w
      have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
      subst d'
      exact h
  have h : ⦃fun w => ⌜w = k⌝⦄
      (MonadLift.monadLift (WG.connectNode (rootSlot v4) id) : WG.M Unit)
      ⦃⇓ x w => ⌜x = () ∧ w = {k with dev := some (connectedRoot d v4 id n)}⌝⦄ := by
    apply adapt k d hd
    have hn := connectNode_root_wp (store d) v4 id n hn
    apply (total_iff_run_ambient _ _ _).mpr
    intro entry ambient hi
    obtain ⟨result, finish, finalAmbient, he, hr, hf⟩ :=
      (total_iff_run_ambient _ _ _).mp hn entry ambient hi
    refine ⟨result, finish, finalAmbient, he, ?_⟩
    subst result
    subst finish
    simp [connectedRoot, rootWrite, store]
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hw
  subst w
  let recorded := {ambient with steps := ambient.steps.push {decision, outcome := true, netRx := ambient.netRxSection}}
  obtain ⟨result, finish, finalAmbient, he, hr, hf⟩ :=
    (total_iff_run_ambient _ _ _).mp h k recorded rfl
  subst result
  subst finish
  refine ⟨0, _, finalAmbient, ?_, rfl, rfl⟩
  change (((MonadLift.monadLift (WG.connectNode (rootSlot v4) id) : WG.M Unit) >>= fun _ => pure (0 : Int)).run k).run recorded = _
  simp only [StateT.run_bind, he]
  rfl

theorem finishGraft_child_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (decision : Decision) (root : WG.Slot) (parent id : Nat) (pn n : WG.AipNode)
    (hp : d.nodes[parent]? = some pn) (hn : d.nodes[id]? = some n)
    (hne : id ≠ parent) (hc : pn.cidr < pn.bitlen) :
    ⦃fun w => ⌜w = k⌝⦄ finishGraft decision root (some parent) id
    ⦃⇓ x w => ⌜x = 0 ∧ w = { k with dev := some (connectedChild d parent (bit pn.bitlen pn.cidr n.bits) id pn n) }⌝⦄ := by
  let store (d : WG.Device) : WG.AipStore :=
    {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}
  have adapt {α : Type} (g : WGWorld) (d : WG.Device) (hd : g.dev = some d)
      (a : WG.AipM α) (Q : α → WGWorld → Prop)
      (h : ⦃fun s => ⌜s = store d⌝⦄ a
        ⦃⇓ x s => ⌜Q x {g with dev := some {d with nodes := s.nodes, nextNode := s.nextNode, peerAllowedips := s.trie}}⌝⦄) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓ x w => ⌜Q x w⌝⦄ := by
    apply total_liftAip_of
    · intro w hw; subst w; exact ⟨d, hd⟩
    · intro w d' hw hd'
      subst w
      have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
      subst d'
      exact h
  have h : ⦃fun w => ⌜w = k⌝⦄
      (MonadLift.monadLift (WG.chooseAndConnectNode parent id) : WG.M Unit)
      ⦃⇓ x w => ⌜x = () ∧ w = {k with dev := some (connectedChild d parent (bit pn.bitlen pn.cidr n.bits) id pn n)}⌝⦄ := by
    apply adapt k d hd
    have hn := chooseAndConnectNode_wp (store d) parent id pn n hp hn hne hc
    apply (total_iff_run_ambient _ _ _).mpr
    intro entry ambient hi
    obtain ⟨result, finish, finalAmbient, he, hr, hf⟩ :=
      (total_iff_run_ambient _ _ _).mp hn entry ambient hi
    refine ⟨result, finish, finalAmbient, he, ?_⟩
    subst result
    subst finish
    simp [connectedChild, store]
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hw
  subst w
  let recorded := {ambient with steps := ambient.steps.push {decision, outcome := false, netRx := ambient.netRxSection}}
  obtain ⟨result, finish, finalAmbient, he, hr, hf⟩ :=
    (total_iff_run_ambient _ _ _).mp h k recorded rfl
  subst result
  subst finish
  refine ⟨0, _, finalAmbient, ?_, rfl, rfl⟩
  change (((MonadLift.monadLift (WG.chooseAndConnectNode parent id) : WG.M Unit) >>= fun _ => pure (0 : Int)).run k).run recorded = _
  simp only [StateT.run_bind, he]
  rfl

theorem graftTail_wp (k : WGWorld) (d : WG.Device) (v4 : Bool)
    (id : Nat) (old : WG.AipNode) (addr cidr pid : Nat) (p : WG.Peer) (placed : Option Nat)
    (hn : d.nodes[id]? = some old) (hid : id < d.nextNode)
    (hs : min cidr (common (rootWidth v4) old.bits addr) < rootWidth v4)
    (outOne outTwo : WG.Device)
    (hfinishOne : ⦃fun w => ⌜w = { k with dev := some (graftOneReady d v4 id old addr cidr pid p) }⌝⦄
      finishGraft .addNewnodeAtRoot (rootSlot v4) placed d.nextNode
      ⦃⇓ x w => ⌜x = 0 ∧ w = { k with dev := some outOne }⌝⦄)
    (hfinishTwo : ⦃fun w => ⌜w = { k with dev := some (graftTwoReady d v4 id old addr cidr pid
          (min cidr (common (rootWidth v4) old.bits addr)) p) }⌝⦄
      finishGraft .addIntermediateAtRoot (rootSlot v4) placed (d.nextNode+1)
      ⦃⇓ x w => ⌜x = 0 ∧ w = { k with dev := some outTwo }⌝⦄) :
    ⦃fun w => ⌜w = { k with dev := some (graftListed d (rootWidth v4) addr cidr pid p) }⌝⦄
      graftTail (rootSlot v4) (rootWidth v4) addr cidr placed d.nextNode id
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w = k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) old.bits addr) ≠ cidr ∧
        w = { k with dev := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w = { k with dev := some (if min cidr (common (rootWidth v4) old.bits addr) = cidr then outOne else outTwo) })⌝⦄ := by
  let store (d : WG.Device) : WG.AipStore :=
    {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}
  have adapt {α : Type} (g : WGWorld) (d : WG.Device) (hd : g.dev = some d)
      (a : WG.AipM α) (Q : α → WGWorld → Prop)
      (h : ⦃fun s => ⌜s = store d⌝⦄ a
        ⦃⇓ x s => ⌜Q x {g with dev := some {d with nodes := s.nodes, nextNode := s.nextNode, peerAllowedips := s.trie}}⌝⦄) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓ x w => ⌜Q x w⌝⦄ := by
    apply total_liftAip_of
    · intro w hw; subst w; exact ⟨d, hd⟩
    · intro w d' hw hd'
      subst w
      have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
      subst d'
      exact h
  have read {α : Type} (g : WGWorld) (d : WG.Device) (hd : g.dev = some d)
      (a : WG.AipM α) (value : α)
      (h : ⦃fun s => ⌜s = store d⌝⦄ a ⦃⇓ x s => ⌜x = value ∧ s = store d⌝⦄) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓ x w => ⌜x = value ∧ w = g⌝⦄ := by
    apply (total_iff_run_ambient _ _ _).mpr
    intro w ambient hw
    subst w
    obtain ⟨x, s, ambient', hr, hv, hs⟩ := (total_iff_run_ambient _ _ _).mp h _ ambient rfl
    subst s
    refine ⟨x, g, ambient', ?_, hv, rfl⟩
    change ((WG.liftAip a).run g).run ambient = _
    rw [liftAip_run, hd]
    simp only [store] at hr
    simp only [hr, Except.map]
    change Except.ok ((x, {g with dev := some d}), ambient') = _
    rw [← hd]
  have getNode_wp (g : WGWorld) (d : WG.Device) (id : Nat) (n : WG.AipNode)
      (hd : g.dev = some d) (hn : d.nodes[id]? = some n) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift (WG.getNode id) : WG.M WG.AipNode)
      ⦃⇓ x w => ⌜x = n ∧ w = g⌝⦄ :=
    read g d hd _ _ (Leanux.Proofs.WG.AllowedIps.getNode_wp (store d) id n hn)
  have chooseAndConnectNode_wp (g : WGWorld) (d : WG.Device) (hd : g.dev = some d)
      (parent id : Nat) (pn n : WG.AipNode) (hp : d.nodes[parent]? = some pn)
      (hn : d.nodes[id]? = some n) (hne : id ≠ parent) (hc : pn.cidr < pn.bitlen) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift (WG.chooseAndConnectNode parent id) : WG.M Unit)
      ⦃⇓ x w => ⌜x = () ∧ w = {g with dev := some (connectedChild d parent (bit pn.bitlen pn.cidr n.bits) id pn n)}⌝⦄ := by
    apply adapt g d hd
    have hnative := Leanux.Proofs.WG.AllowedIps.chooseAndConnectNode_wp (store d) parent id pn n hp hn hne hc
    apply (total_iff_run_ambient _ _ _).mpr
    intro entry ambient hi
    obtain ⟨result, finish, finalAmbient, he, hr, hf⟩ :=
      (total_iff_run_ambient _ _ _).mp hnative entry ambient hi
    refine ⟨result, finish, finalAmbient, he, ?_⟩
    subst result
    subst finish
    simp [connectedChild, store]
  have freeNode_wp (g : WGWorld) (d : WG.Device) (hd : g.dev = some d)
      (id : Nat) (n : WG.AipNode) (hn : d.nodes[id]? = some n) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift (WG.freeNode id) : WG.M Unit)
      ⦃⇓ x w => ⌜x = () ∧ w = {g with dev := some {d with nodes := d.nodes.erase id}}⌝⦄ := by
    apply adapt g d hd
    have hnative := Leanux.Proofs.WG.AllowedIps.freeNode_wp (store d) id n hn
    apply (total_iff_run_ambient _ _ _).mpr
    intro entry ambient hi
    obtain ⟨result, finish, finalAmbient, he, hr, hf⟩ :=
      (total_iff_run_ambient _ _ _).mp hnative entry ambient hi
    refine ⟨result, finish, finalAmbient, he, ?_⟩
    subst result
    subst finish
    simp [store]
  have allocNode_wp (g : WGWorld) (d : WG.Device) (hd : g.dev = some d)
      (site : AllocSite) (n : WG.AipNode) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift (WG.allocNode site n) : WG.M (Option Nat))
      ⦃⇓? result w => ⌜(result = none ∧ w = g) ∨
        (result = some d.nextNode ∧ w = {g with dev := some (allocated d n)})⌝⦄ := by
    apply hoare_liftAip_of
    intro w d' hw hd'
    subst w
    have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
    subst d'
    apply hoare_consequence (Leanux.Proofs.WG.AllowedIps.allocNode_wp _ _ _)
    · intro s h; exact h
    · intro r s h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; refine ⟨rfl, ?_⟩
        change {g with dev := some d} = g
        rw [← hd]
      · right; simp [allocated]

  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let dl := graftListed d (rootWidth v4) addr cidr pid p
  let kl : WGWorld := { k with dev := some dl }
  let split := min cidr (common (rootWidth v4) old.bits addr)
  have hne : d.nextNode ≠ id := Nat.ne_of_gt hid
  have hnl : dl.nodes[id]? = some old := by
    simp [dl, graftListed, allocated, Std.TreeMap.getElem?_insert, hne, hn]
  have hg := getNode_wp kl dl id old rfl hnl
  have hcommon := commonBits_wp kl old addr (rootWidth v4) hw
  have hleaf : dl.nodes[d.nextNode]? = some leaf := by simp [dl, graftListed, allocated, leaf]
  have hglf := getNode_wp kl dl d.nextNode leaf rfl hleaf
  have branchRule {β : Type} (decision : Decision) (value : Bool)
      (P : WGWorld → Prop) (Q : β → WGWorld → Prop) (f : Bool → WG.M β)
      (hf : Hoare (f value) P Q) :
      Hoare ((branch decision value : WG.M Bool) >>= f) P Q := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x out ambient' hi hr
    change ((f value).run w).run _ = .ok ((x, out), ambient') at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ hi hr
  have mayReturn {β : Type} (a : WG.M β) (P : WGWorld → Prop)
      (Q : β → WGWorld → Prop) (h : ⦃fun w => ⌜P w⌝⦄ a ⦃⇓ x w => ⌜Q x w⌝⦄) :
      Hoare a P Q := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x out ambient' hi hr
    obtain ⟨y, v, b, he, hq⟩ := (total_iff_run_ambient _ _ _).mp h w ambient hi
    rw [hr] at he
    cases he
    exact hq
  have known {α β : Type} (a : WG.M α) (f : α → WG.M β)
      (entry finish : WGWorld) (value : α) (Q : β → WGWorld → Prop)
      (h : ⦃fun w => ⌜w = entry⌝⦄ a ⦃⇓ x w => ⌜x = value ∧ w = finish⌝⦄)
      (hf : Hoare (f value) (fun w => w = finish) Q) :
      Hoare (a >>= f) (fun w => w = entry) Q := by
    apply hoare_bind _ _ (mayReturn _ _ _ h)
    intro x
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result out ambient' hx hr
    rcases hx with ⟨hvalue, hstate⟩
    subst x
    subst w
    exact (hoare_iff_run_ambient _ _ _).mp hf _ ambient result out ambient' rfl hr
  let Post := fun result (w : WGWorld) =>
    (result = -ENOMEM ∧ w = k) ∨
      (result = -ENOMEM ∧ split ≠ cidr ∧
        w = {k with dev := some (graftRolledBack d (rootWidth v4) addr cidr pid p)}) ∨
      (result = 0 ∧ w = {k with dev := some (if split = cidr then outOne else outTwo)})
  change Hoare (graftTail (rootSlot v4) (rootWidth v4) addr cidr placed d.nextNode id)
    (fun w => w = kl) Post
  unfold graftTail
  apply known _ _ kl kl _ _ hg
  apply known _ _ kl kl _ _ hcommon
  apply known _ _ kl kl _ _ hglf
  apply branchRule .addNewnodeCoversDown (leaf.cidr == split)
  by_cases he : split = cidr
  · have hb : (leaf.cidr == split) = true := by simp [leaf, WG.newNode, he]
    simp only [hb, ↓reduceIte]
    have hconn := chooseAndConnectNode_wp kl dl rfl d.nextNode id leaf old hleaf hnl
      (Ne.symm hne) (by change cidr < rootWidth v4; omega)
    apply known _ _ kl _ () _ hconn
    apply hoare_consequence (mayReturn _ _ _ hfinishOne)
    · intro w hw; exact hw
    · intro result w hw
      apply Or.inr
      apply Or.inr
      simpa only [he, ↓reduceIte] using hw
  · have hb : (leaf.cidr == split) = false := by simp [leaf, WG.newNode, Ne.symm he]
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    apply known _ _ kl kl _ _ hglf
    let mid := WG.newNode addr split (rootWidth v4) none
    have halloc2 := allocNode_wp kl dl rfl .allocNode234 mid
    apply hoare_bind _ _ halloc2
    intro allocation
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result out ambient' hi hr
    rcases hi with ⟨ha, hw⟩ | ⟨ha, hw⟩
    · subst allocation
      subst w
      apply (hoare_iff_run_ambient _ (fun w => w = kl) Post).mp ?_ kl ambient result out ambient' rfl hr
      apply branchRule .addIntermediateNoMem true
      simp only [↓reduceIte]
      have hdel := listDel_wp kl dl rfl d.nextNode
      let dr := unlisted dl d.nextNode
      let kr : WGWorld := {k with dev := some dr}
      apply known _ _ kl kr () _ hdel
      have hnr : dr.nodes[d.nextNode]? = some leaf := hleaf
      have hfree := freeNode_wp kr dr rfl d.nextNode leaf hnr
      apply known _ _ kr _ () _ hfree
      apply hoare_consequence (hoare_pure (-ENOMEM) _)
      · intro w hw; exact hw
      · intro result w hw
        exact Or.inr (Or.inl ⟨hw.1, he, hw.2⟩)
    · subst allocation
      subst w
      let dm := allocated dl mid
      let km : WGWorld := {k with dev := some dm}
      apply (hoare_iff_run_ambient _ (fun w => w = km) Post).mp ?_ km ambient result out ambient' rfl hr
      apply branchRule .addIntermediateNoMem false
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hmid : dm.nodes[d.nextNode + 1]? = some mid := by simp [dm, allocated, dl, graftListed]
      have hne2 : d.nextNode + 1 ≠ id := Nat.ne_of_gt (Nat.lt_trans hid (Nat.lt_succ_self _))
      have hdown : dm.nodes[id]? = some old := by
        simp [dm, allocated, dl, graftListed, Std.TreeMap.getElem?_insert, hne, hn, hne2]
      have hconn1 := chooseAndConnectNode_wp km dm rfl (d.nextNode + 1) id mid old hmid hdown
        (Ne.symm hne2) hs
      let sd := bit (rootWidth v4) split old.bits
      let sn := bit (rootWidth v4) split addr
      let mid' := {mid with bit := mid.bit.set! sd (some id)}
      let dc := connectedChild dm (d.nextNode + 1) sd id mid old
      let kc : WGWorld := {k with dev := some dc}
      apply known _ _ km kc () _ hconn1
      have hmid' : dc.nodes[d.nextNode + 1]? = some mid' := by simp [dc, connectedChild, mid']
      have hleaf' : dc.nodes[d.nextNode]? = some leaf := by
        simp [dc, connectedChild, dm, allocated, dl, graftListed,
          Ne.symm hne, leaf, Std.TreeMap.getElem_insert]
      have hconn2 := chooseAndConnectNode_wp kc dc rfl (d.nextNode + 1) d.nextNode mid' leaf hmid' hleaf'
        (by omega) hs
      apply known _ _ kc _ () _ hconn2
      apply hoare_consequence (mayReturn _ _ _ hfinishTwo)
      · intro w hw; exact hw
      · intro result w hw
        apply Or.inr
        apply Or.inr
        simpa only [he, ↓reduceIte] using hw

theorem add_placed_root_graft_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (v4 : Bool) (id : Nat) (old : WG.AipNode) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hn : d.nodes[id]? = some old)
    (hroot : rootValue d v4 = some id) (hid : id < d.nextNode)
    (hc : cidr ≤ rootWidth v4)
    (hs : min cidr (common (rootWidth v4) old.bits addr) < rootWidth v4)
    (hplacement : ⦃fun w => ⌜w = k⌝⦄ (MonadLift.monadLift (WG.nodePlacement (some id) addr cidr (rootWidth v4)) : WG.M (Option Nat × Bool))
      ⦃⇓ x w => ⌜x = (none, false) ∧ w = k⌝⦄) :
    ⦃fun w => ⌜w = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w = k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) old.bits addr) ≠ cidr ∧
        w = { k with dev := some (graftRolledBack d (rootWidth v4) addr cidr pid p) }) ∨
      (result = 0 ∧ w = { k with dev := some (graftInstalled d v4 id old addr cidr pid p) })⌝⦄ := by
  let store (d : WG.Device) : WG.AipStore :=
    {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}
  have adapt {α : Type} (g : WGWorld) (d : WG.Device) (hd : g.dev = some d)
      (a : WG.AipM α) (Q : α → WGWorld → Prop)
      (h : ⦃fun s => ⌜s = store d⌝⦄ a
        ⦃⇓ x s => ⌜Q x {g with dev := some {d with nodes := s.nodes, nextNode := s.nextNode, peerAllowedips := s.trie}}⌝⦄) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓ x w => ⌜Q x w⌝⦄ := by
    apply total_liftAip_of
    · intro w hw; subst w; exact ⟨d, hd⟩
    · intro w d' hw hd'
      subst w
      have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
      subst d'
      exact h
  have read {α : Type} (g : WGWorld) (d : WG.Device) (hd : g.dev = some d)
      (a : WG.AipM α) (value : α)
      (h : ⦃fun s => ⌜s = store d⌝⦄ a ⦃⇓ x s => ⌜x = value ∧ s = store d⌝⦄) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓ x w => ⌜x = value ∧ w = g⌝⦄ := by
    apply (total_iff_run_ambient _ _ _).mpr
    intro w ambient hw
    subst w
    obtain ⟨x, s, ambient', hr, hv, hs⟩ := (total_iff_run_ambient _ _ _).mp h _ ambient rfl
    subst s
    refine ⟨x, g, ambient', ?_, hv, rfl⟩
    change ((WG.liftAip a).run g).run ambient = _
    rw [liftAip_run, hd]
    simp only [store] at hr
    simp only [hr, Except.map]
    change Except.ok ((x, {g with dev := some d}), ambient') = _
    rw [← hd]
  have allocNode_wp (g : WGWorld) (d : WG.Device) (hd : g.dev = some d)
      (site : AllocSite) (n : WG.AipNode) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift (WG.allocNode site n) : WG.M (Option Nat))
      ⦃⇓? result w => ⌜(result = none ∧ w = g) ∨
        (result = some d.nextNode ∧ w = {g with dev := some (allocated d n)})⌝⦄ := by
    apply hoare_liftAip_of
    intro w d' hw hd'
    subst w
    have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
    subst d'
    apply hoare_consequence (Leanux.Proofs.WG.AllowedIps.allocNode_wp _ _ _)
    · intro s h; exact h
    · intro r s h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; refine ⟨rfl, ?_⟩
        change {g with dev := some d} = g
        rw [← hd]
      · right; simp [allocated]
  have hgetRoot := read k d hd _ _ (slotGet_root_wp (store d) v4)
  change ⦃fun w => ⌜w = k⌝⦄ (MonadLift.monadLift (WG.slotGet (rootSlot v4)) : WG.M (Option Nat))
    ⦃⇓ r w => ⌜r = rootValue d v4 ∧ w = k⌝⦄ at hgetRoot
  simp only [hroot] at hgetRoot
  have halloc := allocNode_wp k d hd .allocNode205 (WG.newNode addr cidr (rootWidth v4) (some pid))
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let da := allocated d leaf
  let ka : WGWorld := {k with dev := some da}
  have hlist := listAddTail_wp ka da rfl pid d.nextNode p hp
  let dl := graftListed d (rootWidth v4) addr cidr pid p
  let kl : WGWorld := {k with dev := some dl}
  have hgetDown := read kl dl rfl _ _ (slotGet_root_wp (store dl) v4)
  have hrl : (if v4 then (store dl).trie.root4 else (store dl).trie.root6) = some id := hroot
  simp only [hrl] at hgetDown
  have hOne : ⦃fun w => ⌜w = {k with dev := some (graftOneReady d v4 id old addr cidr pid p)}⌝⦄
      finishGraft .addNewnodeAtRoot (rootSlot v4) none d.nextNode
      ⦃⇓ x w => ⌜x = 0 ∧ w = {k with dev := some (graftOne d v4 id old addr cidr pid p)}⌝⦄ := by
    have hnode : (graftOneReady d v4 id old addr cidr pid p).nodes[d.nextNode]? =
        some (graftOneHead v4 id old addr cidr pid) := by
      simp [graftOneReady, graftOneHead, connectedChild]
    simpa only [graftOneReady, graftOneHead, graftOne] using
      (finishGraft_root_wp {k with dev := some (graftOneReady d v4 id old addr cidr pid p)}
        (graftOneReady d v4 id old addr cidr pid p) rfl .addNewnodeAtRoot v4 d.nextNode _ hnode)
  have hTwo : ⦃fun w => ⌜w = {k with dev := some (graftTwoReady d v4 id old addr cidr pid
        (min cidr (common (rootWidth v4) old.bits addr)) p)}⌝⦄
      finishGraft .addIntermediateAtRoot (rootSlot v4) none (d.nextNode + 1)
      ⦃⇓ x w => ⌜x = 0 ∧ w = {k with dev := some (graftTwo d v4 id old addr cidr pid
        (min cidr (common (rootWidth v4) old.bits addr)) p)}⌝⦄ := by
    have hnode : (graftTwoReady d v4 id old addr cidr pid
        (min cidr (common (rootWidth v4) old.bits addr)) p).nodes[d.nextNode + 1]? =
        some (graftTwoHead d v4 id old addr (min cidr (common (rootWidth v4) old.bits addr))) := by
      simp [graftTwoReady, graftTwoHead, connectedChild]
    simpa only [graftTwoReady, graftTwoHead, graftTwo] using
      (finishGraft_root_wp {k with dev := some (graftTwoReady d v4 id old addr cidr pid
        (min cidr (common (rootWidth v4) old.bits addr)) p)}
        (graftTwoReady d v4 id old addr cidr pid (min cidr (common (rootWidth v4) old.bits addr)) p)
        rfl .addIntermediateAtRoot v4 (d.nextNode + 1) _ hnode)
  have htail := graftTail_wp k d v4 id old addr cidr pid p none hn hid hs _ _ hOne hTwo
  have branchRule {β : Type} (decision : Decision) (value : Bool)
      (P : WGWorld → Prop) (Q : β → WGWorld → Prop) (f : Bool → WG.M β)
      (hf : Hoare (f value) P Q) :
      Hoare ((branch decision value : WG.M Bool) >>= f) P Q := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x out ambient' hi hr
    change ((f value).run w).run _ = .ok ((x, out), ambient') at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ hi hr
  have comparisonRule {β : Type} (decision : Decision) (value : Bool) (a b : Int)
      (P : WGWorld → Prop) (Q : β → WGWorld → Prop) (f : Bool → WG.M β)
      (hf : Hoare (f value) P Q) :
      Hoare ((branchCmp decision value a b : WG.M Bool) >>= f) P Q := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x out ambient' hi hr
    change ((f value).run w).run _ = .ok ((x, out), ambient') at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ hi hr
  have mayReturn {β : Type} (a : WG.M β) (P : WGWorld → Prop)
      (Q : β → WGWorld → Prop) (h : ⦃fun w => ⌜P w⌝⦄ a ⦃⇓ x w => ⌜Q x w⌝⦄) :
      Hoare a P Q := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x out ambient' hi hr
    obtain ⟨y, v, b, he, hq⟩ := (total_iff_run_ambient _ _ _).mp h w ambient hi
    rw [hr] at he
    cases he
    exact hq
  have known {α β : Type} (a : WG.M α) (f : α → WG.M β)
      (entry finish : WGWorld) (value : α) (Q : β → WGWorld → Prop)
      (h : ⦃fun w => ⌜w = entry⌝⦄ a ⦃⇓ x w => ⌜x = value ∧ w = finish⌝⦄)
      (hf : Hoare (f value) (fun w => w = finish) Q) :
      Hoare (a >>= f) (fun w => w = entry) Q := by
    apply hoare_bind _ _ (mayReturn _ _ _ h)
    intro x
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result out ambient' hx hr
    rcases hx with ⟨hvalue, hstate⟩
    subst x
    subst w
    exact (hoare_iff_run_ambient _ _ _).mp hf _ ambient result out ambient' rfl hr
  let Post := fun result (w : WGWorld) =>
    (result = -ENOMEM ∧ w = k) ∨
      (result = -ENOMEM ∧ min cidr (common (rootWidth v4) old.bits addr) ≠ cidr ∧
        w = {k with dev := some (graftRolledBack d (rootWidth v4) addr cidr pid p)}) ∨
      (result = 0 ∧ w = {k with dev := some (graftInstalled d v4 id old addr cidr pid p)})
  change Hoare (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)) _ Post
  rw [← addWithTail_eq]
  unfold addWithTail
  apply comparisonRule .addCidrTooLong (decide (cidr > rootWidth v4)) cidr (rootWidth v4)
  simp only [show decide (cidr > rootWidth v4) = false by simp [Nat.not_lt.mpr hc],
    Bool.false_eq_true, ↓reduceIte]
  apply branchRule .addNoPeer false
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply known _ _ k k _ _ hgetRoot
  apply branchRule .addEmptyTrie false
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply known _ _ k k _ _ hplacement
  dsimp only
  apply branchRule .addExact false
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply hoare_bind _ _ halloc
  intro allocation
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result out ambient' hi hr
  rcases hi with ⟨ha, hw⟩ | ⟨ha, hw⟩
  · subst allocation
    subst w
    apply (hoare_iff_run_ambient _ (fun w => w = k) Post).mp ?_ k ambient result out ambient' rfl hr
    apply branchRule .addNewnodeNoMem true
    simp only [↓reduceIte]
    exact hoare_consequence (hoare_pure (-ENOMEM) _)
      (fun _ h => h) (fun _ _ h => Or.inl h)
  · subst allocation
    subst w
    apply (hoare_iff_run_ambient _ (fun w => w = ka) Post).mp ?_ ka ambient result out ambient' rfl hr
    apply branchRule .addNewnodeNoMem false
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply known _ _ ka kl () _ hlist
    apply branchRule .addNoParentNode true
    simp only [↓reduceIte]
    apply known _ _ kl kl _ _ hgetDown
    apply hoare_consequence htail
    · intro w hw; exact hw
    · intro result w hw
      simpa only [Post, graftInstalled] using hw

end Leanux.Proofs.WG.AllowedIps
