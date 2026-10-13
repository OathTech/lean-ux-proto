import Leanux.Proofs.WG.AllowedIps.StoreMutation
import Leanux.Proofs.WG.Keypairs.Frames.WGBase
import Leanux.Proofs.Framing.KernelEffects

/-! Original allowed-IP mutation contracts. Normal-return statements retain
record failures as errors; they do not assume every choice stream completes. -/
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

def allocated (d : WG.Device) (n : WG.AipNode) : WG.Device :=
  { d with nextNode := d.nextNode + 1, nodes := d.nodes.insert d.nextNode n }

theorem allocNode_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (site : AllocSite) (n : WG.AipNode) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.allocNode site n
    ⦃⇓? result w => ⌜(result = none ∧ w.k = k) ∨
      (result = some d.nextNode ∧ w.k = { k with wg := some (allocated d n) })⌝⦄ := by
  have hs := sameKernel_wp _ (hiddenAlloc_sameKernel site) (fun k' => k' = k)
  mvcgen [WG.allocNode, hs, WG.getDev, getK, WG.modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [allocated]

theorem setNode_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (id : Nat) (n : WG.AipNode) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.setNode id n
    ⦃⇓ result w => ⌜result = () ∧
      w.k = { k with wg := some { d with nodes := d.nodes.insert id n } }⌝⦄ := by
  mvcgen [WG.setNode, WG.modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem listAddTail_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (pid id : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.listAddTail pid id
    ⦃⇓ result w => ⌜result = () ∧ w.k = { k with wg := some { d with
      peers := d.peers.insert pid { p with allowedipsList := p.allowedipsList ++ [id] } } }⌝⦄ := by
  mvcgen [WG.listAddTail, WG.getPeer, WG.getDev, getK, WG.setPeer,
    WG.modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

def rootSlot (v4 : Bool) : WG.Slot := if v4 then .root4 else .root6

def rootWidth (v4 : Bool) : Nat := if v4 then 32 else 128

def rootValue (d : WG.Device) (v4 : Bool) : Option Nat :=
  if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6

def rootWrite (d : WG.Device) (v4 : Bool) (value : Option Nat) : WG.Device :=
  { d with peerAllowedips := if v4 then { d.peerAllowedips with root4 := value }
      else { d.peerAllowedips with root6 := value } }

theorem slotGet_root_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d) (v4 : Bool) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.slotGet (rootSlot v4)
    ⦃⇓ result w => ⌜result = rootValue d v4 ∧ w.k = k⌝⦄ := by
  cases v4 <;> mvcgen [rootSlot, rootValue, WG.slotGet, WG.getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [rootValue]

theorem slotSet_root_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (v4 : Bool) (value : Option Nat) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.slotSet (rootSlot v4) value
    ⦃⇓ result w => ⌜result = () ∧ w.k = { k with wg := some (rootWrite d v4 value) }⌝⦄ := by
  cases v4 <;> mvcgen [rootSlot, WG.slotSet, WG.modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [rootWrite]

theorem connectNode_root_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (v4 : Bool) (id : Nat) (n : WG.AipNode) (hn : d.nodes[id]? = some n) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.connectNode (rootSlot v4) id
    ⦃⇓ result w => ⌜result = () ∧ w.k = { k with wg := some (
      rootWrite { d with nodes := d.nodes.insert id { n with parent := rootSlot v4 } }
        v4 (some id)) }⌝⦄ := by
  cases v4 <;> mvcgen [WG.connectNode, rootSlot, WG.getNode, WG.getDev, getK,
    WG.setNode, WG.modifyDev, modifyK, WG.slotSet, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [rootWrite, rootSlot]

/-- The endpoint retains the two source node writes: allocation with the
detached default backlink, followed by connection with the selected root. -/
def emptyInstalled (d : WG.Device) (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let n := WG.newNode addr cidr (rootWidth v4) (some pid)
  rootWrite { d with
    nextNode := d.nextNode + 1
    nodes := (d.nodes.insert d.nextNode n).insert d.nextNode { n with parent := rootSlot v4 }
    peers := d.peers.insert pid { p with allowedipsList := p.allowedipsList ++ [d.nextNode] } }
    v4 (some d.nextNode)

theorem add_empty_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d v4 = none)
    (hc : cidr ≤ rootWidth v4) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w.k = k) ∨
      (result = 0 ∧ w.k = { k with wg := some (emptyInstalled d v4 addr cidr pid p) })⌝⦄ := by
  have ha := allocNode_wp k d hd .allocNode190 (WG.newNode addr cidr (rootWidth v4) (some pid))
  have hg := slotGet_root_wp k d hd v4
  mvcgen [WG.add, branchCmp, branch, hg, ha, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals try omega
  all_goals cases v4 <;> mvcgen [WG.listAddTail, WG.getPeer, WG.getDev, getK,
    WG.setPeer, WG.modifyDev, modifyK, WG.connectNode, WG.getNode, WG.setNode,
    WG.slotSet, rootSlot, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [allocated, emptyInstalled, rootWrite, rootSlot, rootWidth]
  all_goals subst_vars
  all_goals simp_all

def bumpSeq (d : WG.Device) : WG.Device :=
  { d with peerAllowedips := { d.peerAllowedips with seq := d.peerAllowedips.seq + 1 } }

/-- The original wrapper delegates with the sequence already incremented.
The equation preserves the exact result and complete World on success, and
the exact Stop on failure; a failed run does not return a World. -/
theorem insert_run_bump (w : World) (d : WG.Device) (hd : w.k.wg = some d)
    (family addr cidr pid : Nat) :
    (WG.insert family addr cidr pid).run w =
      (WG.add (rootSlot (family == 4)) (rootWidth (family == 4)) addr cidr (some pid)).run
        { w with k := { w.k with wg := some (bumpSeq d) } } := by
  by_cases hf : family = 4
  · subst family
    simp [WG.insert, WG.modifyDev, modifyK, hd, rootSlot, rootWidth, bumpSeq]
  · simp [WG.insert, WG.modifyDev, modifyK, hd, hf, rootSlot, rootWidth, bumpSeq]

theorem insert_empty_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (family addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d (family == 4) = none)
    (hc : cidr ≤ rootWidth (family == 4)) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.insert family addr cidr pid
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w.k = { k with wg := some (bumpSeq d) }) ∨
      (result = 0 ∧ w.k = { k with wg := some (emptyInstalled (bumpSeq d) (family == 4) addr cidr pid p) })⌝⦄ := by
  have h := add_empty_wp { k with wg := some (bumpSeq d) } (bumpSeq d) rfl
    (family == 4) addr cidr pid p hp he hc
  by_cases hf : family = 4
  · subst family
    simp only [beq_self_eq_true, rootSlot, rootWidth, ↓reduceIte] at h ⊢
    mvcgen [WG.insert, WG.modifyDev, modifyK, h]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [bumpSeq]
  · have hb : (family == 4) = false := by simp [hf]
    simp only [hb, rootSlot, rootWidth, Bool.false_eq_true, ↓reduceIte] at h ⊢
    mvcgen [WG.insert, WG.modifyDev, modifyK, h]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [bumpSeq]

theorem add_empty_exact (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d v4 = none)
    (hc : cidr ≤ rootWidth v4) (result : Int)
    (hr : (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w = .ok (result, w')) :
    (result = -ENOMEM ∧ w'.k = w.k) ∨
      (result = 0 ∧ w'.k = { w.k with wg := some (emptyInstalled d v4 addr cidr pid p) }) :=
  (hoare_iff_triple _ _ _).mpr (add_empty_wp w.k d hd v4 addr cidr pid p hp he hc)
    w result w' rfl hr

theorem insert_empty_exact (w w' : World) (d : WG.Device) (hd : w.k.wg = some d)
    (family addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d (family == 4) = none)
    (hc : cidr ≤ rootWidth (family == 4)) (result : Int)
    (hr : (WG.insert family addr cidr pid).run w = .ok (result, w')) :
    (result = -ENOMEM ∧ w'.k = { w.k with wg := some (bumpSeq d) }) ∨
      (result = 0 ∧ w'.k = { w.k with wg := some (emptyInstalled (bumpSeq d) (family == 4) addr cidr pid p) }) :=
  (hoare_iff_triple _ _ _).mpr (insert_empty_wp w.k d hd family addr cidr pid p hp he hc)
    w result w' rfl hr

theorem emptyInstalled_nodes_other (d : WG.Device) (v4 : Bool) (addr cidr pid : Nat)
    (p : WG.Peer) (id : Nat) (hi : d.nextNode ≠ id) :
    (emptyInstalled d v4 addr cidr pid p).nodes[id]? = d.nodes[id]? := by
  cases v4 <;> simp [emptyInstalled, rootWrite, Std.TreeMap.getElem?_insert, hi]

theorem emptyInstalled_below (d : WG.Device) (hb : NodesBelow d) (v4 : Bool)
    (addr cidr pid : Nat) (p : WG.Peer) :
    NodesBelow (emptyInstalled d v4 addr cidr pid p) := by
  intro id n hn
  change id < d.nextNode + 1
  by_cases hi : d.nextNode = id
  · subst id
    exact Nat.lt_succ_self _
  · rw [emptyInstalled_nodes_other d v4 addr cidr pid p id hi] at hn
    exact Nat.lt_trans (hb id n hn) (Nat.lt_succ_self _)

theorem emptyInstalled_root (d : WG.Device) (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer) :
    rootValue (emptyInstalled d v4 addr cidr pid p) v4 = some d.nextNode := by
  cases v4 <;> rfl

theorem emptyInstalled_other_root (d : WG.Device) (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer) :
    rootValue (emptyInstalled d v4 addr cidr pid p) (!v4) = rootValue d (!v4) := by
  cases v4 <;> rfl

theorem emptyInstalled_seq (d : WG.Device) (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer) :
    (emptyInstalled d v4 addr cidr pid p).peerAllowedips.seq = d.peerAllowedips.seq := by
  cases v4 <;> rfl

theorem emptyInstalled_rep (d : WG.Device) (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer) :
    RepAt (emptyInstalled d v4 addr cidr pid p).nodes (rootWidth v4) (rootSlot v4)
      (Tree.empty.insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree := by
  cases v4 <;> simp [emptyInstalled, rootWrite, rootSlot, rootWidth,
    Tree.insertFresh, graft, requestedLeaf, requestedNode, RepAt, encode, WG.newNode, Tree.root]

theorem emptyInstalled_other_rep (d : WG.Device) (hb : NodesBelow d) (v4 : Bool)
    (addr cidr pid : Nat) (p : WG.Peer) (other : Tree)
    (hr : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other) :
    RepAt (emptyInstalled d v4 addr cidr pid p).nodes (rootWidth (!v4)) (rootSlot (!v4)) other := by
  apply hr.congr
  intro id hi
  have hb' := hr.ids_below hb id hi
  exact emptyInstalled_nodes_other d v4 addr cidr pid p id (Nat.ne_of_gt hb')

end Leanux.Proofs.WG.AllowedIps
