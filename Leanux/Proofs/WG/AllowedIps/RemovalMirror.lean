import Leanux.Proofs.WG.AllowedIps.RemovalSource
import Leanux.Proofs.WG.AllowedIps.GraftStore

/-! Total local removal endpoints. The raw node values retain all source
fields; no owner residency or peer-list coherence is required. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

def removalRecords (w : Ambient) (xs : List (Decision × Bool)) : Ambient :=
  xs.foldl (fun w e => record w e.1 e.2) w

def removalCleared (d : WG.Device) (id : Nat) (n : WG.AipNode) : WG.Device :=
  { d with nodes := d.nodes.insert id { n with peer := none } }

def removalRootLeaf (d : WG.Device) (v4 : Bool) (id : Nat) (n : WG.AipNode) : WG.Device :=
  let dc := rootWrite (removalCleared d id n) v4 none
  { dc with nodes := dc.nodes.erase id }

def removalRootUnary (d : WG.Device) (v4 : Bool) (id : Nat) (n : WG.AipNode)
    (child : Nat) (cn : WG.AipNode) : WG.Device :=
  let dc := removalCleared d id n
  let dr := { dc with nodes := dc.nodes.insert child { cn with parent := rootSlot v4 } }
  let linked := rootWrite dr v4 (some child)
  { linked with nodes := linked.nodes.erase id }

theorem removeNodeBody_binary_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (id left right : Nat) (n : WG.AipNode) (hn : d.nodes[id]? = some n)
    (hbits : n.bit = #[some left, some right]) :
    ⦃fun w => ⌜w = k⌝⦄ removeNodeBody id
    ⦃⇓ result w => ⌜result = .yield () ∧
      w = { k with dev := some (removalCleared d id n) }⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hkw
  subst w
  refine ⟨.yield (), { k with dev := some (removalCleared d id n) },
    removalRecords ambient [(.removeHasBit0, true), (.removeHasBit1, true)], ?_, rfl, rfl⟩
  simp [removeNodeBody, liftM, MonadLiftT.monadLift, MonadLift.monadLift, WG.getNode, WG.getDev, WG.liftAip, WG.setNode,
    WG.modifyDev, WG.AipNode.bitAt, branch, AmbientM.branch, hd, hn, hbits,
    removalCleared, removalRecords, record]
  rfl

theorem removeNodeBody_root_leaf_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (v4 : Bool) (id : Nat) (n : WG.AipNode) (hn : d.nodes[id]? = some n)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = rootSlot v4) :
    ⦃fun w => ⌜w = k⌝⦄ removeNodeBody id
    ⦃⇓ result w => ⌜result = .yield () ∧
      w = { k with dev := some (removalRootLeaf d v4 id n) }⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hkw
  subst w
  refine ⟨.yield (), { k with dev := some (removalRootLeaf d v4 id n) },
    removalRecords ambient [(.removeHasBit0, false),
      (.removeChildExists, false), (.removeLeafBit0, true), (.removeLeafBit1, true),
      (.removeParentIsNode, false), (.removeFreeParent, false), (.removeNotFreeParent, true)],
    ?_, rfl, rfl⟩
  cases v4 <;> simp [removeNodeBody, liftM, MonadLiftT.monadLift, MonadLift.monadLift, WG.getNode, WG.getDev, WG.liftAip, WG.setNode,
    WG.modifyDev, WG.AipNode.bitAt, WG.slotSet, WG.freeNode, branch, AmbientM.branch,
    hd, hn, hbits, hparent, rootSlot, removalRootLeaf, removalCleared,
    rootWrite, removalRecords, record]
  all_goals rfl

theorem removeNodeBody_root_unary_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (v4 left : Bool) (id child : Nat) (n cn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hc : d.nodes[child]? = some cn)
    (hne : id ≠ child)
    (hbits : n.bit = if left then #[some child, none] else #[none, some child])
    (hparent : n.parent = rootSlot v4) :
    ⦃fun w => ⌜w = k⌝⦄ removeNodeBody id
    ⦃⇓ result w => ⌜result = .yield () ∧
      w = { k with dev := some (removalRootUnary d v4 id n child cn) }⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hkw
  subst w
  let events : List (Decision × Bool) := if left then [(.removeHasBit0, true), (.removeHasBit1, false),
    (.removeChildExists, true), (.removeLeafBit0, false),
    (.removeFreeParent, false), (.removeNotFreeParent, true)] else
    [(.removeHasBit0, false), (.removeChildExists, true), (.removeLeafBit0, true),
    (.removeLeafBit1, false), (.removeFreeParent, false), (.removeNotFreeParent, true)]
  refine ⟨.yield (), { k with dev := some (removalRootUnary d v4 id n child cn) },
    removalRecords ambient events, ?_, rfl, rfl⟩
  cases v4 <;> cases left <;> simp [removeNodeBody, liftM, MonadLiftT.monadLift, MonadLift.monadLift, WG.getNode, WG.getDev, WG.liftAip,
    WG.setNode, WG.modifyDev, WG.AipNode.bitAt, WG.slotSet, WG.freeNode,
    branch, AmbientM.branch, hd, hn, hc, hbits, hparent, rootSlot, removalRootUnary,
    removalCleared, rootWrite, removalRecords, record, events,
    Std.TreeMap.getElem?_insert, hne, Ne.symm hne]
  all_goals rfl

theorem removeStep_binary_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (id left right : Nat) (n : WG.AipNode) (hn : d.nodes[id]? = some n)
    (hbits : n.bit = #[some left, some right]) :
    ⦃fun w => ⌜w = k⌝⦄ removeStep id
    ⦃⇓ result w => ⌜result = .yield () ∧
      w = { k with dev := some (removalCleared (unlisted d id) id n) }⌝⦄ := by
  have hl := listDel_wp k d hd id
  have hb := removeNodeBody_binary_wp { k with dev := some (unlisted d id) }
    (unlisted d id) rfl id left right n hn hbits
  mvcgen [removeStep, branch, AmbientM.branch, hl, hb]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem removeStep_root_leaf_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (v4 : Bool) (id : Nat) (n : WG.AipNode) (hn : d.nodes[id]? = some n)
    (hbits : n.bit = #[none, none]) (hparent : n.parent = rootSlot v4) :
    ⦃fun w => ⌜w = k⌝⦄ removeStep id
    ⦃⇓ result w => ⌜result = .yield () ∧
      w = { k with dev := some (removalRootLeaf (unlisted d id) v4 id n) }⌝⦄ := by
  have hl := listDel_wp k d hd id
  have hb := removeNodeBody_root_leaf_wp { k with dev := some (unlisted d id) }
    (unlisted d id) rfl v4 id n hn hbits hparent
  mvcgen [removeStep, branch, AmbientM.branch, hl, hb]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem removeStep_root_unary_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (v4 left : Bool) (id child : Nat) (n cn : WG.AipNode)
    (hn : d.nodes[id]? = some n) (hc : d.nodes[child]? = some cn)
    (hne : id ≠ child)
    (hbits : n.bit = if left then #[some child, none] else #[none, some child])
    (hparent : n.parent = rootSlot v4) :
    ⦃fun w => ⌜w = k⌝⦄ removeStep id
    ⦃⇓ result w => ⌜result = .yield () ∧
      w = { k with dev := some (removalRootUnary (unlisted d id) v4 id n child cn) }⌝⦄ := by
  have hl := listDel_wp k d hd id
  have hb := removeNodeBody_root_unary_wp { k with dev := some (unlisted d id) }
    (unlisted d id) rfl v4 left id child n cn hn hc hne hbits hparent
  mvcgen [removeStep, branch, AmbientM.branch, hl, hb]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

end Leanux.Proofs.WG.AllowedIps
