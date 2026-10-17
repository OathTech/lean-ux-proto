import Leanux.Proofs.WG.AllowedIps.StoreMutation
import Leanux.Proofs.WG.Keypairs.Frames.WGBase

/-! Original allowed-IP mutation contracts. Normal-return statements retain
record failures as errors; they do not assume every choice stream completes. -/
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

def allocated (d : WG.Device) (n : WG.AipNode) : WG.Device :=
  { d with nextNode := d.nextNode + 1, nodes := d.nodes.insert d.nextNode n }

theorem allocNode_wp (k : WG.AipStore) (site : AllocSite) (n : WG.AipNode) :
    ⦃fun w => ⌜w = k⌝⦄ WG.allocNode site n
    ⦃⇓? result w => ⌜(result = none ∧ w = k) ∨
      (result = some k.nextNode ∧ w = { k with nextNode := k.nextNode + 1, nodes := k.nodes.insert k.nextNode n })⌝⦄ := by
  have hs : Hoare (hiddenAlloc site : WG.AipM Bool) (fun w => w = k) (fun _ w => w = k) :=
    hoare_liftAmbient (AmbientM.hiddenAlloc site) _
  unfold Hoare at hs
  mvcgen [WG.allocNode, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem setNode_wp (k : WG.AipStore) (id : Nat) (n : WG.AipNode) :
    ⦃fun w => ⌜w = k⌝⦄ WG.setNode id n
    ⦃⇓ result w => ⌜result = () ∧ w = { k with nodes := k.nodes.insert id n }⌝⦄ := by
  mvcgen [WG.setNode]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem listAddTail_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (pid id : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p) :
    ⦃fun w => ⌜w = k⌝⦄ WG.listAddTail pid id
    ⦃⇓ result w => ⌜result = () ∧ w = { k with dev := some { d with
      peers := d.peers.insert pid { p with allowedipsList := p.allowedipsList ++ [id] } } }⌝⦄ := by
  mvcgen [WG.listAddTail, WG.getPeer, WG.getDev, WG.setPeer,
    WG.modifyDev, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

def rootSlot (v4 : Bool) : WG.Slot := if v4 then .root4 else .root6

def rootWidth (v4 : Bool) : Nat := if v4 then 32 else 128

def rootValue (d : WG.Device) (v4 : Bool) : Option Nat :=
  if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6

def rootWrite (d : WG.Device) (v4 : Bool) (value : Option Nat) : WG.Device :=
  { d with peerAllowedips := if v4 then { d.peerAllowedips with root4 := value }
      else { d.peerAllowedips with root6 := value } }

theorem slotGet_root_wp (k : WG.AipStore) (v4 : Bool) :
    ⦃fun w => ⌜w = k⌝⦄ WG.slotGet (rootSlot v4)
    ⦃⇓ result w => ⌜result = (if v4 then k.trie.root4 else k.trie.root6) ∧ w = k⌝⦄ := by
  cases v4 <;> mvcgen [rootSlot, WG.slotGet]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem slotSet_root_wp (k : WG.AipStore) (v4 : Bool) (value : Option Nat) :
    ⦃fun w => ⌜w = k⌝⦄ WG.slotSet (rootSlot v4) value
    ⦃⇓ result w => ⌜result = () ∧ w = { k with trie :=
      if v4 then { k.trie with root4 := value } else { k.trie with root6 := value } }⌝⦄ := by
  cases v4 <;> mvcgen [rootSlot, WG.slotSet]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem connectNode_root_wp (k : WG.AipStore)
    (v4 : Bool) (id : Nat) (n : WG.AipNode) (hn : k.nodes[id]? = some n) :
    ⦃fun w => ⌜w = k⌝⦄ WG.connectNode (rootSlot v4) id
    ⦃⇓ result w => ⌜result = () ∧ w = { k with nodes := k.nodes.insert id { n with parent := rootSlot v4 }, trie := if v4 then { k.trie with root4 := some id } else { k.trie with root6 := some id } }⌝⦄ := by
  cases v4 <;> mvcgen [WG.connectNode, rootSlot, WG.getNode,
    WG.setNode, WG.slotSet, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [rootSlot]

/-- The endpoint retains the two source node writes: allocation with the
detached default backlink, followed by connection with the selected root. -/
def emptyInstalled (d : WG.Device) (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let n := WG.newNode addr cidr (rootWidth v4) (some pid)
  rootWrite { d with
    nextNode := d.nextNode + 1
    nodes := (d.nodes.insert d.nextNode n).insert d.nextNode { n with parent := rootSlot v4 }
    peers := d.peers.insert pid { p with allowedipsList := p.allowedipsList ++ [d.nextNode] } }
    v4 (some d.nextNode)

theorem add_empty_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d v4 = none)
    (hc : cidr ≤ rootWidth v4) :
    ⦃fun w => ⌜w = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w = k) ∨
      (result = 0 ∧ w = { k with dev := some (emptyInstalled d v4 addr cidr pid p) })⌝⦄ := by
  have ha : ⦃fun w => ⌜w = k⌝⦄
      (MonadLift.monadLift (WG.allocNode .allocNode190 (WG.newNode addr cidr (rootWidth v4) (some pid))) : WG.M (Option Nat))
      ⦃⇓? result w => ⌜(result = none ∧ w = k) ∨
        (result = some d.nextNode ∧ w = { k with dev := some (allocated d (WG.newNode addr cidr (rootWidth v4) (some pid))) })⌝⦄ := by
    apply hoare_liftAip_of
    intro g d' hg hd'
    subst g
    have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
    subst d'
    apply hoare_consequence (allocNode_wp _ _ _)
    · intro s h; exact h
    · intro r s h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left
        refine ⟨rfl, ?_⟩
        change { k with dev := some d } = k
        rw [← hd]
      · right; simp [allocated]
  have hg : ⦃fun w => ⌜w = k⌝⦄ (MonadLift.monadLift (WG.slotGet (rootSlot v4)) : WG.M (Option Nat))
      ⦃⇓ result w => ⌜result = rootValue d v4 ∧ w = k⌝⦄ := by
    apply (total_iff_run_ambient _ _ _).mpr
    intro g ambient h
    subst g
    obtain ⟨r, s, b, hr, h⟩ := (total_iff_run_ambient _ _ _).mp
      (slotGet_root_wp {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips} v4)
      _ ambient rfl
    rcases h with ⟨hrv, rfl⟩
    refine ⟨r, k, b, ?_, ?_⟩
    · change ((WG.liftAip (WG.slotGet (rootSlot v4))).run k).run ambient = _
      rw [liftAip_run, hd]
      simp only [hr, Except.map]
      change Except.ok ((r, { k with dev := some d }), b) = Except.ok ((r, k), b)
      rw [← hd]
    · simpa [rootValue] using hrv
  let n := WG.newNode addr cidr (rootWidth v4) (some pid)
  let listed : WG.Device := { allocated d n with
    peers := d.peers.insert pid { p with allowedipsList := p.allowedipsList ++ [d.nextNode] } }
  have hl := listAddTail_wp { k with dev := some (allocated d n) } (allocated d n)
    rfl pid d.nextNode p hp
  have hconnect : ⦃fun w => ⌜w = { k with dev := some listed }⌝⦄
      (MonadLift.monadLift (WG.connectNode (rootSlot v4) d.nextNode) : WG.M Unit)
      ⦃⇓? result w => ⌜result = () ∧
        w = { k with dev := some (emptyInstalled d v4 addr cidr pid p) }⌝⦄ := by
    apply hoare_liftAip_of
    intro g d' hg hd'
    subst g
    have hdd : d' = listed := Option.some.inj hd'.symm
    subst d'
    have hn : listed.nodes[d.nextNode]? = some n := by simp [listed, allocated]
    have hs := connectNode_root_wp
      {nodes := listed.nodes, nextNode := listed.nextNode, trie := listed.peerAllowedips}
      v4 d.nextNode n hn
    unfold Hoare
    mvcgen [hs]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [allocated, emptyInstalled, rootWrite]
  mvcgen [WG.add, branchCmp, AmbientM.branchCmp, branch, AmbientM.branch,
    hg, ha, hl, hconnect, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals clear ha hg
  all_goals subst_vars
  all_goals try simp_all [rootValue]
  all_goals try omega
  all_goals mvcgen [hl, hconnect]
  all_goals try dsimp +zetaDelta only at *
  all_goals clear hl hconnect
  all_goals cases v4 <;> simp_all [allocated, emptyInstalled, rootWrite, rootSlot, rootWidth]

def bumpSeq (d : WG.Device) : WG.Device :=
  { d with peerAllowedips := { d.peerAllowedips with seq := d.peerAllowedips.seq + 1 } }

/-- The original wrapper delegates with the sequence already incremented.
The equation preserves the exact result and both native state endpoints on
success, and the exact Stop on failure; a failed run returns no state. -/
theorem insert_run_bump (w : WGWorld) (ambient : Ambient) (d : WG.Device) (hd : w.dev = some d)
    (family addr cidr pid : Nat) :
    ((WG.insert family addr cidr pid).run w).run ambient =
      ((WG.add (rootSlot (family == 4)) (rootWidth (family == 4)) addr cidr (some pid)).run
        { w with dev := some (bumpSeq d) }).run ambient := by
  by_cases hf : family = 4
  · subst family
    simp [WG.insert, WG.modifyDev, hd, rootSlot, rootWidth, bumpSeq]
  · simp [WG.insert, WG.modifyDev, hd, hf, rootSlot, rootWidth, bumpSeq]

theorem insert_empty_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (family addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d (family == 4) = none)
    (hc : cidr ≤ rootWidth (family == 4)) :
    ⦃fun w => ⌜w = k⌝⦄ WG.insert family addr cidr pid
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w = { k with dev := some (bumpSeq d) }) ∨
      (result = 0 ∧ w = { k with dev := some (emptyInstalled (bumpSeq d) (family == 4) addr cidr pid p) })⌝⦄ := by
  have h := add_empty_wp { k with dev := some (bumpSeq d) } (bumpSeq d) rfl
    (family == 4) addr cidr pid p hp he hc
  by_cases hf : family = 4
  · subst family
    simp only [beq_self_eq_true, rootSlot, rootWidth, ↓reduceIte] at h ⊢
    mvcgen [WG.insert, WG.modifyDev, h]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [bumpSeq]
  · have hb : (family == 4) = false := by simp [hf]
    simp only [hb, rootSlot, rootWidth, Bool.false_eq_true, ↓reduceIte] at h ⊢
    mvcgen [WG.insert, WG.modifyDev, h]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [bumpSeq]

theorem add_empty_exact (w w' : WGWorld) (ambient ambient' : Ambient)
    (d : WG.Device) (hd : w.dev = some d)
    (v4 : Bool) (addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d v4 = none)
    (hc : cidr ≤ rootWidth v4) (result : Int)
    (hr : ((WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)).run w).run ambient =
      .ok ((result, w'), ambient')) :
    (result = -ENOMEM ∧ w' = w) ∨
      (result = 0 ∧ w' = { w with dev := some (emptyInstalled d v4 addr cidr pid p) }) :=
  (hoare_iff_run_ambient _ _ _).mp (add_empty_wp w d hd v4 addr cidr pid p hp he hc)
    w ambient result w' ambient' rfl hr

theorem insert_empty_exact (w w' : WGWorld) (ambient ambient' : Ambient)
    (d : WG.Device) (hd : w.dev = some d)
    (family addr cidr pid : Nat) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (he : rootValue d (family == 4) = none)
    (hc : cidr ≤ rootWidth (family == 4)) (result : Int)
    (hr : ((WG.insert family addr cidr pid).run w).run ambient = .ok ((result, w'), ambient')) :
    (result = -ENOMEM ∧ w' = { w with dev := some (bumpSeq d) }) ∨
      (result = 0 ∧ w' = { w with dev := some (emptyInstalled (bumpSeq d) (family == 4) addr cidr pid p) }) :=
  (hoare_iff_run_ambient _ _ _).mp (insert_empty_wp w d hd family addr cidr pid p hp he hc)
    w ambient result w' ambient' rfl hr

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
