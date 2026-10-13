import Leanux.Proofs.WG.AllowedIps.MutationMirror
import Leanux.Proofs.WG.AllowedIps.PlacementMirror

/-! Exact child-slot mutations and the original insertion into an immediate
empty child. The source's array `set!` behavior is retained explicitly. -/
set_option pp.structureInstances false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

theorem slotSet_child_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (parent side : Nat) (pn : WG.AipNode) (hp : d.nodes[parent]? = some pn)
    (hb : side ≤ 1) (value : Option Nat) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.slotSet (.child parent side) value
    ⦃⇓ result w => ⌜result = () ∧ w.k = { k with wg := some (
      { d with nodes := d.nodes.insert parent { pn with bit := pn.bit.set! side value } }) }⌝⦄ := by
  mvcgen [WG.slotSet, WG.getNode, WG.getDev, getK, WG.setNode, WG.modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals omega

/-- The new node is reparented before the old parent's child slot is written.
The distinctness condition preserves the supplied old-parent snapshot. -/
def connectedChild (d : WG.Device) (parent side id : Nat) (pn n : WG.AipNode) : WG.Device :=
  { d with nodes := ((d.nodes.insert id { n with parent := .child parent side }).insert
      parent { pn with bit := pn.bit.set! side (some id) }) }

theorem connectNode_child_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (parent side id : Nat) (pn n : WG.AipNode)
    (hp : d.nodes[parent]? = some pn) (hn : d.nodes[id]? = some n)
    (hne : id ≠ parent) (hb : side ≤ 1) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.connectNode (.child parent side) id
    ⦃⇓ result w => ⌜result = () ∧ w.k = { k with wg := some (connectedChild d parent side id pn n) }⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w hkw
  refine ⟨(), { w with k := { k with wg := some (connectedChild d parent side id pn n) } }, ?_, rfl, rfl⟩
  simp [WG.connectNode, WG.getNode, WG.getDev, getK, WG.setNode, WG.modifyDev,
    modifyK, WG.slotSet, hkw, hd, hp, hn, Std.TreeMap.getElem?_insert, hne,
    show ¬ side > 1 from by omega, connectedChild]

def gapContext (n : NodeData) (side : Nat) (sibling : Tree) : Context :=
  if side = 0 then .left n .here sibling else .right n sibling .here

def gapParent (width : Nat) (base : WG.Slot) (n : NodeData) (side : Nat) (sibling : Tree) : WG.AipNode :=
  if side = 0 then encode width base n .empty sibling else encode width base n sibling .empty

@[simp] theorem gapParent_cidr (width : Nat) (base : WG.Slot) (n : NodeData) (side : Nat) (sibling : Tree) :
    (gapParent width base n side sibling).cidr = n.cidr := by
  unfold gapParent
  split <;> rfl

@[simp] theorem gapParent_bitlen (width : Nat) (base : WG.Slot) (n : NodeData) (side : Nat) (sibling : Tree) :
    (gapParent width base n side sibling).bitlen = width := by
  unfold gapParent
  split <;> rfl

theorem gapParent_bitAt_wp (k : Kernel) (width : Nat) (base : WG.Slot) (n : NodeData)
    (side : Nat) (sibling : Tree) (hb : side < 2) :
    ⦃fun w => ⌜w.k = k⌝⦄ (gapParent width base n side sibling).bitAt side
    ⦃⇓ result w => ⌜result = none ∧ w.k = k⌝⦄ := by
  apply (total_iff_run _ _ _).mpr
  intro w hkw
  have hcases : side = 0 ∨ side = 1 := by omega
  rcases hcases with rfl | rfl <;> exact ⟨none, w, rfl, rfl, hkw⟩

theorem gapContext_plug (n : NodeData) (side : Nat) (sibling u : Tree) :
    (gapContext n side sibling).plug u = Tree.fork n side u sibling := by
  unfold gapContext Tree.fork
  split <;> rfl

theorem gapContext_follows (n : NodeData) (side : Nat) (sibling : Tree) (hb : side < 2)
    (hlt : n.cidr < cidr) (hm : prefixBits width n.cidr n.addr = prefixBits width n.cidr key)
    (hbit : bit width n.cidr key = side) : (gapContext n side sibling).Follows width key cidr := by
  have hcases : side = 0 ∨ side = 1 := by omega
  rcases hcases with rfl | rfl <;> exact ⟨hlt, hm, hbit, trivial⟩

def gapInstalled (d : WG.Device) (v4 : Bool) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let listed := { allocated d leaf with peers := (d.peers.insert pid
    { p with allowedipsList := p.allowedipsList ++ [d.nextNode] }) }
  connectedChild listed n.id side d.nextNode
    (gapParent (rootWidth v4) (rootSlot v4) n side sibling) leaf

theorem add_root_gap_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (v4 : Bool) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (Tree.fork n side .empty sibling))
    (hv : (Tree.fork n side .empty sibling).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4) (hlt : n.cidr < cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (hbit : bit (rootWidth v4) n.cidr addr = side) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w.k = k) ∨
      (result = 0 ∧ w.k = { k with wg := some (gapInstalled d v4 n side sibling addr cidr pid p) })⌝⦄ := by
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  have hplacement := nodePlacement_empty_focus_wp k d (rootWidth v4) addr cidr hw ha hc hd
    (gapContext n side sibling) (rootSlot v4) (by simpa [gapContext_plug] using hr)
    (by simpa [gapContext_plug] using hv) (gapContext_follows n side sibling hb hlt hm hbit)
  have hparent : (gapContext n side sibling).lastParent none = some n.id := by
    unfold gapContext
    split <;> rfl
  simp only [gapContext_plug, Tree.fork_root, hparent] at hplacement
  have hgetRoot := slotGet_root_wp k d hd v4
  simp only [hroot] at hgetRoot
  have halloc := allocNode_wp k d hd .allocNode205 (WG.newNode addr cidr (rootWidth v4) (some pid))
  mvcgen [WG.add, branchCmp, branch, hgetRoot, invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  all_goals try omega
  obtain ⟨hptr, hframe⟩ := (show _ = some n.id ∧ _ = k from by assumption)
  cases hptr
  mvcgen [hplacement, branch, invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  obtain ⟨hplaced, hplacedFrame⟩ := (show _ = (some n.id, false) ∧ _ = k from by assumption)
  cases hplaced
  mvcgen [halloc, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  rename_i alloc current hcases step hn newId heq hpre
  rcases hcases with ⟨hNone, _⟩ | ⟨hSome, hak⟩
  · rw [hNone] at heq
    cases heq
  have hid : newId = d.nextNode := by
    rw [hSome] at heq
    exact (Option.some.inj heq).symm
  subst newId
  let da := allocated d (WG.newNode addr cidr (rootWidth v4) (some pid))
  let ka : Kernel := { k with wg := some da }
  have hlist := listAddTail_wp ka da rfl pid d.nextNode p hp
  mvcgen [hlist, branch, invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  rename_i hlisted
  let dl := { da with peers := da.peers.insert pid { p with allowedipsList := p.allowedipsList ++ [d.nextNode] } }
  let kl : Kernel := { k with wg := some dl }
  change _ = kl at hlisted
  have hnold : d.nodes[n.id]? = some (gapParent (rootWidth v4) (rootSlot v4) n side sibling) := by
    unfold Tree.fork at hr
    unfold gapParent
    split at hr <;> split <;> simp_all [RepAt]
  have hne : d.nextNode ≠ n.id := Nat.ne_of_gt (hbelow n.id _ hnold)
  have hnlisted : dl.nodes[n.id]? = some (gapParent (rootWidth v4) (rootSlot v4) n side sibling) := by
    simp [dl, da, allocated, Std.TreeMap.getElem?_insert, hne, hnold]
  have getter := getNode_wp kl dl n.id (gapParent (rootWidth v4) (rootSlot v4) n side sibling) rfl hnlisted
  mvcgen [getter]
  all_goals try (dsimp +zetaDelta only; exact hlisted)
  rename_i fetched
  intro currentGet hget hgetFrame
  subst fetched
  have choosing := choose_wp kl (gapParent (rootWidth v4) (rootSlot v4) n side sibling) addr
    (by simp only [gapParent_cidr, gapParent_bitlen]; omega)
  simp only [gapParent_cidr, gapParent_bitlen, hbit] at choosing
  mvcgen [choosing]
  all_goals try exact hgetFrame
  rename_i chosen
  intro currentChoose hchoose hchooseFrame
  subst chosen
  mvcgen [getter]
  all_goals try exact hchooseFrame
  rename_i fetchedAgain
  intro currentGetAgain hgetAgain hgetAgainFrame
  subst fetchedAgain
  have hbitAt := gapParent_bitAt_wp kl (rootWidth v4) (rootSlot v4) n side sibling hb
  mvcgen [hbitAt, branch]
  all_goals try exact hgetAgainFrame
  all_goals try dsimp only at *
  all_goals try simp_all
  have hleaf : dl.nodes[d.nextNode]? = some (WG.newNode addr cidr (rootWidth v4) (some pid)) := by
    simp [dl, da, allocated]
  have connecting := connectNode_child_wp kl dl rfl n.id side d.nextNode
    (gapParent (rootWidth v4) (rootSlot v4) n side sibling)
    (WG.newNode addr cidr (rootWidth v4) (some pid)) hnlisted hleaf hne (by omega)
  mvcgen [connecting]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [gapInstalled, allocated]

end Leanux.Proofs.WG.AllowedIps
