import Leanux.Proofs.WG.AllowedIps.ChildStore

/-! Original empty-child insertion at a represented parent beneath an arbitrary
path. Contexts supply proof evidence; the original `add` remains the operation. -/
set_option pp.structureInstances false
set_option maxHeartbeats 1000000
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

def gapInstalledAt (d : WG.Device) (v4 : Bool) (base : WG.Slot)
    (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) : WG.Device :=
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let listed := { allocated d leaf with peers := (d.peers.insert pid
    { p with allowedipsList := p.allowedipsList ++ [d.nextNode] }) }
  connectedChild listed n.id side d.nextNode
    (gapParent (rootWidth v4) base n side sibling) leaf

/-- Compositional source contract: the supplied original placement contract
must name this parent, and the original selected root must name its input. -/
theorem add_placed_gap_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (v4 : Bool) (trie : Nat) (base : WG.Slot) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some trie) (hb : side < 2) (hbelow : NodesBelow d)
    (hnold : d.nodes[n.id]? = some (gapParent (rootWidth v4) base n side sibling))
    (hc : cidr ≤ rootWidth v4) (hlt : n.cidr < cidr)
    (hbit : bit (rootWidth v4) n.cidr addr = side)
    (hplacement : ⦃fun w => ⌜w.k = k⌝⦄ WG.nodePlacement (some trie) addr cidr (rootWidth v4)
      ⦃⇓ result w => ⌜result = (some n.id, false) ∧ w.k = k⌝⦄) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w.k = k) ∨
      (result = 0 ∧ w.k = { k with wg := some (gapInstalledAt d v4 base n side sibling addr cidr pid p) })⌝⦄ := by
  have hgetRoot := slotGet_root_wp k d hd v4
  simp only [hroot] at hgetRoot
  have halloc := allocNode_wp k d hd .allocNode205 (WG.newNode addr cidr (rootWidth v4) (some pid))
  mvcgen [WG.add, branchCmp, branch, hgetRoot, invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  all_goals try omega
  obtain ⟨hptr, hframe⟩ := (show _ = some trie ∧ _ = k from by assumption)
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
  have hne : d.nextNode ≠ n.id := Nat.ne_of_gt (hbelow n.id _ hnold)
  have hnlisted : dl.nodes[n.id]? = some (gapParent (rootWidth v4) base n side sibling) := by
    simp [dl, da, allocated, Std.TreeMap.getElem?_insert, hne, hnold]
  have getter := getNode_wp kl dl n.id (gapParent (rootWidth v4) base n side sibling) rfl hnlisted
  mvcgen [getter]
  all_goals try (dsimp +zetaDelta only; exact hlisted)
  rename_i fetched
  intro currentGet hget hgetFrame
  subst fetched
  have choosing := choose_wp kl (gapParent (rootWidth v4) base n side sibling) addr
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
  have hbitAt := gapParent_bitAt_wp kl (rootWidth v4) base n side sibling hb
  mvcgen [hbitAt, branch]
  all_goals try exact hgetAgainFrame
  all_goals try dsimp only at *
  all_goals try simp_all
  have hleaf : dl.nodes[d.nextNode]? = some (WG.newNode addr cidr (rootWidth v4) (some pid)) := by
    simp [dl, da, allocated]
  have connecting := connectNode_child_wp kl dl rfl n.id side d.nextNode
    (gapParent (rootWidth v4) base n side sibling)
    (WG.newNode addr cidr (rootWidth v4) (some pid)) hnlisted hleaf hne (by omega)
  mvcgen [connecting]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [gapInstalledAt, allocated]

theorem add_context_gap_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (v4 : Bool) (c : Context) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (Tree.fork n side .empty sibling)).root)
    (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (Tree.fork n side .empty sibling)))
    (hv : (c.plug (Tree.fork n side .empty sibling)).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hlt : n.cidr < cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (hbit : bit (rootWidth v4) n.cidr addr = side) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w.k = k) ∨
      (result = 0 ∧ w.k = { k with wg := some (gapInstalledAt d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p) })⌝⦄ := by
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  have hpctx := hf.append (gapContext_follows n side sibling hb hlt hm hbit)
  have hplacement := nodePlacement_empty_focus_wp k d (rootWidth v4) addr cidr hw ha hc hd
    (c.append (gapContext n side sibling)) (rootSlot v4)
    (by simpa only [Context.plug_append, gapContext_plug] using hr)
    (by simpa only [Context.plug_append, gapContext_plug] using hv) hpctx
  have hlast : (gapContext n side sibling).lastParent (c.lastParent none) = some n.id := by
    unfold gapContext
    split <;> rfl
  simp only [Context.plug_append, gapContext_plug, Context.lastParent_append, hlast] at hplacement
  obtain ⟨trie, htrie⟩ : ∃ trie, (c.plug (Tree.fork n side .empty sibling)).root = some trie := by
    cases c with
    | here => exact ⟨n.id, Tree.fork_root n side .empty sibling⟩
    | left a inner r => exact ⟨a.id, rfl⟩
    | right a l inner => exact ⟨a.id, rfl⟩
  rw [htrie] at hplacement
  exact add_placed_gap_wp k d hd v4 trie (c.slot (rootSlot v4)) n side sibling addr cidr pid p hp
    (hroot.trans htrie) hb hbelow (gap_rep_parts hb (c.focus_rep _ _ hr)).1 hc hlt hbit hplacement

end Leanux.Proofs.WG.AllowedIps
