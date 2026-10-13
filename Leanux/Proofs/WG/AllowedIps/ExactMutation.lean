import Leanux.Proofs.WG.AllowedIps.ListsMirror
import Leanux.Proofs.WG.AllowedIps.PlacementMirror

/-! Exact-prefix owner replacement in the original trie mutation. The old
node identifier, unmasked address and all structural fields are retained. -/
set_option pp.structureInstances false
set_option maxHeartbeats 1000000
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

def exactInstalled (d : WG.Device) (id : Nat) (old : WG.AipNode) (pid : Nat) (p : WG.Peer) : WG.Device :=
  { d with
    nodes := d.nodes.insert id { old with peer := some pid }
    peers := (unlisted d id).peers.insert pid
      { unlist id p with allowedipsList := (unlist id p).allowedipsList ++ [id] } }

theorem add_placed_exact_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (v4 : Bool) (trie id addr cidr pid : Nat) (old : WG.AipNode) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hn : d.nodes[id]? = some old)
    (hroot : rootValue d v4 = some trie) (hc : cidr ≤ rootWidth v4)
    (hplacement : ⦃fun w => ⌜w.k = k⌝⦄ WG.nodePlacement (some trie) addr cidr (rootWidth v4)
      ⦃⇓ result w => ⌜result = (some id, true) ∧ w.k = k⌝⦄) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓ result w => ⌜result = 0 ∧ w.k = { k with wg := some (exactInstalled d id old pid p) }⌝⦄ := by
  have hgetRoot := slotGet_root_wp k d hd v4
  simp only [hroot] at hgetRoot
  mvcgen [WG.add, branchCmp, branch, hgetRoot, invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  all_goals try omega
  obtain ⟨hptr, hframe⟩ := (show _ = some trie ∧ _ = k from by assumption)
  cases hptr
  mvcgen [hplacement, branch, invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  rename_i foundId hstart hplaced heq hslotFrame
  subst foundId
  have getter := getNode_wp k d id old hd hn
  mvcgen [getter]
  all_goals try exact hplaced.2
  rename_i fetched
  intro currentGet hget hgetFrame
  subst fetched
  have setter := setNode_wp k d hd id { old with peer := some pid }
  mvcgen [setter]
  all_goals try exact hgetFrame
  rename_i ignored
  intro currentSet hsetFrame
  let dn := { d with nodes := d.nodes.insert id { old with peer := some pid } }
  let kn : Kernel := { k with wg := some dn }
  have deleting := listDel_wp kn dn rfl id
  mvcgen [deleting]
  all_goals try exact hsetFrame
  rename_i ignoredDel
  intro currentDel hdelFrame
  let dl := unlisted dn id
  let kl : Kernel := { k with wg := some dl }
  have hpl : dl.peers[pid]? = some (unlist id p) := by
    rw [unlisted_get]
    simp [dn, hp]
  have appending := listAddTail_wp kl dl rfl pid id (unlist id p) hpl
  mvcgen [appending]
  all_goals try exact hdelFrame
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [exactInstalled, unlisted]
  all_goals grind

theorem add_context_exact_wp (k : Kernel) (d : WG.Device) (hd : k.wg = some d)
    (v4 : Bool) (c : Context) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (.node n l r)).root)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (.node n l r)))
    (hv : (c.plug (.node n l r)).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hn : n.cidr = cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr) :
    ⦃fun w => ⌜w.k = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓ result w => ⌜result = 0 ∧ w.k = { k with wg := some (exactInstalled d n.id
      (encode (rootWidth v4) (c.slot (rootSlot v4)) n l r) pid p) }⌝⦄ := by
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  have placement := nodePlacement_exact_focus_wp k d (rootWidth v4) addr cidr hw ha hc hd c
    (rootSlot v4) n l r hr hv hf hn hm
  obtain ⟨trie, htrie⟩ : ∃ trie, (c.plug (.node n l r)).root = some trie := by
    cases c with
    | here => exact ⟨n.id, rfl⟩
    | left a inner r => exact ⟨a.id, rfl⟩
    | right a l inner => exact ⟨a.id, rfl⟩
  rw [htrie] at placement
  exact add_placed_exact_wp k d hd v4 trie n.id addr cidr pid _ p hp
    (c.focus_rep _ _ hr).1 (hroot.trans htrie) hc placement

end Leanux.Proofs.WG.AllowedIps
