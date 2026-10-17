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

theorem add_placed_exact_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (v4 : Bool) (trie id addr cidr pid : Nat) (old : WG.AipNode) (p : WG.Peer)
    (hp : d.peers[pid]? = some p) (hn : d.nodes[id]? = some old)
    (hroot : rootValue d v4 = some trie) (hc : cidr ≤ rootWidth v4)
    (hplacement : ⦃fun w => ⌜w = ({nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips} : WG.AipStore)⌝⦄ WG.nodePlacement (some trie) addr cidr (rootWidth v4)
      ⦃⇓ result w => ⌜result = (some id, true) ∧ w = ({nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips} : WG.AipStore)⌝⦄) :
    ⦃fun w => ⌜w = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓ result w => ⌜result = 0 ∧ w = { k with dev := some (exactInstalled d id old pid p) }⌝⦄ := by
  let store (d : WG.Device) : WG.AipStore :=
    {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}
  have read {α : Type} (g : WGWorld) (d : WG.Device) (hd : g.dev = some d)
      (a : WG.AipM α) (value : α)
      (h : ⦃fun s => ⌜s = store d⌝⦄ a ⦃⇓ x s => ⌜x = value ∧ s = store d⌝⦄) :
      ⦃fun w => ⌜w = g⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓ x w => ⌜x = value ∧ w = g⌝⦄ := by
    apply total_liftAip_of
    · intro w hw; subst w; exact ⟨d, hd⟩
    · intro w d' hw hd'
      subst w
      have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
      subst d'
      mvcgen [h]
      all_goals try dsimp +zetaDelta only at *
      all_goals simp_all []
      intro _ _ _
      change {g with dev := some d} = g
      rw [← hd']
  have rootNative := slotGet_root_wp (store d) v4
  have rootValueEq : (if v4 then (store d).trie.root4 else (store d).trie.root6) = some trie := hroot
  simp only [rootValueEq] at rootNative
  have hgetRoot := read k d hd _ _ rootNative
  have placed := read k d hd _ _ hplacement
  have getter := read k d hd _ _ (getNode_wp (store d) id old hn)
  let dn := { d with nodes := d.nodes.insert id { old with peer := some pid } }
  let kn : WGWorld := { k with dev := some dn }
  have setter : ⦃fun w => ⌜w = k⌝⦄
      (MonadLift.monadLift (WG.setNode id {old with peer := some pid}) : WG.M Unit)
      ⦃⇓ result w => ⌜result = () ∧ w = kn⌝⦄ := by
    apply total_liftAip_of
    · intro w hw; subst w; exact ⟨d, hd⟩
    · intro w d' hw hd'
      subst w
      have hdd : d' = d := Option.some.inj (hd'.symm.trans hd)
      subst d'
      have hs := setNode_wp (store d) id {old with peer := some pid}
      mvcgen [hs]
      all_goals try dsimp +zetaDelta only at *
      all_goals simp_all []
  have deleting := listDel_wp kn dn rfl id
  let dl := unlisted dn id
  let kl : WGWorld := { k with dev := some dl }
  have hpl : dl.peers[pid]? = some (unlist id p) := by
    rw [unlisted_get]
    simp [dn, hp]
  have appending := listAddTail_wp kl dl rfl pid id (unlist id p) hpl
  clear read rootNative
  mvcgen [WG.add, branchCmp, AmbientM.branchCmp, branch, AmbientM.branch,
    hgetRoot, invariant, AmbientM.invariant]
  all_goals try dsimp only at *
  all_goals try simp_all
  all_goals try omega
  obtain ⟨hptr, hframe⟩ := (show _ = some trie ∧ _ = k from by assumption)
  cases hptr
  cases hframe
  mvcgen [placed]
  all_goals try dsimp only at *
  obtain ⟨hplaced, hplacedFrame⟩ := (show _ = (some id, true) ∧ _ = k from by assumption)
  cases hplaced
  cases hplacedFrame
  clear hgetRoot placed
  iterate 8
    all_goals try mvcgen [getter, setter, deleting, appending,
      branch, AmbientM.branch, invariant, AmbientM.invariant]
    all_goals try dsimp only at *
    all_goals repeat intro
    all_goals try
      obtain ⟨rfl, rfl⟩ := (show _ = old ∧ _ = k from by assumption)
    all_goals try
      obtain ⟨rfl, rfl⟩ := (show _ = () ∧ _ = kn from by assumption)
    all_goals try
      obtain ⟨rfl, rfl⟩ := (show _ = () ∧ _ = kl from by assumption)
    all_goals try simp_all
    all_goals try simp_all only [kn, kl, dn, dl]
  all_goals clear getter setter deleting appending
  all_goals simp_all [unlisted]
  all_goals grind


theorem add_context_exact_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (v4 : Bool) (c : Context) (n : NodeData) (l r : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = (c.plug (.node n l r)).root)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (c.plug (.node n l r)))
    (hv : (c.plug (.node n l r)).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4)
    (hf : c.Follows (rootWidth v4) addr cidr) (hn : n.cidr = cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr) :
    ⦃fun w => ⌜w = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓ result w => ⌜result = 0 ∧ w = { k with dev := some (exactInstalled d n.id
      (encode (rootWidth v4) (c.slot (rootSlot v4)) n l r) pid p) }⌝⦄ := by
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  let store : WG.AipStore := {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}
  have placement := nodePlacement_exact_focus_wp store (rootWidth v4) addr cidr hw ha hc c
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
