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
    apply (total_iff_run_ambient _ _ _).mpr
    intro w ambient hw
    subst w
    refine ⟨(), kn, ambient, ?_, rfl, rfl⟩
    change ((WG.liftAip (WG.setNode id {old with peer := some pid})).run k).run ambient = _
    rw [liftAip_run, hd]
    rfl
  have deleting := listDel_wp kn dn rfl id
  let dl := unlisted dn id
  let kl : WGWorld := { k with dev := some dl }
  have hpl : dl.peers[pid]? = some (unlist id p) := by
    rw [unlisted_get]
    simp [dn, hp]
  have appending := listAddTail_wp kl dl rfl pid id (unlist id p) hpl
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hw
  subst w
  let a1 := Leanux.Proofs.WG.CounterWindow.recordCmp ambient .addCidrTooLong false cidr (rootWidth v4)
  let a2 := Leanux.Proofs.WG.CounterWindow.record a1 .addNoPeer false
  obtain ⟨x, g, a3, hr, hx, hg⟩ := (total_iff_run_ambient _ _ _).mp hgetRoot k a2 rfl
  subst x g
  let a4 := Leanux.Proofs.WG.CounterWindow.record a3 .addEmptyTrie false
  obtain ⟨x, g, a5, ht, hx, hg⟩ := (total_iff_run_ambient _ _ _).mp placed k a4 rfl
  subst x g
  let a6 := Leanux.Proofs.WG.CounterWindow.record a5 .addExact true
  obtain ⟨x, g, a7, hnrun, hx, hg⟩ := (total_iff_run_ambient _ _ _).mp getter k a6 rfl
  subst x g
  obtain ⟨x, g, a8, hs, hx, hg⟩ := (total_iff_run_ambient _ _ _).mp setter k a7 rfl
  subst x g
  obtain ⟨x, g, a9, hdRun, hx, hg⟩ := (total_iff_run_ambient _ _ _).mp deleting kn a8 rfl
  subst x g
  obtain ⟨x, g, a10, haRun, hx, hg⟩ := (total_iff_run_ambient _ _ _).mp appending kl a9 rfl
  subst x g
  change ((monadLift (WG.slotGet (rootSlot v4)) : WG.M _).run k).run a2 =
    .ok ((some trie, k), a3) at hr
  change ((monadLift (WG.nodePlacement (some trie) addr cidr (rootWidth v4)) : WG.M _).run k).run a4 =
    .ok (((some id, true), k), a5) at ht
  change ((monadLift (WG.getNode id) : WG.M _).run k).run a6 = .ok ((old, k), a7) at hnrun
  change ((monadLift (WG.setNode id {old with peer := some pid}) : WG.M _).run k).run a7 =
    .ok (((), kn), a8) at hs
  change ((WG.listDel id).run kn).run a8 = .ok (((), kl), a9) at hdRun
  change ((WG.listAddTail pid id).run kl).run a9 =
    .ok (((), { k with dev := some (exactInstalled d id old pid p) }), a10) at haRun
  dsimp only [a1, a2] at hr
  dsimp only [a4] at ht
  dsimp only [a6] at hnrun
  refine ⟨0, { k with dev := some (exactInstalled d id old pid p) }, a10, ?_, rfl, rfl⟩
  have hcidr : decide (cidr > rootWidth v4) = false := by simp [Nat.not_lt.mpr hc]
  simp only [WG.add, branchCmp, branch, Leanux.Proofs.WG.CounterWindow.branchCmp_run,
    Leanux.Proofs.WG.CounterWindow.branch_run, StateT.run_bind, StateT.run_pure,
    StateT.run_monadLift, monadLift_self, liftM, Leanux.Proofs.WG.CounterWindow.except_ok_bind,
    Leanux.Proofs.WG.CounterWindow.except_pure, hcidr, Bool.false_eq_true,
    Option.isNone_some, ↓reduceIte, hr, ht, hnrun, hs, hdRun, haRun]


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
