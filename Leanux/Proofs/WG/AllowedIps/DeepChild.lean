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
theorem add_placed_gap_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (v4 : Bool) (trie : Nat) (base : WG.Slot) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some trie) (hb : side < 2) (hbelow : NodesBelow d)
    (hnold : d.nodes[n.id]? = some (gapParent (rootWidth v4) base n side sibling))
    (hc : cidr ≤ rootWidth v4) (hlt : n.cidr < cidr)
    (hbit : bit (rootWidth v4) n.cidr addr = side)
    (hplacement : ⦃fun w => ⌜w = k⌝⦄ (MonadLift.monadLift (WG.nodePlacement (some trie) addr cidr (rootWidth v4)) : WG.M (Option Nat × Bool))
      ⦃⇓ result w => ⌜result = (some n.id, false) ∧ w = k⌝⦄) :
    ⦃fun w => ⌜w = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w = k) ∨
      (result = 0 ∧ w = { k with dev := some (gapInstalledAt d v4 base n side sibling addr cidr pid p) })⌝⦄ := by
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
  have halloc : ⦃fun w => ⌜w = k⌝⦄
      (MonadLift.monadLift (WG.allocNode .allocNode205 (WG.newNode addr cidr (rootWidth v4) (some pid))) : WG.M (Option Nat))
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
      · left; refine ⟨rfl, ?_⟩
        change { k with dev := some d } = k
        rw [← hd]
      · right; simp [allocated]
  let leaf := WG.newNode addr cidr (rootWidth v4) (some pid)
  let da := allocated d leaf
  let ka : WGWorld := { k with dev := some da }
  have hlist := listAddTail_wp ka da rfl pid d.nextNode p hp
  let dl := { da with peers := da.peers.insert pid { p with allowedipsList := p.allowedipsList ++ [d.nextNode] } }
  let kl : WGWorld := { k with dev := some dl }
  have hne : d.nextNode ≠ n.id := Nat.ne_of_gt (hbelow n.id _ hnold)
  have hnlisted : dl.nodes[n.id]? = some (gapParent (rootWidth v4) base n side sibling) := by
    simp [dl, da, allocated, Std.TreeMap.getElem?_insert, hne, hnold]
  have getter := read kl dl rfl _ _ (getNode_wp (store dl) n.id
    (gapParent (rootWidth v4) base n side sibling) hnlisted)
  have choosing : ⦃fun w => ⌜w = kl⌝⦄
      (WG.choose (gapParent (rootWidth v4) base n side sibling) addr : WG.M Nat)
      ⦃⇓ x w => ⌜x = side ∧ w = kl⌝⦄ := by
    rw [choose_run _ _ (by simp only [gapParent_cidr, gapParent_bitlen]; omega)]
    simp only [gapParent_cidr, gapParent_bitlen, hbit]
    apply Triple.pure
    intro w
    exact SPred.pure_mono (fun hw => ⟨rfl, hw⟩)
  have hbitAt := gapParent_bitAt_wp (m := AmbientM) kl (rootWidth v4) base n side sibling hb
  have hleaf : dl.nodes[d.nextNode]? = some leaf := by simp [dl, da, allocated]
  have connecting : ⦃fun w => ⌜w = kl⌝⦄
      (MonadLift.monadLift (WG.connectNode (.child n.id side) d.nextNode) : WG.M Unit)
      ⦃⇓ x w => ⌜x = () ∧ w = { k with dev := some (gapInstalledAt d v4 base n side sibling addr cidr pid p) }⌝⦄ := by
    apply total_liftAip_of
    · intro w hw; subst w; exact ⟨dl, rfl⟩
    · intro w d' hw hd'
      subst w
      have hdd : d' = dl := Option.some.inj hd'.symm
      subst d'
      have hs := connectNode_child_wp (store dl) n.id side d.nextNode
        (gapParent (rootWidth v4) base n side sibling) leaf hnlisted hleaf hne (by omega)
      apply (total_iff_run_ambient _ _ _).mpr
      intro entry ambient hi
      obtain ⟨result, finish, finalAmbient, he, hr, hf⟩ :=
        (total_iff_run_ambient _ _ _).mp hs entry ambient hi
      refine ⟨result, finish, finalAmbient, he, ?_⟩
      subst result
      subst finish
      simp [gapInstalledAt, connectedChild, allocated, store, kl, dl, da, leaf]

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
      (result = 0 ∧ w = {k with dev := some (gapInstalledAt d v4 base n side sibling addr cidr pid p)})
  change Hoare (WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)) _ Post
  unfold WG.add
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
    apply branchRule .addNoParentNode false
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply known _ _ kl kl _ _ getter
    apply known _ _ kl kl _ _ choosing
    apply known _ _ kl kl _ _ getter
    apply known _ _ kl kl _ _ hbitAt
    apply branchRule .addNoDown true
    simp only [↓reduceIte]
    apply known _ _ kl _ () _ connecting
    exact hoare_consequence (hoare_pure (0 : Int) _)
      (fun _ h => h) (fun _ _ h => Or.inr h)

theorem add_context_gap_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
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
    ⦃fun w => ⌜w = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w = k) ∨
      (result = 0 ∧ w = { k with dev := some (gapInstalledAt d v4 (c.slot (rootSlot v4)) n side sibling addr cidr pid p) })⌝⦄ := by
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  have hpctx := hf.append (gapContext_follows n side sibling hb hlt hm hbit)
  let store : WG.AipStore := {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}
  have nativePlacement := nodePlacement_empty_focus_wp store (rootWidth v4) addr cidr hw ha hc
    (c.append (gapContext n side sibling)) (rootSlot v4)
    (by simpa only [Context.plug_append, gapContext_plug] using hr)
    (by simpa only [Context.plug_append, gapContext_plug] using hv) hpctx
  have hlast : (gapContext n side sibling).lastParent (c.lastParent none) = some n.id := by
    unfold gapContext
    split <;> rfl
  simp only [Context.plug_append, gapContext_plug, Context.lastParent_append, hlast] at nativePlacement
  obtain ⟨trie, htrie⟩ : ∃ trie, (c.plug (Tree.fork n side .empty sibling)).root = some trie := by
    cases c with
    | here => exact ⟨n.id, Tree.fork_root n side .empty sibling⟩
    | left a inner r => exact ⟨a.id, rfl⟩
    | right a l inner => exact ⟨a.id, rfl⟩
  rw [htrie] at nativePlacement
  have hplacement : ⦃fun w => ⌜w = k⌝⦄
      (MonadLift.monadLift (WG.nodePlacement (some trie) addr cidr (rootWidth v4)) : WG.M (Option Nat × Bool))
      ⦃⇓ result w => ⌜result = (some n.id, false) ∧ w = k⌝⦄ := by
    apply (total_iff_run_ambient _ _ _).mpr
    intro w ambient hw
    subst w
    obtain ⟨x, s, ambient', hrun, hx, hs⟩ :=
      (total_iff_run_ambient _ _ _).mp nativePlacement store ambient rfl
    subst s
    refine ⟨x, k, ambient', ?_, hx, rfl⟩
    change ((WG.liftAip _).run k).run ambient = _
    rw [liftAip_run, hd]
    simp only [store] at hrun
    simp only [hrun, Except.map]
    change Except.ok ((x, {k with dev := some d}), ambient') = _
    rw [← hd]
  exact add_placed_gap_wp k d hd v4 trie (c.slot (rootSlot v4)) n side sibling addr cidr pid p hp
    (hroot.trans htrie) hb hbelow (gap_rep_parts hb (c.focus_rep _ _ hr)).1 hc hlt hbit hplacement

end Leanux.Proofs.WG.AllowedIps
