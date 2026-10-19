import Leanux.Proofs.WG.AllowedIps.MutationMirror
import Leanux.Proofs.WG.AllowedIps.PlacementMirror

/-! Exact child-slot mutations and the original insertion into an immediate
empty child. The source's array `set!` behavior is retained explicitly. -/
set_option pp.structureInstances false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.AllowedIps
open Leanux Std.Do Leanux.Proofs.Framing

theorem slotSet_child_wp (k : WG.AipStore)
    (parent side : Nat) (pn : WG.AipNode) (hp : k.nodes[parent]? = some pn)
    (hb : side ≤ 1) (value : Option Nat) :
    ⦃fun w => ⌜w = k⌝⦄ WG.slotSet (.child parent side) value
    ⦃⇓ result w => ⌜result = () ∧ w = { k with nodes := k.nodes.insert parent { pn with bit := pn.bit.set! side value } }⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hw
  subst w
  refine ⟨(), _, ambient, ?_, rfl, rfl⟩
  simp [WG.slotSet, WG.getNode, WG.setNode, hp, show ¬ side > 1 from by omega]

/-- The new node is reparented before the old parent's child slot is written.
The distinctness condition preserves the supplied old-parent snapshot. -/
def connectedChild (d : WG.Device) (parent side id : Nat) (pn n : WG.AipNode) : WG.Device :=
  { d with nodes := ((d.nodes.insert id { n with parent := .child parent side }).insert
      parent { pn with bit := pn.bit.set! side (some id) }) }

theorem connectNode_child_wp (k : WG.AipStore)
    (parent side id : Nat) (pn n : WG.AipNode)
    (hp : k.nodes[parent]? = some pn) (hn : k.nodes[id]? = some n)
    (hne : id ≠ parent) (hb : side ≤ 1) :
    ⦃fun w => ⌜w = k⌝⦄ WG.connectNode (.child parent side) id
    ⦃⇓ result w => ⌜result = () ∧ w = { k with nodes := (k.nodes.insert id { n with parent := .child parent side }).insert parent { pn with bit := pn.bit.set! side (some id) } }⌝⦄ := by
  apply (total_iff_run_ambient _ _ _).mpr
  intro w ambient hkw
  subst w
  refine ⟨(), { k with nodes := (k.nodes.insert id { n with parent := .child parent side }).insert parent { pn with bit := pn.bit.set! side (some id) } }, ambient, ?_, rfl, rfl⟩
  simp [WG.connectNode, WG.getNode, WG.setNode, WG.slotSet, hp, hn,
    Std.TreeMap.getElem?_insert, hne, show ¬ side > 1 from by omega]

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

theorem gapParent_bitAt_wp {σ : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] [MonadLiftT AmbientM (StateT σ m)]
    (k : σ) (width : Nat) (base : WG.Slot) (n : NodeData)
    (side : Nat) (sibling : Tree) (hb : side < 2) :
    ⦃fun w => ⌜w = k⌝⦄ ((gapParent width base n side sibling).bitAt side : StateT σ m (Option Nat))
    ⦃⇓ result w => ⌜result = none ∧ w = k⌝⦄ := by
  have hcases : side = 0 ∨ side = 1 := by omega
  rcases hcases with rfl | rfl <;>
    change ⦃fun w => ⌜w = k⌝⦄ (pure none : StateT σ m (Option Nat))
      ⦃⇓ result w => ⌜result = none ∧ w = k⌝⦄
  all_goals
    apply Triple.pure
    intro w
    exact SPred.pure_mono (fun hw => ⟨rfl, hw⟩)

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

theorem add_root_gap_wp (k : WGWorld) (d : WG.Device) (hd : k.dev = some d)
    (v4 : Bool) (n : NodeData) (side : Nat) (sibling : Tree)
    (addr cidr pid : Nat) (p : WG.Peer) (hp : d.peers[pid]? = some p)
    (hroot : rootValue d v4 = some n.id) (hb : side < 2) (hbelow : NodesBelow d)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) (Tree.fork n side .empty sibling))
    (hv : (Tree.fork n side .empty sibling).Valid (rootWidth v4))
    (ha : addr < 2 ^ rootWidth v4) (hc : cidr ≤ rootWidth v4) (hlt : n.cidr < cidr)
    (hm : prefixBits (rootWidth v4) n.cidr n.addr = prefixBits (rootWidth v4) n.cidr addr)
    (hbit : bit (rootWidth v4) n.cidr addr = side) :
    ⦃fun w => ⌜w = k⌝⦄ WG.add (rootSlot v4) (rootWidth v4) addr cidr (some pid)
    ⦃⇓? result w => ⌜(result = -ENOMEM ∧ w = k) ∨
      (result = 0 ∧ w = { k with dev := some (gapInstalled d v4 n side sibling addr cidr pid p) })⌝⦄ := by
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
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  have hpNative := nodePlacement_empty_focus_wp (store d) (rootWidth v4) addr cidr hw ha hc
    (gapContext n side sibling) (rootSlot v4) (by simpa [gapContext_plug, store] using hr)
    (by simpa [gapContext_plug] using hv) (gapContext_follows n side sibling hb hlt hm hbit)
  have hparent : (gapContext n side sibling).lastParent none = some n.id := by
    unfold gapContext
    split <;> rfl
  simp only [gapContext_plug, Tree.fork_root, hparent] at hpNative
  have hplacement := read k d hd _ _ hpNative
  have rootNative := slotGet_root_wp (store d) v4
  have rootValueEq : (if v4 then (store d).trie.root4 else (store d).trie.root6) = some n.id := hroot
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
  have hnold : d.nodes[n.id]? = some (gapParent (rootWidth v4) (rootSlot v4) n side sibling) := by
    unfold Tree.fork at hr
    unfold gapParent
    split at hr <;> split <;> simp_all [RepAt]
  have hne : d.nextNode ≠ n.id := Nat.ne_of_gt (hbelow n.id _ hnold)
  have hnlisted : dl.nodes[n.id]? = some (gapParent (rootWidth v4) (rootSlot v4) n side sibling) := by
    simp [dl, da, allocated, Std.TreeMap.getElem?_insert, hne, hnold]
  have getter := read kl dl rfl _ _ (getNode_wp (store dl) n.id
    (gapParent (rootWidth v4) (rootSlot v4) n side sibling) hnlisted)
  have choosing : ⦃fun w => ⌜w = kl⌝⦄
      (WG.choose (gapParent (rootWidth v4) (rootSlot v4) n side sibling) addr : WG.M Nat)
      ⦃⇓ x w => ⌜x = side ∧ w = kl⌝⦄ := by
    rw [choose_run _ _ (by simp only [gapParent_cidr, gapParent_bitlen]; omega)]
    simp only [gapParent_cidr, gapParent_bitlen, hbit]
    apply Triple.pure
    intro w
    exact SPred.pure_mono (fun hw => ⟨rfl, hw⟩)
  have hbitAt := gapParent_bitAt_wp (m := AmbientM) kl (rootWidth v4) (rootSlot v4) n side sibling hb
  have hleaf : dl.nodes[d.nextNode]? = some leaf := by simp [dl, da, allocated]
  have connecting : ⦃fun w => ⌜w = kl⌝⦄
      (MonadLift.monadLift (WG.connectNode (.child n.id side) d.nextNode) : WG.M Unit)
      ⦃⇓ x w => ⌜x = () ∧ w = { k with dev := some (gapInstalled d v4 n side sibling addr cidr pid p) }⌝⦄ := by
    apply total_liftAip_of
    · intro w hw; subst w; exact ⟨dl, rfl⟩
    · intro w d' hw hd'
      subst w
      have hdd : d' = dl := Option.some.inj hd'.symm
      subst d'
      have hs := connectNode_child_wp (store dl) n.id side d.nextNode
        (gapParent (rootWidth v4) (rootSlot v4) n side sibling) leaf hnlisted hleaf hne (by omega)
      apply (total_iff_run_ambient _ _ _).mpr
      intro entry ambient hi
      obtain ⟨result, finish, finalAmbient, he, hr, hf⟩ :=
        (total_iff_run_ambient _ _ _).mp hs entry ambient hi
      refine ⟨result, finish, finalAmbient, he, ?_⟩
      subst result
      subst finish
      simp [gapInstalled, connectedChild, allocated, store, kl, dl, da, leaf]
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
      (result = 0 ∧ w = {k with dev := some (gapInstalled d v4 n side sibling addr cidr pid p)})
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

end Leanux.Proofs.WG.AllowedIps
