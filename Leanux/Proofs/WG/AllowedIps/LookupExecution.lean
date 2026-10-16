import Leanux.Proofs.WG.AllowedIps.RoutingTxFrames
import Leanux.Proofs.WG.AllowedIps.AddressBounds

/-! Normal answers of the original acquiring lookup. A represented raw winner
need not be resident: failed acquisition Stops, so no liveness premise or
successful-termination conclusion is added. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

def PeerWinner (width key : Nat) (xs : FlatTable) (peer : Option PeerId) : Prop :=
  ∃ answer, FlatWinner width key xs answer ∧ answer.map Prod.snd = peer

theorem lookup_tree_spec (initial : WGStoreView) (d : Device) (width key : Nat)
    (hw : width = 32 ∨ width = 128) (hk : key < 2 ^ width)
    (hd : initial.dev = some d) (t : Tree) (parent : Slot)
    (rep : RepAt d.nodes width parent t) (valid : t.Valid width) :
    ⦃fun w => ⌜wgStoreView w = initial⌝⦄ lookup t.root width key
    ⦃⇓? result _ => ⌜result = (t.lookup width key).map Entry.peer⌝⦄ := by
  have hs := (Lifetimes.swapEndian_sameWGStore width).wp (fun k => k = initial)
  let store : AipStore := {nodes := d.nodes, nextNode := d.nextNode, trie := d.peerAllowedips}
  have read {α : Type} (a : AipM α) (value : α)
      (h : ⦃fun s => ⌜s = store⌝⦄ a ⦃⇓ x s => ⌜x = value ∧ s = store⌝⦄) :
      ⦃fun w => ⌜wgStoreView w = initial⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓ x w => ⌜x = value ∧ wgStoreView w = initial⌝⦄ := by
    apply total_liftAip_of
    · intro g hg
      exact ⟨d, (congrArg WGStoreView.dev hg).trans hd⟩
    · intro g actual hg hactual
      have hgd : g.dev = some d := (congrArg WGStoreView.dev hg).trans hd
      have he : actual = d := Option.some.inj (hactual.symm.trans hgd)
      subst actual
      mvcgen [h]
      all_goals dsimp +zetaDelta only at *
      all_goals simp_all [store, wgStoreView]
  have hf := read _ _ (findNode_wp store width key hw hk t parent rep valid)
  have ha := fun peer => PeerBorrow.acquire_spec peer initial
  cases he : t.lookup width key with
  | none =>
    have hn : t.lookupId width key = none := by simp [Tree.lookupId, he]
    mvcgen [lookup, hs, hf, ha, branch, AmbientM.branch, invariant, AmbientM.invariant, unsupported, AmbientM.unsupported]
    all_goals simp_all [hn, he]
  | some e =>
    have hm : e ∈ t.entries := by
      have h := Tree.lookup_spec valid key
      rw [he] at h
      exact h.1
    obtain ⟨n, hn⟩ := rep.resident (Tree.entry_mem_nodeIds hm)
    have ho : n.peer = some e.peer := by
      simpa only [hn, Option.bind_some] using rep.entry_owner hm
    have hid : t.lookupId width key = some e.id := by simp [Tree.lookupId, he]
    have hg := read _ _ (getNode_wp store e.id n hn)
    mvcgen [lookup, hs, hf, hg, ha, branch, AmbientM.branch, invariant, AmbientM.invariant, unsupported, AmbientM.unsupported]
    all_goals simp_all [hid, he, ho]
    all_goals mvcgen [hg, ha, branch, AmbientM.branch, invariant, AmbientM.invariant, unsupported, AmbientM.unsupported]
    all_goals simp_all [ho]

/-- The actual reached family root, with no initial successful-acquisition
assumption. The normal result and its longest-prefix witness are both retained. -/
theorem lookup_normal (w v : WGWorld) (ambient ambient' : Ambient) (xs : FlatTable × FlatTable) (v4 : Bool)
    (key : Nat) (hk : key < 2 ^ rootWidth v4) (peer : Option PeerId)
    (hi : RoutedView (routingView w) xs) (d : Device) (hd : w.dev = some d)
    (hr : ((lookup (rootValue d v4) (rootWidth v4) key).run w).run ambient = .ok ((peer, v), ambient')) :
    PeerWinner (rootWidth v4) key (selectedFlat v4 xs) peer ∧
      routingView v = routingView w := by
  obtain ⟨old, t4, t6, hold, hinv, h4, h6⟩ := hi.realize
  have eqd : old = d := Option.some.inj (hold.symm.trans hd)
  subst old
  let t := selectedTree v4 t4 t6
  have he : FlatAgree (rootWidth v4) t (selectedFlat v4 xs) := by
    cases v4 <;> assumption
  have hw : rootWidth v4 = 32 ∨ rootWidth v4 = 128 := by cases v4 <;> simp [rootWidth]
  have hs := lookup_tree_spec (wgStoreView w) d (rootWidth v4) key hw hk hd t (rootSlot v4)
    (hinv.selected_rep v4) (hinv.selected_valid v4)
  have hroot : t.root = rootValue d v4 := (hinv.selected_root v4).symm
  rw [hroot] at hs
  have hp := (hoare_iff_run_ambient _ _ _).mp hs w ambient peer v ambient' rfl hr
  refine ⟨⟨(t.lookup (rootWidth v4) key).map (canonical (rootWidth v4)),
    he.winner (Tree.lookup_spec (hinv.selected_valid v4) key), ?_⟩,
    (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp (lookup_routing _ _ _) w ambient peer v ambient' hr⟩
  rw [hp]
  simp only [Option.map_map, canonical, Function.comp_def]

theorem beAt_bound (bytes : List UInt8) (off len : Nat) :
    beAt bytes off len < 256 ^ len := by
  have h := addressValue_bound ((bytes.drop off).take len)
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

theorem lookup_family_spec (initial : WGStoreView) (xs : FlatTable × FlatTable)
    (hi : RoutedView (initial.dev.map routingState) xs) (d : Device) (hd : initial.dev = some d)
    (v4 : Bool) (key : Nat) (hk : key < 2 ^ rootWidth v4) :
    ⦃fun w => ⌜wgStoreView w = initial⌝⦄ lookup (rootValue d v4) (rootWidth v4) key
    ⦃⇓? result _ => ⌜PeerWinner (rootWidth v4) key (selectedFlat v4 xs) result⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hw hr
  exact (lookup_normal w v ambient ambient' xs v4 key hk result (by simpa only [routingView, ← hw, wgStoreView] using hi)
    d ((congrArg WGStoreView.dev hw).trans hd) hr).1

theorem lookupDst_normal (w v : WGWorld) (ambient ambient' : Ambient) (xs : FlatTable × FlatTable) (v4 : Bool)
    (addr : Nat) (hk : addr < 2 ^ rootWidth v4) (peer : Option PeerId)
    (hi : RoutedView (routingView w) xs)
    (hr : ((lookupDst (if v4 then 4 else 6) addr).run w).run ambient = .ok ((peer, v), ambient')) :
    PeerWinner (rootWidth v4) addr (selectedFlat v4 xs) peer := by
  obtain ⟨d, t4, t6, hd, hinv, h4, h6⟩ := hi.realize
  have hl := lookup_family_spec (wgStoreView w) xs hi d hd v4 addr hk
  have hspec : ⦃fun s => ⌜wgStoreView s = wgStoreView w⌝⦄ lookupDst (if v4 then 4 else 6) addr
      ⦃⇓? result _ => ⌜PeerWinner (rootWidth v4) addr (selectedFlat v4 xs) result⌝⦄ := by
    cases v4 <;> mvcgen [lookupDst, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant, hl]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [wgStoreView, rootValue, rootWidth, selectedFlat]
    all_goals mvcgen [hl]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [wgStoreView, rootValue, rootWidth, selectedFlat]
  exact (hoare_iff_run_ambient _ _ _).mp hspec w ambient peer v ambient' rfl hr

def sourceAddress (v4 : Bool) (bytes : List UInt8) : Nat :=
  if v4 then beAt bytes 12 4 else beAt bytes 8 16

theorem sourceAddress_bound (v4 : Bool) (bytes : List UInt8) :
    sourceAddress v4 bytes < 2 ^ rootWidth v4 := by
  cases v4
  · simpa [sourceAddress, rootWidth] using beAt_bound bytes 8 16
  · simpa [sourceAddress, rootWidth] using beAt_bound bytes 12 4

theorem lookupSrc_normal (w v : WGWorld) (ambient ambient' : Ambient) (xs : FlatTable × FlatTable) (v4 : Bool)
    (bytes : List UInt8) (peer : Option PeerId) (hi : RoutedView (routingView w) xs)
    (hr : ((lookupSrc (if v4 then 4 else 6) bytes).run w).run ambient = .ok ((peer, v), ambient')) :
    PeerWinner (rootWidth v4) (sourceAddress v4 bytes) (selectedFlat v4 xs) peer := by
  obtain ⟨d, t4, t6, hd, hinv, h4, h6⟩ := hi.realize
  have hl := lookup_family_spec (wgStoreView w) xs hi d hd v4 (sourceAddress v4 bytes)
    (sourceAddress_bound v4 bytes)
  have hspec : ⦃fun s => ⌜wgStoreView s = wgStoreView w⌝⦄ lookupSrc (if v4 then 4 else 6) bytes
      ⦃⇓? result _ => ⌜PeerWinner (rootWidth v4) (sourceAddress v4 bytes) (selectedFlat v4 xs) result⌝⦄ := by
    cases v4 <;> mvcgen [lookupSrc, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant, hl]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [wgStoreView, rootValue, rootWidth, selectedFlat, sourceAddress]
    all_goals mvcgen [hl]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [wgStoreView, rootValue, rootWidth, selectedFlat, sourceAddress]
  exact (hoare_iff_run_ambient _ _ _).mp hspec w ambient peer v ambient' rfl hr

end Leanux.Proofs.WG.AllowedIps
