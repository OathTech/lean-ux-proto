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

  have branchRule {β : Type} (decision : Decision) (value : Bool)
      (P : WGWorld → Prop) (Q : β → WGWorld → Prop) (f : Bool → WG.M β)
      (hf : Hoare (f value) P Q) :
      Hoare ((branch decision value : WG.M Bool) >>= f) P Q := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x out ambient' hi hr
    change ((f value).run w).run _ = .ok ((x, out), ambient') at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ hi hr
  have returned {α β : Type} (a : WG.M α) (value : α) (f : α → WG.M β)
      (P : WGWorld → Prop) (Q : β → WGWorld → Prop)
      (ha : ⦃fun w => ⌜P w⌝⦄ a ⦃⇓ x w => ⌜x = value ∧ P w⌝⦄)
      (hf : Hoare (f value) P Q) : Hoare (a >>= f) P Q := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x out ambient' hi hr
    obtain ⟨y, current, nextAmbient, he, hv, hp⟩ :=
      (total_iff_run_ambient _ _ _).mp ha w ambient hi
    subst y
    simp only [StateT.run_bind, he] at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ hp hr
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
      apply (total_iff_run_ambient _ _ _).mpr
      intro entry ambient hentry
      obtain ⟨result, finish, finalAmbient, hr, hv, hf⟩ :=
        (total_iff_run_ambient _ _ _).mp h entry ambient hentry
      subst result
      subst finish
      refine ⟨value, store, finalAmbient, hr, rfl, ?_⟩
      simpa [store, wgStoreView, ← hgd] using hg
  have hf := read _ _ (findNode_wp store width key hw hk t parent rep valid)
  unfold lookup
  apply hoare_bind _ _ hs
  intro _
  cases he : t.lookup width key with
  | none =>
    have hn : t.lookupId width key = none := by simp [Tree.lookupId, he]
    rw [hn] at hf
    apply returned _ _ _ _ _ hf
    apply branchRule
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result out ambient' _ hr
    cases hr
    simp
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
    rw [hid] at hf
    apply returned _ _ _ _ _ hf
    apply branchRule
    dsimp only [Option.isSome, Bool.true_eq, ite_true]
    apply returned _ _ _ _ _ hg
    apply hoare_bind _ _ (PeerBorrow.acquire_spec n.peer initial)
    intro peer
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result out ambient' hp hr
    cases peer with
    | none =>
      simp [branch, AmbientM.branch, unsupported, AmbientM.unsupported] at hr
      cases hr
    | some pid =>
      simp [branch, AmbientM.branch] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      rcases hp.1 with bad | good
      · contradiction
      · simpa [he, ho] using good
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
  cases v4
  · apply (hoare_iff_run_ambient _ _ _).mp hl w
      (record (record ambient .lookupDstV4 false) .lookupDstV6 true) peer v ambient' rfl
    simpa [lookupDst, getDev, hd, branch, AmbientM.branch, rootValue, rootWidth, record] using hr
  · apply (hoare_iff_run_ambient _ _ _).mp hl w
      (record ambient .lookupDstV4 true) peer v ambient' rfl
    simpa [lookupDst, getDev, hd, branch, AmbientM.branch, rootValue, rootWidth, record] using hr

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
  cases v4
  · apply (hoare_iff_run_ambient _ _ _).mp hl w
      (record (record ambient .lookupSrcV4 false) .lookupSrcV6 true) peer v ambient' rfl
    simpa [lookupSrc, getDev, hd, branch, AmbientM.branch, rootValue, rootWidth, sourceAddress, record] using hr
  · apply (hoare_iff_run_ambient _ _ _).mp hl w
      (record ambient .lookupSrcV4 true) peer v ambient' rfl
    simpa [lookupSrc, getDev, hd, branch, AmbientM.branch, rootValue, rootWidth, sourceAddress, record] using hr

end Leanux.Proofs.WG.AllowedIps
