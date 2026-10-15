import Leanux.Proofs.WG.Origins.SessionMaterial
import Leanux.Proofs.WG.Peers.Affiliation

/-! The actual index acquisition can keep or clear an embedded peer word.
Exact read/borrow/fresh-store equations retain every other keypair field.
The normal-return material frame has no affiliation or reference-credit premise;
the history consequence preserves existing supplied support, not initialized origin. -/
namespace Leanux.Proofs.WG.Origins
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Std.Do
set_option pp.structureInstances false

private theorem borrowed_view (hb : PeerBorrow.Borrowed w.k result v.k) :
    view v = view w := by
  cases result with
  | none => change v.k = w.k at hb; simp [view, hb]
  | some pid =>
    obtain ⟨d, p, hd, _, _, hk⟩ := hb
    simp [view, hk, hd]

private theorem keypair_word_read (id : KeypairId) (w v : World) (word : Option PeerId)
    (hr : (IndexOwner.keypair id).peerWord.run w = .ok (word,v)) :
    ∃ d k, w.k.wg = some d ∧ d.keypairs[id]? = some k ∧ word = k.peer ∧ v = w := by
  cases hd : w.k.wg with
  | none => simp [IndexOwner.peerWord, getKeypair, getDev, getK, hd, invariant] at hr
  | some d =>
    cases hk : d.keypairs[id]? with
    | none => simp [IndexOwner.peerWord, getKeypair, getDev, getK, hd, hk, invariant] at hr
    | some k =>
      have he : k.peer = word ∧ w = v := by
        simpa [IndexOwner.peerWord, getKeypair, getDev, getK, hd, hk] using hr
      exact ⟨d,k,rfl,hk,he.1.symm,he.2.symm⟩

/-- The setter rereads the full resident key, then changes only its peer word.
The returned World is the original setter endpoint, not a projected surrogate. -/
theorem keypair_word_store (id : KeypairId) (word : Option PeerId) (w v : World)
    (hr : ((IndexOwner.keypair id).setPeerWord word).run w = .ok ((),v)) :
    ∃ d k, w.k.wg = some d ∧ d.keypairs[id]? = some k ∧
      v = CounterWindow.store w id {k with peer := word} := by
  unfold IndexOwner.setPeerWord at hr
  rw [MaterialOrigin.bind_ok] at hr
  obtain ⟨k,u,hg,hs⟩ := hr
  obtain ⟨hu,d,hd,hk⟩ := KeyTimes.getKeypair_return _ _ _ _ hg
  subst u
  have he : CounterWindow.store w id {k with peer := word} = v := by
    simpa only [CounterWindow.setKeypair_run, Except.ok.injEq, Prod.mk.injEq, true_and] using hs
  exact ⟨d,k,hd,hk,he.symm⟩

private theorem handshake_word_view (id : PeerId) (word : Option PeerId) :
    SameView view ((IndexOwner.handshake id).setPeerWord word) := by
  exact (getPeer_view id).bind (fun p => setPeer_view id {p with handshakeEntryPeer := word})

/-- On every normal acquisition of a keypair owner, the original full key is
still the fresh setter input. Only its nullable peer word may change; a failed
get can clear that word without invalidating or replacing receiving material. -/
theorem acquireOwner_keypair_effect (id : KeypairId) (w v : World) (result : Option PeerId)
    (hr : (Affiliation.acquireOwner (.keypair id)).run w = .ok (result,v)) :
    ∃ (d : Device) (old : Keypair), w.k.wg = some d ∧ d.keypairs[id]? = some old ∧
      WordLe result old.peer ∧
      view v = some (d.ifindex, fun q => if id = q then some {old with peer := result} else d.keypairs[q]?) := by
  obtain ⟨word,a,b,hread,hborrow,hstore⟩ := Affiliation.acquireOwner_acquisition _ _ _ _ hr
  obtain ⟨d,old,hd,hold,hword,ha⟩ := keypair_word_read id w a word hread
  subst a
  have hb := (hoare_iff_triple _ _ _).mpr (PeerBorrow.acquire_spec word w.k)
    w result b rfl hborrow
  have hv : view b = view w := borrowed_view hb.2
  obtain ⟨db,fresh,hdb,hfresh,hvout⟩ := keypair_word_store id result b v hstore
  have he : (db.ifindex, fun q : KeypairId => db.keypairs[q]?) =
      (d.ifindex, fun q : KeypairId => d.keypairs[q]?) := by
    simpa only [view,hdb,hd,Option.map_some,Option.some.injEq] using hv
  have hm : db.keypairs[id]? = d.keypairs[id]? := congrFun (congrArg Prod.snd he) id
  have hf : fresh = old := Option.some.inj (hfresh.symm.trans (hm.trans hold))
  subst fresh
  refine ⟨d,old,hd,hold,?_,?_⟩
  · rcases hb.1 with hn | hn
    · exact Or.inl hn
    · exact Or.inr (hn.trans hword)
  · rw [hvout]
    simp only [view,CounterWindow.store,hdb,Option.map_some]
    apply congrArg some
    apply Prod.ext
    · change db.ifindex = d.ifindex
      exact congrArg (fun p : Nat × (KeypairId → Option Keypair) => p.1) he
    · funext q
      have hq := congrFun (congrArg Prod.snd he) q
      simp only [Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq]
      split <;> simp_all

theorem acquireOwner_retains (owner : IndexOwner) :
    ProjectedAction view RetainsView (Affiliation.acquireOwner owner) := by
  intro w result v hr
  cases owner with
  | handshake id =>
    obtain ⟨word,a,b,hread,hborrow,hstore⟩ := Affiliation.acquireOwner_acquisition _ _ _ _ hr
    have ha := (kernel (indexOwner_peerWord_sameKernel (.handshake id))) w word a hread
    have hb := (hoare_iff_triple _ _ _).mpr (PeerBorrow.acquire_spec word a.k)
      a result b rfl hborrow
    have hc := handshake_word_view id result b () v hstore
    rw [hc,borrowed_view hb.2,ha]
    exact RetainsView.refl _
  | keypair id =>
    obtain ⟨d,old,hd,hk,hw,hv⟩ := acquireOwner_keypair_effect id w v result hr
    rw [hv]
    have keep := retains_insert d.ifindex (fun q => d.keypairs[q]?) id {old with peer := result}
      (fun valid => ⟨old,hk,valid,rfl,hw⟩)
    simpa only [view,hd,Option.map_some] using keep

/-- The original complete index scan, including an ordinary None result after
store-back, retains material. No assumption about indices or owner residency is
needed; original missing-object and other Stops have no returned World. -/
theorem indexLookup_retains (kinds : List IndexKind) (index : Nat) :
    ProjectedAction view RetainsView (indexLookup kinds index) := by
  apply ProjectedAction.of_wp
  intro initial
  let P := RetainsView initial
  have stable : Stable P := fun _ _ hab hi => hi.trans hab
  have hb := fun decision value => (kernel (sameKernel_branch decision value)).wp P
  have hi := (kernel (Framing.indexBucket_sameKernel index)).wp P
  have ha := fun owner => (acquireOwner_retains owner).wp P stable
  rw [← Affiliation.indexLookupSource_eq]
  mvcgen [Affiliation.indexLookupSource,hb,hi,ha,invariant]
  all_goals try exact ((⇓? _ w => ⌜P (view w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst_vars
  all_goals first | assumption | exact RetainsView.refl _ | exact fun h => h

/-- The existing access observer keeps supplied session support on normal
return and valid prior receipts on Stop. It adds no session occurrence or new
observer hierarchy, and does not establish initialized origin chronology. -/
theorem indexLookup_support (kinds : List IndexKind) (index : Nat) :
    PrefixPreserves SessionInv (MaterialOrigin.Valid SessionOrigin.Receipt.Valid)
      (MaterialOrigin.access (indexLookupPrefix kinds index)) :=
  access_support _ _ (indexLookupPrefix_erases kinds index) (indexLookup_retains kinds index)

end Leanux.Proofs.WG.Origins
