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

private theorem borrowed_view {w v : WGWorld}
    (hb : PeerBorrow.Borrowed (wgStoreView w) result (wgStoreView v)) :
    view v = view w := by
  change (wgStoreView v).dev.map (fun d => (d.ifindex, fun q => d.keypairs[q]?)) =
    (wgStoreView w).dev.map (fun d => (d.ifindex, fun q => d.keypairs[q]?))
  cases result with
  | none => change wgStoreView v = wgStoreView w at hb; rw [hb]
  | some pid =>
    obtain ⟨d, p, hd, _, _, hk⟩ := hb
    simp [hk, hd]

private theorem keypair_word_read (id : KeypairId) (w v : WGWorld) (word : Option PeerId)
    (ambient ambient' : Ambient)
    (hr : ((IndexOwner.keypair id).peerWord.run w).run ambient = .ok ((word,v),ambient')) :
    ∃ d k, w.dev = some d ∧ d.keypairs[id]? = some k ∧ word = k.peer ∧
      v = w ∧ ambient' = ambient := by
  cases hd : w.dev with
  | none =>
    simp [IndexOwner.peerWord, getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hk : d.keypairs[id]? with
    | none =>
      simp [IndexOwner.peerWord, getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
      cases hr
    | some k =>
      have he : k.peer = word ∧ w = v ∧ ambient = ambient' := by
        simpa [IndexOwner.peerWord, getKeypair, getDev, hd, hk, and_assoc] using hr
      exact ⟨d,k,rfl,hk,he.1.symm,he.2.1.symm,he.2.2.symm⟩

/-- The setter rereads the full resident key, then changes only its peer word.
The native WG and Ambient endpoints are the actual setter's endpoints. -/
theorem keypair_word_store (id : KeypairId) (word : Option PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : (((IndexOwner.keypair id).setPeerWord word).run w).run ambient = .ok (((),v),ambient')) :
    ∃ d k, w.dev = some d ∧ d.keypairs[id]? = some k ∧
      v = CounterWindow.store w id {k with peer := word} ∧ ambient' = ambient := by
  unfold IndexOwner.setPeerWord at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨k,u,readAmbient,hg,hs⟩ := hr
  obtain ⟨hu,ha,d,hd,hk⟩ := KeyTimes.getKeypair_return _ _ _ _ _ _ hg
  subst u
  subst readAmbient
  have he : CounterWindow.store w id {k with peer := word} = v ∧ ambient = ambient' := by
    simpa only [CounterWindow.setKeypair_run, Except.ok.injEq, Prod.mk.injEq, true_and] using hs
  exact ⟨d,k,hd,hk,he.1.symm,he.2.symm⟩

private theorem handshake_word_view (id : PeerId) (word : Option PeerId) :
    SameView view ((IndexOwner.handshake id).setPeerWord word) := by
  exact (getPeer_view id).bind (fun p => setPeer_view id {p with handshakeEntryPeer := word})

/-- On every normal acquisition of a keypair owner, the original full key is
still the fresh setter input. Only its nullable peer word may change; a failed
get can clear that word without invalidating or replacing receiving material. -/
theorem acquireOwner_keypair_effect (id : KeypairId) (w v : WGWorld) (result : Option PeerId)
    (ambient ambient' : Ambient)
    (hr : ((Affiliation.acquireOwner (.keypair id)).run w).run ambient = .ok ((result,v),ambient')) :
    ∃ (d : Device) (old : Keypair), w.dev = some d ∧ d.keypairs[id]? = some old ∧
      WordLe result old.peer ∧
      view v = some (d.ifindex, fun q => if id = q then some {old with peer := result} else d.keypairs[q]?) := by
  obtain ⟨word,a,b,readAmbient,borrowedAmbient,hread,hborrow,hstore⟩ :=
    Affiliation.acquireOwner_acquisition _ _ _ _ _ _ hr
  obtain ⟨d,old,hd,hold,hword,ha,haAmbient⟩ := keypair_word_read id w a word _ _ hread
  subst a
  subst readAmbient
  have hb := (hoare_iff_run_ambient _ _ _).mp (PeerBorrow.acquire_spec word (wgStoreView w))
    w ambient result b borrowedAmbient rfl hborrow
  have hv : view b = view w := borrowed_view hb.2
  obtain ⟨db,fresh,hdb,hfresh,hvout,_⟩ := keypair_word_store id result b v _ _ hstore
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
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  cases owner with
  | handshake id =>
    obtain ⟨word,a,b,readAmbient,borrowedAmbient,hread,hborrow,hstore⟩ :=
      Affiliation.acquireOwner_acquisition _ _ _ _ _ _ hr
    have ha := (hoare_iff_run_ambient _ _ _).mp
      (indexOwner_peerWord_preserves (.handshake id) (fun g => view g = view w))
      w ambient word a readAmbient rfl hread
    have hb := (hoare_iff_run_ambient _ _ _).mp (PeerBorrow.acquire_spec word (wgStoreView a))
      a readAmbient result b borrowedAmbient rfl hborrow
    have hc := (ProjectedAction.iff_run_ambient _ _ _).mp (handshake_word_view id result)
      b borrowedAmbient () v ambient' hstore
    rw [hc,borrowed_view hb.2,ha]
    exact RetainsView.refl _
  | keypair id =>
    obtain ⟨d,old,hd,hk,hw,hv⟩ := acquireOwner_keypair_effect id w v result ambient ambient' hr
    rw [hv]
    have keep := retains_insert d.ifindex (fun q => d.keypairs[q]?) id {old with peer := result}
      (fun valid => ⟨old,hk,valid,rfl,hw⟩)
    simpa only [view,hd,Option.map_some] using keep

elab "index_material_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := ty.getAppArgs
  unless (ty.isAppOf ``Hoare || ty.isAppOf ``Triple) && args.size ≥ 3 do
    Lean.throwError "not an endpoint contract"
  let action := args[args.size - 3]!.consumeMData
  let .const actual _ := action.getAppFn | Lean.throwError "not a constant action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different action"

/-- The original complete index scan, including an ordinary None result after
store-back, retains material. No assumption about indices or owner residency is
needed; original missing-object and other Stops have no returned World. -/
theorem indexLookup_retains (kinds : List IndexKind) (index : Nat) :
    ProjectedAction view RetainsView (indexLookup kinds index) := by
  apply ProjectedAction.of_wp
  intro initial
  let P := RetainsView initial
  have stable : Stable P := fun _ _ hab hi => hi.trans hab
  have hb (decision : Decision) (value : Bool) :
      Hoare (branch decision value : WG.M Bool) (fun w => P (view w)) (fun _ w => P (view w)) :=
    hoare_liftAmbient (AmbientM.branch decision value) _
  have stop {α : Type} (message : String) :
      Hoare (invariant message : WG.M α) (fun w => P (view w)) (fun _ w => P (view w)) :=
    hoare_liftAmbient (AmbientM.invariant message) _
  have hi : Hoare (liftIndex (indexBucket index))
      (fun w => P (view w)) (fun _ w => P (view w)) := by
    apply hoare_liftIndex
    intro g d table hg hd
    simpa only [view, hd, Option.map_some] using hg
  have ha := fun owner => (acquireOwner_retains owner).wp P stable
  suffices h : Hoare (indexLookup kinds index)
      (fun w => P (view w)) (fun _ w => P (view w)) by
    exact hoare_consequence h (fun w hw => by rw [hw]; exact RetainsView.refl _)
      (fun _ _ hp => hp)
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  repeat' first
    | (index_material_head branch; exact hb _ _)
    | (index_material_head invariant; exact stop _)
    | (index_material_head liftIndex; exact hi)
    | (index_material_head Affiliation.acquireOwner; exact ha _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply hoare_bind (Q := fun _ w => P (view w)))
    | (index_material_head ForIn.forIn; apply list_view_spec view P)
    | dsimp (config := {failIfUnchanged := true}) only
    | (run_tac do
        let ty ← (← Lean.Elab.Tactic.getMainGoal).getType
        unless ty.isForall do Lean.throwError "not a binder"
        Lean.Elab.Tactic.evalTactic (← `(tactic| intro x)))
    | split

/-- The existing access observer keeps supplied session support on normal
return and valid prior receipts on Stop. It adds no session occurrence or new
observer hierarchy, and does not establish initialized origin chronology. -/
theorem indexLookup_support (kinds : List IndexKind) (index : Nat) :
    StatePrefixPreserves (fun h w _ => SessionInv h w)
      (MaterialOrigin.Valid SessionOrigin.Receipt.Valid)
      (accessNative (indexLookupPrefix kinds index)) :=
  access_support_native _ _ (indexLookupPrefix_erases kinds index)
    ((ProjectedAction.iff_run_ambient view RetainsView _).mp (indexLookup_retains kinds index))

end Leanux.Proofs.WG.Origins
