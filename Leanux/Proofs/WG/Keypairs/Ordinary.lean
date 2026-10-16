import Leanux.Proofs.WG.Keypairs.LifetimeMirror
import Leanux.Proofs.Framing.Projection

set_option pp.structureInstances false

/-! Successful original helper executions compose through the ordinary
lifetime-store relation.  No condition is placed on failing executions. -/
namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing

abbrev OrdinaryAction (a : WG.M α) : Prop :=
  Lifetimes.ProjectedAction snapshot Ordinary a

def Stable (P : Snapshot → Prop) : Prop :=
  ∀ s t, Ordinary s t → P s → P t

abbrev SameSnapshot (a : WG.M α) : Prop := SameView snapshot a

theorem SameView.ordinary {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    {a : StateT S m α} (h : SameView project a) : Lifetimes.ProjectedAction project Ordinary a := by
  intro initial
  apply hoare_consequence (h initial) (fun _ hs => hs)
  intro _ w hw
  rw [hw]
  exact .refl _

/-- Preservation of every stable predicate characterizes ordinary executions. -/
theorem ordinaryAction_iff_wp {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    (a : StateT S m α) : Lifetimes.ProjectedAction project Ordinary a ↔
    ∀ P, Stable P → ⦃fun w => ⌜P (project w)⌝⦄ a
      ⦃⇓? _ w => ⌜P (project w)⌝⦄ := by
  constructor
  · intro h; exact Lifetimes.ProjectedAction.wp h
  · intro h initial
    have hp : Stable (Ordinary initial) := fun _ _ ht hs => .trans hs ht
    apply hoare_consequence (h _ hp)
    · intro w hw
      rw [hw]
      exact .refl _
    · intro _ _ hr
      exact hr

theorem ordinaryAction_of_wp {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    (a : StateT S m α)
    (h : ∀ initial, ⦃fun w => ⌜project w = initial⌝⦄ a
      ⦃⇓? _ w => ⌜Ordinary initial (project w)⌝⦄) : Lifetimes.ProjectedAction project Ordinary a :=
  Lifetimes.ProjectedAction.of_wp project Ordinary a h

theorem sameSnapshot_of_wp {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    (a : StateT S m α)
    (h : ∀ initial, ⦃fun w => ⌜project w = initial⌝⦄ a
      ⦃⇓? _ w => ⌜project w = initial⌝⦄) : SameView project a :=
  SameView.of_wp project a h

theorem ordinary_pure (x : α) : OrdinaryAction (pure x) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient y w' ambient' hr
  cases hr
  exact .refl _

theorem ordinary_bind {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    {a : StateT S m α} {f : α → StateT S m β}
    (ha : Lifetimes.ProjectedAction project Ordinary a) (hf : ∀ x, Lifetimes.ProjectedAction project Ordinary (f x)) :
    Lifetimes.ProjectedAction project Ordinary (a >>= f) := by
  apply (ordinaryAction_iff_wp _).mpr
  intro P hp
  exact preserves_bind (Lifetimes.ProjectedAction.wp ha P hp)
    (fun x => Lifetimes.ProjectedAction.wp (hf x) P hp)

theorem keypairGet_sameSnapshot (kp : Option KeypairId) : SameSnapshot (keypairGet kp) := by
  apply sameSnapshot_of_wp
  intro s
  mvcgen [keypairGet, getKeypair, getDev, setKeypair, modifyDev,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    refcountIncNotZero, unsupported, invariant, AmbientM.unsupported, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [snapshot]
  subst s
  apply Snapshot.ext
  · rfl
  · funext j
    simp only [Std.TreeMap.getElem?_insert]
    split <;> simp_all [cell]

theorem keypairGet_ordinary (kp : Option KeypairId) : OrdinaryAction (keypairGet kp) :=
  SameView.ordinary (keypairGet_sameSnapshot kp)

/-- Pure map lemmas discharge the final state update without requiring the
mirror to expose any new helper. -/
def mapSnapshot (frontier : Nat) (keys : Std.TreeMap Nat Keypair) : Snapshot :=
  ⟨frontier, fun i => keys[i]?.map cell⟩

theorem mapSnapshot_insert_same (frontier : Nat) (keys : Std.TreeMap Nat Keypair)
    (i : Nat) (old new : Keypair) (hk : keys[i]? = some old) (hc : cell new = cell old) :
    mapSnapshot frontier (keys.insert i new) = mapSnapshot frontier keys := by
  apply Snapshot.ext
  · rfl
  · funext j
    simp only [mapSnapshot, Std.TreeMap.getElem?_insert]
    split <;> simp_all

theorem ordinary_map_insert_same (frontier : Nat) (keys : Std.TreeMap Nat Keypair)
    (i : Nat) (old new : Keypair) (hk : keys[i]? = some old) (hc : cell new = cell old) :
    Ordinary (mapSnapshot frontier keys) (mapSnapshot frontier (keys.insert i new)) := by
  rw [mapSnapshot_insert_same frontier keys i old new hk hc]
  exact .refl _

theorem ordinary_map_insert_erase (frontier : Nat) (keys : Std.TreeMap Nat Keypair)
    (i : Nat) (new : Keypair) :
    Ordinary (mapSnapshot frontier keys)
      (mapSnapshot frontier ((keys.insert i new).erase i)) := by
  have he : mapSnapshot frontier ((keys.insert i new).erase i) =
      (mapSnapshot frontier keys).put i none := by
    apply Snapshot.ext
    · rfl
    · funext j
      simp [mapSnapshot, Snapshot.put, Std.TreeMap.getElem?_erase,
        Std.TreeMap.getElem?_insert]
      split <;> simp_all [eq_comm]
  rw [he]
  exact .erase _ _

theorem ordinary_map_fresh (frontier : Nat) (keys : Std.TreeMap Nat Keypair)
    (i : Nat) (new : Keypair) (hc : cell new = ⟨frontier + 1, {}⟩) :
    Ordinary (mapSnapshot frontier keys)
      (mapSnapshot (frontier + 1) (keys.insert i new)) := by
  have he : mapSnapshot (frontier + 1) (keys.insert i new) =
      (mapSnapshot frontier keys).fresh i := by
    apply Snapshot.ext
    · rfl
    · funext j
      simp [mapSnapshot, Snapshot.fresh, Std.TreeMap.getElem?_insert]
      split <;> simp_all [eq_comm]
  rw [he]
  exact .fresh _ _

theorem keypairPut_ordinary (kp : Option KeypairId) (now : Bool) :
    OrdinaryAction (keypairPut kp now) := by
  apply ordinaryAction_of_wp
  intro s
  simp only [keypairPut, indexRemove_eq]
  have hd := fun o g => indexOwner_peerDeref_preserves o (fun w => w = g)
  -- The adapter's exact endpoint retains the saved keypair while permitting
  -- each actual removal to replace the index table and consume its records.
  have hu (a : IndexM Unit) (g : WGWorld) : Hoare (monadLift a : WG.M Unit)
      (fun w => w = g)
      (fun _ w => ∃ table, w = {g with dev := g.dev.map fun d => {d with indexTable := table}}) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x w' ambient' hw hr
    subst w
    change ((liftIndex a).run g).run ambient = .ok ((x, w'), ambient') at hr
    rw [liftIndex_run] at hr
    cases hg : g.dev with
    | none => simp [hg] at hr
    | some d =>
      simp only [hg] at hr
      cases ha : (a.run d.indexTable).run ambient with
      | error e => simp [ha, Except.map] at hr
      | ok out =>
        rcases out with ⟨⟨y, table⟩, ambient''⟩
        simp only [ha, Except.map, Except.ok.injEq, Prod.mk.injEq] at hr
        rcases hr with ⟨⟨_, hw⟩, _⟩
        exact ⟨table, by simpa [hg] using hw.symm⟩
  unfold Preserves Hoare at hd hu
  mvcgen [hd, hu, getKeypair, getDev, setKeypair, modifyDev,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    refcountDecAndTest, unsupported, invariant, AmbientM.unsupported, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  -- There are at most two index removals: the optional unreference and release.
  all_goals try obtain ⟨table, rfl⟩ := ‹∃ table, _ = _›
  all_goals try simp_all [snapshot]
  all_goals subst_vars
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [Option.bind_map, Function.comp_def]
  all_goals try obtain ⟨table, rfl⟩ := ‹∃ table, _ = _›
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals subst_vars
  all_goals first
  | exact .refl _
  | exact ordinary_map_insert_erase _ _ _ _
  | apply ordinary_map_insert_same <;> first | assumption | rfl

theorem keypairCreate_ordinary (pid : Option PeerId) : OrdinaryAction (keypairCreate pid) := by
  apply ordinaryAction_of_wp
  intro s
  have alloc_spec : Hoare (hiddenAlloc .kzallocKeypair : WG.M Bool)
      (fun w => snapshot w = s) (fun _ w => snapshot w = s) :=
    hoare_liftAmbient (AmbientM.hiddenAlloc .kzallocKeypair) (fun w => snapshot w = s)
  unfold Hoare at alloc_spec
  mvcgen [keypairCreate, alloc_spec, getDev, setKeypair, modifyDev,
    branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [snapshot]
  all_goals try subst s
  all_goals first
  | exact .refl _
  | rename_i he
    rw [← he]
    apply ordinary_map_fresh
    rfl

end Leanux.Proofs.WG.Keypairs
