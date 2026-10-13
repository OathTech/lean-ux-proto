import Leanux.Spikes.LifetimeMirror

set_option pp.structureInstances false

/-! Successful original helper executions compose through the ordinary
lifetime-store relation.  No condition is placed on failing executions. -/
namespace Leanux.Spikes.Lifetimes
open Leanux Leanux.WG Std.Do Leanux.Spikes.Framing

def OrdinaryAction (a : M α) : Prop :=
  ∀ w x w', a.run w = .ok (x, w') → Ordinary (snapshot w) (snapshot w')

def Stable (P : Snapshot → Prop) : Prop :=
  ∀ s t, Ordinary s t → P s → P t

def SameSnapshot (a : M α) : Prop :=
  ∀ w x w', a.run w = .ok (x, w') → snapshot w' = snapshot w

theorem SameSnapshot.ordinary {a : M α} (h : SameSnapshot a) : OrdinaryAction a := by
  intro w x w' hr
  rw [h w x w' hr]
  exact .refl _

theorem sameSnapshot_of_sameKernel {a : M α} (h : SameKernel a) : SameSnapshot a := by
  intro w x w' hr
  simp only [snapshot, h w x w' hr]

theorem SameSnapshot.wp {a : M α} (h : SameSnapshot a) (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ a ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x w' hw hr
  simpa only [h w x w' hr] using hw

theorem OrdinaryAction.wp {a : M α} (h : OrdinaryAction a) (P : Snapshot → Prop)
    (hp : Stable P) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ a ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x w' hw hr
  exact hp _ _ (h w x w' hr) hw

/-- Preservation of every stable predicate characterizes ordinary executions. -/
theorem ordinaryAction_iff_wp (a : M α) : OrdinaryAction a ↔
    ∀ P, Stable P → ⦃fun w => ⌜P (snapshot w)⌝⦄ a
      ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  constructor
  · intro h; exact h.wp
  · intro h w x w' hr
    have hp : Stable (Ordinary (snapshot w)) := fun _ _ ht hs => .trans hs ht
    exact (hoare_iff_triple _ _ _).mpr (h _ hp) w x w' (.refl _) hr

theorem ordinaryAction_of_wp (a : M α)
    (h : ∀ s, ⦃fun w => ⌜snapshot w = s⌝⦄ a
      ⦃⇓? _ w => ⌜Ordinary s (snapshot w)⌝⦄) : OrdinaryAction a := by
  intro w x w' hr
  exact (hoare_iff_triple _ _ _).mpr (h (snapshot w)) w x w' rfl hr

theorem sameSnapshot_of_wp (a : M α)
    (h : ∀ s, ⦃fun w => ⌜snapshot w = s⌝⦄ a
      ⦃⇓? _ w => ⌜snapshot w = s⌝⦄) : SameSnapshot a := by
  intro w x w' hr
  exact (hoare_iff_triple _ _ _).mpr (h (snapshot w)) w x w' rfl hr

theorem ordinary_pure (x : α) : OrdinaryAction (pure x) := by
  intro w y w' hr
  cases hr
  exact .refl _

theorem ordinary_bind {a : M α} {f : α → M β}
    (ha : OrdinaryAction a) (hf : ∀ x, OrdinaryAction (f x)) :
    OrdinaryAction (a >>= f) := by
  intro w y w' hr
  simp only [StateT.run_bind] at hr
  cases hx : a.run w with
  | error e => simp [hx] at hr
  | ok v =>
    simp only [hx, Leanux.Spikes.Window.except_ok_bind] at hr
    exact .trans (ha w v.1 v.2 hx) (hf v.1 v.2 y w' hr)

theorem keypairGet_sameSnapshot (kp : Option KeypairId) : SameSnapshot (keypairGet kp) := by
  apply sameSnapshot_of_wp
  intro s
  mvcgen [keypairGet, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, branchCmp, refcountIncNotZero, unsupported, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [snapshot]
  subst s
  apply Snapshot.ext
  · rfl
  · funext j
    simp only [Std.TreeMap.getElem?_insert]
    split <;> simp_all [cell]

theorem keypairGet_ordinary (kp : Option KeypairId) : OrdinaryAction (keypairGet kp) :=
  (keypairGet_sameSnapshot kp).ordinary

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
  mvcgen [keypairPut, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, branchCmp, refcountDecAndTest, unsupported, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [snapshot]
  all_goals try subst s
  all_goals first
  | exact .refl _
  | exact ordinary_map_insert_erase _ _ _ _
  | apply ordinary_map_insert_same <;> first | assumption | rfl

theorem keypairCreate_ordinary (pid : PeerId) : OrdinaryAction (keypairCreate pid) := by
  apply ordinaryAction_of_wp
  intro s
  have alloc_spec := sameKernel_wp _ keypairAllocation_sameKernel
    (fun k => (⟨k.keypairCounter, fun i => (k.wg.bind fun d => d.keypairs[i]?).map cell⟩ : Snapshot) = s)
  mvcgen [keypairCreate, alloc_spec, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [snapshot]
  all_goals try subst s
  all_goals first
  | exact .refl _
  | rename_i he
    rw [← he]
    apply ordinary_map_fresh
    rfl

end Leanux.Spikes.Lifetimes
