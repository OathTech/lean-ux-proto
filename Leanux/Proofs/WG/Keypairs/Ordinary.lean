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
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases kp with
  | none =>
    simp [keypairGet, branch, AmbientM.branch] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact hp
  | some id =>
    cases hd : w.dev with
    | none =>
      simp [keypairGet, getKeypair, getDev, hd, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[id]? with
      | none =>
        simp [keypairGet, getKeypair, getDev, hd, hk, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at hr
        cases hr
      | some key =>
        simp only [keypairGet, getKeypair, getDev, setKeypair, modifyDev,
          branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, refcountIncNotZero,
          unsupported, invariant, AmbientM.unsupported, AmbientM.invariant,
          StateT.run_bind] at hr
        simp [hd, hk] at hr
        split at hr <;> simp_all
        all_goals try split at hr <;> simp_all
        all_goals try split at hr <;> simp_all
        all_goals try split at hr <;> simp_all
        all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        all_goals
          first
          | exact hp
          | have he := snapshot_store w d id {key with refcount := key.refcount + 1} hd
            simp only [Leanux.Proofs.WG.CounterWindow.store, hd, Option.map_some] at he
            rw [he]
            change (snapshot w).put id (some (cell key)) = initial
            rw [put_existing _ _ _ (snapshot_lookup w d id key hd hk)]
            exact hp

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
  have read (id : KeypairId) (P : Snapshot → Prop) :
      Hoare (getKeypair id) (fun w => P (snapshot w))
        (fun key w => P (snapshot w) ∧ (snapshot w).slots id = some (cell key)) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient key w' ambient' hp hr
    cases hd : w.dev with
    | none =>
      simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[id]? with
      | none =>
        simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
        cases hr
      | some value =>
        rw [Leanux.Proofs.WG.CounterWindow.getKeypair_run w ambient d id value hd hk] at hr
        cases hr
        exact ⟨hp, snapshot_lookup w d id key hd hk⟩
  have write (id : KeypairId) (key : Keypair) (P : Snapshot → Prop) :
      Hoare (setKeypair id key)
        (fun w => P (snapshot w) ∧ (snapshot w).slots id = some (cell key))
        (fun _ w => P (snapshot w)) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x w' ambient' hp hr
    cases hd : w.dev with
    | none => simp [snapshot, hd] at hp
    | some d =>
      rw [Leanux.Proofs.WG.CounterWindow.setKeypair_run] at hr
      cases hr
      rw [snapshot_store w d id key hd, put_existing _ _ _ hp.2]
      exact hp.1
  have unhash (id : KeypairId) :
      SameSnapshot (monadLift (indexRemove (.keypair id)) : WG.M Unit) := by
    intro initial
    apply hoare_liftIndex
    intro g d table hp hd
    simpa [snapshot, hd] using hp
  have owner (id : KeypairId) : SameSnapshot (IndexOwner.peerDeref (.keypair id)) :=
    fun initial => indexOwner_peerDeref_preserves _ (fun w => snapshot w = initial)
  have erase (id : KeypairId) :
      OrdinaryAction (modifyDev fun d => {d with keypairs := d.keypairs.erase id}) := by
    apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x w' ambient' hr
    change Except.ok (((), _), ambient) = Except.ok ((x, w'), ambient') at hr
    cases hr
    cases hd : w.dev with
    | none =>
      simpa [snapshot, hd] using Ordinary.refl (snapshot w)
    | some d =>
      have he : snapshot {w with dev := some {d with keypairs := d.keypairs.erase id}} =
          (snapshot w).put id none := by
        apply Snapshot.ext
        · rfl
        · funext j
          simp [snapshot, hd, Snapshot.put, Std.TreeMap.getElem?_erase]
          split <;> simp_all [eq_comm]
      simpa only [hd, Option.map_some, he] using Ordinary.erase (snapshot w) id
  apply (ordinaryAction_iff_wp _).mpr
  intro P stable
  let Q := fun w => P (snapshot w)
  have rc (old : Nat) : Preserves Q (refcountDecAndTest old : WG.M Bool) := by
    let finish : WG.M Bool := do
      if ← branch .refcountSubNonpositive (old == 0) then
        unsupported "refcount_warn_saturate (use after free)"
      if ← branch .refcountSubUnderflow (old < 1) then
        unsupported "refcount_warn_saturate (underflow)"
      return false
    have finishP : Preserves Q finish := by
      unfold finish
      apply preserves_bind (hoare_liftAmbient
        (AmbientM.branch .refcountSubNonpositive (old == 0)) Q)
      intro bad
      cases bad with
      | true =>
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro w a x w' a' _ hr
        change Except.error _ = Except.ok _ at hr
        cases hr
      | false =>
        apply preserves_bind (hoare_liftAmbient
          (AmbientM.branch .refcountSubUnderflow (old < 1)) Q)
        intro bad
        cases bad with
        | true =>
          apply (hoare_iff_run_ambient _ _ _).mpr
          intro w a x w' a' _ hr
          change Except.error _ = Except.ok _ at hr
          cases hr
        | false => exact preserves_pure false
    unfold refcountDecAndTest
    apply preserves_bind (hoare_liftAmbient
      (AmbientM.branchCmp .refcountSubPositive (old > 0) old 0) Q)
    intro positive
    cases positive with
    | false => exact finishP
    | true =>
      apply preserves_bind (hoare_liftAmbient
        (AmbientM.branchCmp .refcountSubToZero (old == 1) old 1) Q)
      intro released
      cases released
      · exact finishP
      · exact preserves_pure true
  unfold keypairPut
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .keypairPutNull kp.isNone) Q)
  intro null
  cases null with
  | true => exact preserves_pure ()
  | false =>
    cases kp with
    | none => exact hoare_liftAmbient (AmbientM.invariant "unreachable") Q
    | some id =>
      apply hoare_bind _ _ (read id P)
      intro key
      dsimp only
      let saved := fun s : Snapshot => P s ∧ s.slots id = some (cell key)
      let tail : WG.M Unit := do
        setKeypair id {key with refcount := key.refcount - 1}
        if ← branch .keypairKrefPutReleased (← refcountDecAndTest key.refcount) then
          _ ← IndexOwner.peerDeref (.keypair id)
          (indexRemove (.keypair id) : WG.M Unit)
          modifyDev fun d => {d with keypairs := d.keypairs.erase id}
      have tailP : Hoare tail (fun w => saved (snapshot w)) (fun _ => Q) := by
        unfold tail
        apply hoare_bind _ _ (write id {key with refcount := key.refcount - 1} P)
        intro _
        apply preserves_bind (rc key.refcount)
        intro released
        apply preserves_bind (hoare_liftAmbient
          (AmbientM.branch .keypairKrefPutReleased released) Q)
        intro free
        cases free with
        | false => exact preserves_pure ()
        | true =>
          apply preserves_bind ((owner id).wp P)
          intro _
          apply preserves_bind ((unhash id).wp P)
          intro _
          exact (erase id).wp P stable
      apply hoare_bind _ _ (hoare_liftAmbient
        (AmbientM.branch .keypairPutUnreferenceNow now) (fun w => saved (snapshot w)))
      intro run
      cases run with
      | false =>
        simpa only [tail, Bool.false_eq_true, ite_false, bind_assoc] using tailP
      | true =>
        simp only [bind_assoc]
        apply hoare_bind _ _ ((owner id).wp saved)
        intro _
        apply hoare_bind _ _ ((unhash id).wp saved)
        intro _
        simpa only [tail, bind_assoc] using tailP

theorem keypairCreate_ordinary (pid : Option PeerId) : OrdinaryAction (keypairCreate pid) := by
  unfold keypairCreate
  apply ordinary_bind (SameView.ordinary (fun initial => hoare_liftAmbient
    (AmbientM.hiddenAlloc .kzallocKeypair) (fun w => snapshot w = initial)))
  intro allocated
  apply ordinary_bind (SameView.ordinary (fun initial => hoare_liftAmbient
    (AmbientM.branch .keypairCreateNoMem (!allocated)) (fun w => snapshot w = initial)))
  intro failed
  cases failed with
  | true => exact ordinary_pure none
  | false =>
    apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x w' ambient' hr
    cases hd : w.dev with
    | none =>
      simp [getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      simp [getDev, modifyDev, setKeypair, hd] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      simpa only [snapshot, hd, Option.bind_some, mapSnapshot,
        List.replicate_succ, List.replicate_zero] using
        ordinary_map_fresh w.keypairCounter d.keypairs d.nextKeypairId
          {internalId := w.keypairCounter + 1, peer := pid} rfl

end Leanux.Proofs.WG.Keypairs
