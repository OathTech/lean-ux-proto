import Leanux.Proofs.WG.HandshakeSecurity.ResponderCoreProjection
import Leanux.Proofs.WG.Origins.RetainingTraffic

/-! Native send-side frames retain allocation identity, role and send material
for every surviving key. They do not assume that keys remain resident. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Origins Origins.Retaining Lifetimes

theorem pool_factor (w : WGWorld) :
    pool w = fun kid => ((Origins.view w).bind fun pair => pair.2 kid).map keyCore := by
  funext kid
  cases device : w.dev <;> simp [pool, Origins.view, device]

theorem pool_of_material {a : WG.M α} (h : SameView Origins.view a) : SameView pool a :=
  h.of_factor (fun obs : Origins.View => fun kid => (obs.bind fun pair => pair.2 kid).map keyCore)
    pool pool_factor

theorem pool_get (P : Pool → Prop) (kid : KeypairId) :
    Hoare (getKeypair kid) (fun w => P (pool w))
      (fun k w => P (pool w) ∧ pool w kid = some (keyCore k)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a key v b entry run
  obtain ⟨rfl, _, d, device, resident⟩ := KeyTimes.getKeypair_return kid w v key a b run
  exact ⟨entry, by simp [pool, device, resident]⟩

theorem pool_set (P : Pool → Prop) (kid : KeypairId) (k : Keypair) :
    Hoare (setKeypair kid k) (fun w => P (pool w) ∧ pool w kid = some (keyCore k))
      (fun _ w => P (pool w)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  cases run
  suffices same : pool (CounterWindow.store w kid k) = pool w by
    exact same ▸ entry.1
  funext q
  cases device : w.dev with
  | none => simp [pool, CounterWindow.store, device]
  | some d =>
    by_cases equal : kid = q
    · subst q
      simpa [pool, CounterWindow.store, device] using entry.2.symm
    · simp [pool, CounterWindow.store, device, Std.TreeMap.getElem?_insert, equal]

theorem pool_erase (kid : KeypairId) :
    CoreRetains (modifyDev fun d => {d with keypairs := d.keypairs.erase kid}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  intro q core resident
  cases device : w.dev with
  | none => simp [pool, device] at resident
  | some d =>
    by_cases equal : kid = q
    · subst q
      simp [pool, device] at resident
    · simpa [pool, modifyDev, device, Std.TreeMap.getElem?_erase, equal] using resident

theorem coreUpdateThen (P : Pool → Prop) (kid : KeypairId) (f : Keypair → Keypair)
    (same : ∀ k, keyCore (f k) = keyCore k) (next : Keypair → WG.M α)
    (tail : ∀ k, Preserves (fun w => P (pool w)) (next k)) :
    Preserves (fun w => P (pool w)) (do let k ← getKeypair kid; setKeypair kid (f k); next k) := by
  apply hoare_bind (getKeypair kid) _ (pool_get P kid)
  intro k
  apply hoare_bind (setKeypair kid (f k)) _
  · exact hoare_consequence (pool_set P kid (f k))
      (fun _ h => ⟨h.1, (same k) ▸ h.2⟩) (fun _ _ h => h)
  · intro _
    exact tail k

open Lean Meta Elab Tactic
elab "core_key_update" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple || target.isAppOf ``Preserves) && args.size ≥ 2 do
    throwError "not a contract"
  let action := if target.isAppOf ``Preserves then args.back! else args[args.size-3]!
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let aa := action.getAppArgs
  unless aa[aa.size-2]!.isAppOf ``getKeypair do throwError "not a key read"
  lambdaTelescope aa.back! fun _ body => do
    let rec head : Nat → Expr → Expr
      | 0, e => e
      | n+1, e => match e.consumeMData with
        | .letE _ _ v b _ => head n (b.instantiate1 v)
        | e => e.headBeta
    let body := head 16 body
    unless body.isAppOf ``Bind.bind do throwError "not an immediate update"
    let ba := body.getAppArgs
    unless ba[ba.size-2]!.isAppOf ``setKeypair do throwError "not a key write"
  evalTactic (← `(tactic| apply coreUpdateThen))
  evalTactic (← `(tactic| all_goals try (solve | intro k; rfl)))

macro "core_basic " P:term : tactic => `(tactic|
  first
    | core_key_update
    | (index_material_head getPeer; exact (pool_of_material (getPeer_material _)).wp $P)
    | (index_material_head setPeer; exact (pool_of_material (Origins.setPeer_view _ _)).wp $P)
    | (index_material_head getKeypair; exact (pool_of_material (getKeypair_material _)).wp $P)
    | (index_material_head peerGet; exact (pool_of_material (peerGet_material _)).wp $P)
    | (index_material_head peerPut; exact (pool_of_material (peerPut_material _)).wp $P)
    | (index_material_head IndexOwner.peerDeref; exact (pool_of_material (ownerDeref_material _)).wp $P)
    | (index_material_head IndexOwner.peerWord; exact (pool_of_material (ownerWord_material _)).wp $P)
    | (index_material_head modifyDev; exact (pool_of_material (modifyDev_material _ (fun _ => rfl))).wp $P)
    | (index_material_head getDev; exact (getDev_sameWGStore.factor (fun store : WGStoreView => fun kid => (store.dev.bind fun d => d.keypairs[kid]?).map keyCore)).wp $P)
    | (index_material_head liftIndex; apply hoare_liftIndex; intro w d table h hd; simpa [pool, hd] using h)
    | (index_material_head liftRouting; apply hoare_liftRouting; exact fun _ _ h => h)
    | (first | index_material_head monadLift | index_material_head MonadLift.monadLift | index_material_head MonadLiftT.monadLift
       first
         | exact hoare_liftAmbient _ (fun w => $P (pool w))
         | (apply hoare_liftIndex; intro w d table hw hd
            change $P (fun kid => (d.keypairs[kid]?).map keyCore)
            change $P (fun kid => (w.dev.bind fun d => d.keypairs[kid]?).map keyCore) at hw
            rw [hd] at hw
            exact hw)
         | (apply hoare_liftRouting; exact fun _ _ h => h)
         | simp (config := {failIfUnchanged := true}) only [monadLift_self])
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (first | index_material_head get | index_material_head MonadStateOf.get
       exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
    | (index_material_head modify; apply hoare_modify; intro w hw; exact hw)
    | (first | index_material_head throw | index_material_head MonadExceptOf.throw
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w ambient x v ambient' hi hr
       cases hr)
    | (index_material_head ForIn.forIn; apply list_view_spec pool $P; intro x b)
    | (index_material_head discard; apply discard_view_spec pool $P)
    | material_intro
    | material_reduce
    | material_match
    | (index_material_head ite; split)
    | contradiction)

theorem keypairGet_core (kp : Option KeypairId) : SameView pool (keypairGet kp) := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  cases kp with
  | none =>
    simp [keypairGet, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact entry
  | some id =>
    cases device : w.dev with
    | none =>
      simp [keypairGet, getKeypair, getDev, device, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.keypairs[id]? with
      | none =>
        simp [keypairGet, getKeypair, getDev, device, resident, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at run
        cases run
      | some k =>
        simp only [keypairGet, getKeypair, getDev, setKeypair, modifyDev,
          branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, refcountIncNotZero,
          unsupported, invariant, AmbientM.unsupported, AmbientM.invariant,
          StateT.run_bind] at run
        simp [device, resident] at run
        split at run <;> simp_all
        all_goals try split at run <;> simp_all
        all_goals try split at run <;> simp_all
        all_goals try split at run <;> simp_all
        all_goals first
          | (change (Except.error _ : Except Stop _) = _ at run; cases run)
          | (rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
             refine Eq.trans ?_ entry
             funext q
             by_cases equal : id = q
             · subst q; simp [pool, device, resident, keyCore]
             · simp [pool, device, Std.TreeMap.getElem?_insert, equal])

theorem keypairPut_core (kp : Option KeypairId) (now : Bool) : CoreRetains (keypairPut kp now) := by
  apply ProjectedAction.of_wp
  intro initial
  let P := Retains initial
  let Q := fun w : WGWorld => P (pool w)
  have ambient {α : Type} (a : AmbientM α) (R : WGWorld → Prop) :
      Preserves R (monadLift a : WG.M α) := hoare_liftAmbient a R
  have remove (kid : KeypairId) (R : Pool → Prop) : Preserves (fun w => R (pool w))
      (do let _ ← IndexOwner.peerDeref (.keypair kid); indexRemove (.keypair kid)) := by
    apply preserves_bind (indexOwner_peerDeref_preserves _ _)
    intro _
    rw [indexRemove_eq]
    apply hoare_liftIndex
    intro w d table hi hd
    change R (fun q => (d.keypairs[q]?).map keyCore)
    change R (fun q => (w.dev.bind fun d => d.keypairs[q]?).map keyCore) at hi
    rw [hd] at hi
    exact hi
  suffices run : Preserves Q (keypairPut kp now) from
    hoare_consequence run (fun w h => by change Retains initial (pool w); rw [h]; exact Retains.refl _) (fun _ _ h => h)
  cases kp with
  | none =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a x v b hp hr
    simp [keypairPut, branch, AmbientM.branch] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact hp
  | some kid =>
    unfold keypairPut
    apply preserves_bind (ambient _ Q)
    intro null
    split
    · exact preserves_pure _
    · simp only
      apply hoare_bind _ _ (pool_get P kid)
      intro key
      let R := fun w : WGWorld => Q w ∧ pool w kid = some (keyCore key)
      have unhash : Preserves R
          (do let _ ← IndexOwner.peerDeref (.keypair kid); indexRemove (.keypair kid)) :=
        remove kid (fun s => P s ∧ s kid = some (keyCore key))
      let releaseEntry : WG.M Unit := do
        let _ ← IndexOwner.peerDeref (.keypair kid)
        indexRemove (.keypair kid)
      have afterRef : Hoare (do
          setKeypair kid {key with refcount := key.refcount - 1}
          if ← branch .keypairKrefPutReleased (← refcountDecAndTest key.refcount) then
            releaseEntry
            modifyDev fun d => {d with keypairs := d.keypairs.erase kid})
          R (fun _ => Q) := by
        apply hoare_bind _ _ (pool_set P kid {key with refcount := key.refcount - 1})
        intro _
        change Preserves Q _
        have rc : Preserves Q (refcountDecAndTest key.refcount : WG.M Bool) := by
          unfold refcountDecAndTest
          simp only [branch, branchCmp, unsupported]
          repeat' first
            | (allocation_release_lift_from AmbientM; exact ambient _ Q)
            | allocation_release_step
        apply preserves_bind rc
        intro released
        apply preserves_bind (ambient _ Q)
        intro release
        split
        · exact preserves_bind (remove kid P) (fun _ => (pool_erase kid).wp initial)
        · exact preserves_pure _
      apply hoare_bind _ _ (ambient (AmbientM.branch .keypairPutUnreferenceNow now) R)
      intro unref
      split
      · exact hoare_bind _ _ unhash (fun _ => afterRef)
      · exact afterRef

end Leanux.Proofs.WG.HandshakeSecurity.Responder
