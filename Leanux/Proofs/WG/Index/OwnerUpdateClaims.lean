import Leanux.Proofs.WG.Index.OwnerIndexFrames
import Leanux.Proofs.WG.Index.ReleaseBounds
import Leanux.Proofs.WG.Noise.RotationSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem keypairPut_ownersFresh (kp : KeypairId) (id : Option KeypairId) (now : Bool) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ keypairPut id now ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨d, device, unique, bounded, small, fresh⟩ := pre
  cases id with
  | none =>
    simp [keypairPut, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨d, device, unique, bounded, small, fresh⟩
  | some id =>
    cases resident : d.keypairs[id]? with
    | none =>
      simp [keypairPut, branch, AmbientM.branch, getKeypair, getDev, device,
        resident, invariant, AmbientM.invariant] at run
      cases run
    | some k =>
      have removeForm : indexRemove (.keypair id) = (do
        _ ← branch .idxRemoveHashed ((← get).any (·.owner == .keypair id))
        modify fun table => table.filter fun e => !(e.owner == .keypair id) : IndexM Unit) := rfl
      have lifted : (monadLift (indexRemove (.keypair id)) : WG.M Unit) =
          liftIndex (indexRemove (.keypair id)) := rfl
      by_cases live : 0 < k.refcount
      · by_cases word : k.peer ≠ none
        · obtain ⟨value, next, nextAmbient, exactRun, finalDevice⟩ :=
            keypairPut_exact id now d k resident live word g ambient device
          rw [run] at exactRun
          cases exactRun
          refine ⟨_, finalDevice, released_owners d id k now unique,
            released_owners_bounded d id k now bounded, ?_, ?_⟩
          · simpa only [released_next] using small
          · intro e member
            rw [released_table] at member
            split at member
            · exact fresh e (List.mem_filter.mp member).1
            · exact fresh e member
        · have peer : k.peer = none := by simpa using word
          cases now with
          | true =>
            simp [keypairPut, branch, AmbientM.branch, getKeypair, getDev, device,
              resident, IndexOwner.peerDeref, IndexOwner.peerWord, peer,
              unsupported, AmbientM.unsupported] at run
            cases run
          | false =>
            cases count : k.refcount with
            | zero => omega
            | succ n =>
              cases n with
              | zero =>
                simp only [keypairPut, lifted] at run
                simp [branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, getKeypair,
                  getDev, device, resident, IndexOwner.peerDeref, IndexOwner.peerWord,
                  peer, setKeypair, modifyDev, refcountDecAndTest, count,
                  unsupported, AmbientM.unsupported] at run
                cases run
              | succ n =>
                simp [keypairPut, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
                  getKeypair, getDev, device, resident, setKeypair, modifyDev,
                  refcountDecAndTest, count] at run
                rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
                exact ⟨_, rfl, unique, bounded, small, fresh⟩
      · have zero : k.refcount = 0 := by omega
        simp only [keypairPut, lifted] at run
        cases now <;> cases peer : k.peer
        all_goals
          simp [branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
            getKeypair, getDev, device, resident, IndexOwner.peerDeref,
            IndexOwner.peerWord, peer, setKeypair, modifyDev, refcountDecAndTest,
            zero, removeForm, liftIndex, invariant, AmbientM.invariant,
            unsupported, AmbientM.unsupported] at run
        all_goals cases run

theorem addNewKeypair_ownersFresh (pid : PeerId) (kp : KeypairId) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ addNewKeypair pid kp ⦃⇓? _ w => ⌜OwnersFresh kp w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  let Q : WGWorld → Prop := OwnersFresh kp
  have hrotation (actions : List RotationAction) : Ensures (rotationExecute pid actions) Q (fun _ => Q) := by
    induction actions with
    | nil =>
      intro g ambient result final after pre run
      cases run
      exact pre
    | cons action rest ih =>
      cases action with
      | write change =>
        change Ensures ((getPeer pid >>= fun p => setPeer pid (change.apply p)) >>=
          fun _ => rotationExecute pid rest) _ _
        refine ensures_bind (Q := fun _ => Q) _ _ ?_ (fun _ => ih)
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid Q)) ?_
        intro p g ambient result final after pre run
        exact (ensures_iff _ _ _).mpr (setPeer_ownersFresh kp pid (change.apply p))
          g ambient result final after pre.1 run
      | put key =>
        exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (keypairPut_ownersFresh kp key true))
          (fun _ => ih)
  have hread : Ensures (getKeypair kp) Q (fun _ => Q) := by
    intro g ambient k final after pre run
    cases device : g.dev with
    | none =>
      simp [getKeypair, getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases key : d.keypairs[kp]? with
      | none =>
        simp [getKeypair, getDev, device, key, invariant, AmbientM.invariant] at run
        cases run
      | some k =>
        simp [getKeypair, getDev, device, key] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) Q (fun _ => Q) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) Q)
  rw [addNewKeypair_rotation_source]
  unfold rotationSource
  refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
  · intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid Q)
      g ambient p final after pre run).1
  · intro p
    refine ensures_bind _ _ hread ?_
    intro k
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro initiator
    cases initiator with
    | false => exact hrotation _
    | true =>
      refine ensures_bind _ _ (hbranch _ _) ?_
      intro hasNext
      cases hasNext <;> exact hrotation _

end Leanux.Proofs.WG.Index
