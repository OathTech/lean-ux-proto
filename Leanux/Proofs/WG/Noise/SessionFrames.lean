import Leanux.Proofs.WG.Noise.RotationSource
import Leanux.Proofs.WG.Noise.ComponentFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem keypairPut_counter (key : Option KeypairId) (now : Bool) (counter : Nat) :
    ⦃fun w => ⌜w.keypairCounter = counter⌝⦄ keypairPut key now
      ⦃⇓? _ w => ⌜w.keypairCounter = counter⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases key with
  | none =>
    simp [keypairPut, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact pre
  | some id =>
    cases device : g.dev with
    | none =>
      simp [keypairPut, branch, AmbientM.branch, getKeypair, getDev, device,
        invariant, AmbientM.invariant] at run
      cases run
    | some d =>
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
        simp only [keypairPut, lifted] at run
        cases now <;> cases peer : k.peer <;> cases count : k.refcount
        all_goals
          simp [branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
            getKeypair, getDev, device, resident, IndexOwner.peerDeref,
            IndexOwner.peerWord, peer, setKeypair, modifyDev, refcountDecAndTest,
            count, removeForm, liftIndex, unsupported, AmbientM.unsupported] at run
        all_goals try cases run
        all_goals split at run
        all_goals
          simp_all [branch, AmbientM.branch, getDev, modifyDev, liftIndex]
        all_goals cases run
        all_goals rfl

theorem rotationExecute_counter (pid : PeerId) (actions : List RotationAction) (counter : Nat) :
    ⦃fun w => ⌜w.keypairCounter = counter⌝⦄ rotationExecute pid actions
      ⦃⇓? _ w => ⌜w.keypairCounter = counter⌝⦄ := by
  apply (ensures_iff _ _ _).mp
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
      refine ensures_bind (Q := fun _ g => g.keypairCounter = counter) _ _ ?_ (fun _ => ih)
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (getPeer_spec pid (fun g => g.keypairCounter = counter))) ?_
      intro p g ambient result final after pre run
      change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
        {d with peers := d.peers.insert pid (change.apply p)})}), ambient) = _ at run
      cases run
      exact pre.1
    | put key =>
      exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (keypairPut_counter key true counter))
        (fun _ => ih)

theorem addNewKeypair_counter (pid : PeerId) (kp : KeypairId) (counter : Nat) :
    ⦃fun w => ⌜w.keypairCounter = counter⌝⦄ addNewKeypair pid kp
      ⦃⇓? _ w => ⌜w.keypairCounter = counter⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  let Q : WGWorld → Prop := fun g => g.keypairCounter = counter
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
    | false => exact (ensures_iff _ _ _).mpr (rotationExecute_counter pid _ counter)
    | true =>
      refine ensures_bind _ _ (hbranch _ _) ?_
      intro hasNext
      cases hasNext <;> exact (ensures_iff _ _ _).mpr (rotationExecute_counter pid _ counter)

theorem rotationPeer_word (actions : List RotationAction) (p : Peer) :
    (rotationPeer actions p).handshakeEntryPeer = p.handshakeEntryPeer := by
  induction actions generalizing p with
  | nil => rfl
  | cons action rest ih =>
    cases action with
    | put key => exact ih p
    | write change =>
      simp only [rotationPeer, ih]
      cases change <;> rfl

end Leanux.Proofs.WG.Noise
