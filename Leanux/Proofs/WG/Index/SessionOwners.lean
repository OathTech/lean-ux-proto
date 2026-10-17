import Leanux.Proofs.WG.Index.OwnerUpdateClaims
import Leanux.Proofs.WG.Index.SessionOperations

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

def allocatedOwners (created : Option KeypairId) (w : WGWorld) : Prop :=
  match created with
  | none => OwnersBoundedSafe w
  | some kp => OwnersFresh kp w

theorem keypairCreate_owners_spec (peer : Option PeerId) :
    ⦃fun w => ⌜OwnersBoundedSafe w⌝⦄ keypairCreate peer
      ⦃⇓? result w => ⌜allocatedOwners result w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w ambient result final after pre run
  obtain ⟨d, device, unique, bounded⟩ := pre
  have effect := keypairCreate_exact peer d w.keypairCounter
    w ambient result final after ⟨device, rfl⟩ run
  cases result with
  | none => exact ⟨d, effect.1, unique, bounded⟩
  | some kp =>
    obtain ⟨rfl, hd, hc⟩ := effect
    exact ⟨_, hd, unique, created_bounded d _ peer bounded, Nat.lt_succ_self _, bounded_fresh d bounded⟩

theorem sessionAfterAllocation_owners (pid : PeerId) (st : Nat) (kp : KeypairId) :
    ⦃fun w => ⌜OwnersFresh kp w⌝⦄ sessionAfterAllocation pid st kp
      ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  let Q : WGWorld → Prop := OwnersFresh kp
  have hpeer : Ensures (getPeer pid) Q (fun _ => Q) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid Q)
      g ambient p final after pre run).1
  have hkey : Ensures (getKeypair kp) Q (fun _ => Q) := by
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
  have hderef : Ensures (IndexOwner.peerDeref (.handshake pid)) Q (fun _ => Q) := by
    unfold IndexOwner.peerDeref IndexOwner.peerWord
    refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
    · refine ensures_bind _ _ hpeer ?_
      intro p g ambient result final after pre run
      cases run
      exact pre
    · intro word g ambient result final after pre run
      cases word with
      | none =>
        simp [unsupported, AmbientM.unsupported] at run
        cases run
      | some owner =>
        cases run
        exact pre
  have htail : Ensures (do
      handshakeZero pid
      if ← branch .sessionAlive !(← getPeer pid).isDead then
        addNewKeypair pid kp
        _ ← IndexOwner.peerDeref (.handshake pid)
        if !(← indexReplaceHandshake pid kp) then
          unsupported "begin_session: the handshake entry was unhashed"
        return true
      unsupported "a dead peer finishing a session" : WG.M Bool)
      Q (fun _ => OwnersBoundedSafe) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (handshakeZero_ownersFresh kp pid)) ?_
    intro done
    refine ensures_bind _ _ hpeer ?_
    intro current
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro alive
    cases alive with
    | false =>
      intro g ambient result final after pre run
      simp [unsupported, AmbientM.unsupported] at run
      cases run
    | true =>
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (addNewKeypair_ownersFresh pid kp)) ?_
      intro done
      refine ensures_bind _ _ hderef ?_
      intro owner
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (indexReplace_ownersFresh pid kp)) ?_
      intro replaced g ambient result final after pre run
      cases replaced with
      | false =>
        simp [unsupported, AmbientM.unsupported] at run
        cases run
      | true =>
        cases run
        exact pre
  unfold sessionAfterAllocation
  refine ensures_bind _ _ hpeer ?_
  intro p
  refine ensures_bind _ _ hkey ?_
  intro key
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (setKeypair_ownersFresh kp kp _)) ?_
  intro done
  refine ensures_bind _ _ (hbranch _ _) ?_
  intro initiator
  cases initiator <;>
    exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (deriveKeys_ownersFresh kp _ _))
      (fun _ => htail)

theorem sessionAfterCreate_owners (pid : PeerId) (st : Nat) (created : Option KeypairId) :
    ⦃fun w => ⌜allocatedOwners created w⌝⦄ sessionAfterCreate pid st created
      ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases created with
  | none =>
    simp [sessionAfterCreate, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact pre
  | some kp =>
    simp [sessionAfterCreate, branch, AmbientM.branch] at run
    exact (ensures_iff _ _ _).mpr (sessionAfterAllocation_owners pid st kp)
      g _ result final after pre run

theorem beginSession_owners_spec (pid : PeerId) :
    ⦃fun w => ⌜OwnersBoundedSafe w⌝⦄ beginSession pid ⦃⇓? _ w => ⌜OwnersBoundedSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  let Q : WGWorld → Prop := OwnersBoundedSafe
  have hpeer : Ensures (getPeer pid) Q (fun _ => Q) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid Q)
      g ambient p final after pre run).1
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) Q (fun _ => Q) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) Q)
  have hword : Ensures (IndexOwner.peerWord (.handshake pid)) Q (fun _ => Q) := by
    unfold IndexOwner.peerWord
    refine ensures_bind _ _ hpeer ?_
    intro p g ambient result final after pre run
    cases run
    exact pre
  rw [beginSession_owner_source]
  refine ensures_bind _ _ hpeer ?_
  intro p
  refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
  · unfold WG.andM
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro first
    cases first with
    | false =>
      intro g ambient result final after pre run
      cases run
      exact pre
    | true => exact hbranch _ _
  · intro inactive
    cases inactive with
    | true =>
      intro g ambient result final after pre run
      cases run
      exact pre
    | false =>
      refine ensures_bind _ _ hword ?_
      intro word
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (keypairCreate_owners_spec word)) ?_
      intro created
      exact (ensures_iff _ _ _).mpr (sessionAfterCreate_owners pid _ created)

end Leanux.Proofs.WG.Index
