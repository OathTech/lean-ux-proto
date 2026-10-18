import Leanux.Proofs.WG.HandshakeSecurity.ResponderJointHistory

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins Origins.Retaining

theorem peerMaybe_core (word : Option PeerId) : SameView pool (peerGetMaybeZero word) := by
  apply pool_of_material
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp (PeerBorrow.acquire_spec word (wgStoreView w))
    w a result v b rfl run
  exact (pinned_const _private.Leanux.Proofs.WG.Origins.IndexMaterial.«0».Leanux.Proofs.WG.Origins.borrowed_view) borrowed.2

theorem ownerSet_core (owner : IndexOwner) (word : Option PeerId) :
    SameView pool (owner.setPeerWord word) := by
  cases owner with
  | handshake pid =>
    apply pool_of_material
    exact (getPeer_material pid).bind (fun p => Origins.setPeer_view pid {p with handshakeEntryPeer := word})
  | keypair kid =>
    intro initial
    unfold IndexOwner.setPeerWord
    have changeOnly : Preserves (fun w => pool w = initial) (do
        let k ← getKeypair kid
        setKeypair kid {k with peer := word}
        pure ()) := by
      apply coreUpdateThen (fun p => p = initial) kid
      · intro k; rfl
      · intro k; exact preserves_pure _
    simpa only [Preserves, bind_pure_unit] using changeOnly

theorem acquireOwner_core (owner : IndexOwner) : SameView pool (Affiliation.acquireOwner owner) := by
  unfold Affiliation.acquireOwner
  exact (pool_of_material (ownerWord_material owner)).bind (fun word =>
    (peerMaybe_core word).bind (fun result => (ownerSet_core owner result).bind (fun _ => SameView.pure _ _)))

theorem indexLookup_core (kinds : List IndexKind) (index : Nat) : SameView pool (indexLookup kinds index) := by
  intro initial
  let P := fun p : Pool => p = initial
  have hb (decision : Decision) (value : Bool) :
      Hoare (branch decision value : WG.M Bool) (fun w => P (pool w)) (fun _ w => P (pool w)) :=
    hoare_liftAmbient (AmbientM.branch decision value) _
  have stop {α : Type} (message : String) :
      Hoare (invariant message : WG.M α) (fun w => P (pool w)) (fun _ w => P (pool w)) :=
    hoare_liftAmbient (AmbientM.invariant message) _
  have hi : Hoare (liftIndex (indexBucket index))
      (fun w => P (pool w)) (fun _ w => P (pool w)) := by
    apply hoare_liftIndex
    intro w d table entry device
    change P (fun kid => (d.keypairs[kid]?).map keyCore)
    change P (fun kid => (w.dev.bind fun d => d.keypairs[kid]?).map keyCore) at entry
    rw [device] at entry
    exact entry
  change Hoare _ (fun w => P (pool w)) (fun _ w => P (pool w))
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  repeat' first
    | (index_material_head branch; exact hb _ _)
    | (index_material_head invariant; exact stop _)
    | (index_material_head liftIndex; exact hi)
    | (index_material_head Affiliation.acquireOwner; exact (acquireOwner_core _).wp P)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply hoare_bind (Q := fun _ w => P (pool w)))
    | (index_material_head ForIn.forIn; apply list_view_spec pool P)
    | material_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

theorem indexLookup_native (kinds : List IndexKind) (index : Nat) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (indexLookup kinds index) := by
  apply native_retained _ (RxCredits.indexLookup_keyEffect kinds index)
    (CurrentSlots.indexLookup_preserves kinds index) confirmed
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  rw [(ProjectedAction.iff_run_ambient _ _ _).mp (indexLookup_core kinds index) w a result v b run]
  exact Retains.refl _

end Leanux.Proofs.WG.HandshakeSecurity.Responder
