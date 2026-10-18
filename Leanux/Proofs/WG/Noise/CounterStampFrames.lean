import Leanux.Proofs.WG.Packets.PublicationRunner
import Leanux.Proofs.WG.Queues.CurrentSlotCompletion
import Leanux.Proofs.WG.Noise.ConfirmationSequenceEffects
import Leanux.Proofs.WG.Noise.RotationSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ConsumeConfirmation
open Std.Do
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues MaterialOrigin

def keyStampAt (w : WGWorld) (id : KeypairId) : Option Nat :=
  ((w.dev.bind fun d => d.keypairs[id]?)).map Keypair.internalId

theorem counter_stamped (id nonce : Nat) (initial : Option Nat) :
    Hoare (counterValidate id nonce) (fun w => keyStampAt w id = initial)
      (fun _ w => ∃ stamp, initial = some stamp ∧ keyStampAt w id = some stamp) := by
  have getter : Hoare (getKeypair id) (fun w => keyStampAt w id = initial)
      (fun k g => initial = some k.internalId ∧ keyStampAt g id = some k.internalId) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient k v ambient' hi hr
    obtain ⟨hv,_,d,hd,hk⟩ := KeyTimes.getKeypair_return id w v k ambient ambient' hr
    subst v
    have key : keyStampAt w id = some k.internalId := by simp [keyStampAt,hd,hk]
    exact ⟨hi.symm.trans key,key⟩
  unfold counterValidate
  apply hoare_bind _ _ getter
  intro k
  let Q := fun g => initial = some k.internalId ∧ keyStampAt g id = some k.internalId
  have setter (counter : ReplayCounter) :
      Preserves Q (setKeypair id {k with receivingCounter := counter}) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' hi hr
    cases hd : w.dev with
    | none => simp [Q,keyStampAt,hd] at hi
    | some d =>
      cases hr
      exact ⟨hi.1,by simp [keyStampAt,hd]⟩
  apply hoare_consequence (P := Q) (Q := fun _ => Q) ?_
    (fun _ h => h) (fun _ _ h => ⟨k.internalId,h⟩)
  simp (config := {zeta := false}) only [WG.orM,Std.Legacy.Range.forIn_eq_forIn_range']
  material_lower
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head setKeypair; exact setter _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (index_material_head ForIn.forIn; apply list_view_spec _root_.id Q)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match


/-- The endpoint setter cannot change the optional allocation stamp. -/
theorem endpoint_stamp (pid : PeerId) (ep : Endpoint) (id : KeypairId) :
    SameView (fun w => keyStampAt w id) (setPeerEndpoint pid ep) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  have h := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (Keypairs.WGFrames.setPeerEndpoint_sameSnapshot pid ep) w ambient result v ambient' hr
  have slot := congrArg (fun x : Keypairs.Snapshot => (x.slots id).map Keypairs.Cell.stamp) h
  simpa only [keyStampAt,Keypairs.snapshot,Keypairs.cell,Option.map_map,Function.comp_def] using slot


end Leanux.Proofs.WG.Noise.ConsumeConfirmation
