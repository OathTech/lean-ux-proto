import Leanux.WG.Timers
import Leanux.Proofs.Framing.Projection
import Leanux.Proofs.Framing.Lift
import Leanux.Proofs.WG.Peers.Primitives

/-! The zero-key timer's immediate action is a queue operation, not a
clearance of transport keys. This contract concerns the callback only. -/
namespace Leanux.Proofs.WG.KeyTimes
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

def keypairStore (w : WGWorld) : Option (Std.TreeMap KeypairId Keypair) :=
  w.dev.map (·.keypairs)

theorem expiredZeroKeyMaterial_store (pid : PeerId) :
    SameView keypairStore (expiredZeroKeyMaterial pid) := by
  apply SameView.of_wp
  intro before
  have ambientSpec {α : Type} (a : AmbientM α) :
      ⦃fun w => ⌜keypairStore w = before⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ w => ⌜keypairStore w = before⌝⦄ :=
    hoare_liftAmbient a _
  have indexSpec {α : Type} (a : IndexM α) :
      ⦃fun w => ⌜keypairStore w = before⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ w => ⌜keypairStore w = before⌝⦄ := by
    apply hoare_liftIndex a _
    intro g d table hp hd
    simpa [keypairStore, hd] using hp
  have countInc (old : Nat) :
      ⦃fun w => ⌜keypairStore w = before⌝⦄ (refcountInc old : WG.M Unit)
      ⦃⇓? _ w => ⌜keypairStore w = before⌝⦄ := by
    mvcgen [-Std.Do.Spec.monadLift_StateT, refcountInc, branch, branchCmp,
      unsupported, ambientSpec]
  have countDec (old : Nat) :
      ⦃fun w => ⌜keypairStore w = before⌝⦄ (refcountDecAndTest old : WG.M Bool)
      ⦃⇓? _ w => ⌜keypairStore w = before⌝⦄ := by
    mvcgen [-Std.Do.Spec.monadLift_StateT, refcountDecAndTest, branch, branchCmp,
      unsupported, ambientSpec]
  have getDevSpec :
      ⦃fun w => ⌜keypairStore w = before⌝⦄ getDev
      ⦃⇓? _ w => ⌜keypairStore w = before⌝⦄ := by
    mvcgen [-Std.Do.Spec.monadLift_StateT, getDev, invariant, ambientSpec]
  have getPeerSpec (i : PeerId) :
      ⦃fun w => ⌜keypairStore w = before⌝⦄ getPeer i
      ⦃⇓? _ w => ⌜keypairStore w = before⌝⦄ := by
    mvcgen [-Std.Do.Spec.monadLift_StateT, getPeer, getDevSpec, invariant, ambientSpec]
  have modifySpec (f : Device → Device) (hf : ∀ d, (f d).keypairs = d.keypairs) :
      ⦃fun w => ⌜keypairStore w = before⌝⦄ modifyDev f
      ⦃⇓? _ w => ⌜keypairStore w = before⌝⦄ := by
    apply hoare_modify
    intro g hg
    simpa [keypairStore, Option.map_map, Function.comp_def, hf] using hg
  have setPeerSpec (i : PeerId) (p : Peer) :
      ⦃fun w => ⌜keypairStore w = before⌝⦄ setPeer i p
      ⦃⇓? _ w => ⌜keypairStore w = before⌝⦄ := modifySpec _ (fun _ => rfl)
  have peerGetSpec (i : PeerId) :
      ⦃fun w => ⌜keypairStore w = before⌝⦄ peerGet i
      ⦃⇓? _ w => ⌜keypairStore w = before⌝⦄ := by
    mvcgen [-Std.Do.Spec.monadLift_StateT, peerGet, requireNotPending,
      getPeerSpec, setPeerSpec, countInc]
  have peerPutSpec (i : Option PeerId) :
      ⦃fun w => ⌜keypairStore w = before⌝⦄ peerPut i
      ⦃⇓? _ w => ⌜keypairStore w = before⌝⦄ := by
    mvcgen [-Std.Do.Spec.monadLift_StateT, peerPut, requireNotPending,
      getPeerSpec, setPeerSpec, modifySpec, retirePeerUnits, branch, invariant,
      unsupported, ambientSpec, indexSpec, countDec]
    all_goals simp
  mvcgen [-Std.Do.Spec.monadLift_StateT, expiredZeroKeyMaterial,
    peerPutSpec, peerGetSpec, getPeerSpec, getDevSpec, modifySpec,
    recordQueued, peekQueuedUnit, branch, invariant, unsupported,
    ambientSpec]
  all_goals simp

end Leanux.Proofs.WG.KeyTimes
