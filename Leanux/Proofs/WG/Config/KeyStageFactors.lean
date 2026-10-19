import Leanux.Proofs.WG.Config.KeyCollision
import Leanux.Proofs.WG.Config.RequestOrderReceiptBridge

/-! Native factors separated from observer and frame dependencies. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.KeyStage
open Leanux Leanux.WG Leanux.Proofs.WG.Configuration

theorem stage_factor (attrs : DeviceAttrs) :
    RequestOrder.keyStage attrs = (do
      if ← WG.andM (branch .setDevHasPrivateKey attrs.privateKey.isSome)
          (branch .setDevPrivateKeyLen true) then
        let some key := attrs.privateKey | invariant "unreachable"
        if !(← branch .setDevKeyUnchanged ((← getDev).staticIdentity.staticPrivate == key)) then
          keyCollisionSource key
          keyInstallSource key
      pure 0 : WG.M Int) := by
  have bind_cond {α β : Type} (c : Prop) [Decidable c]
      (a b : WG.M α) (f : α → WG.M β) :
      (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
    split <;> rfl
  have map_cond (yes : Bool) (action : WG.M Unit) :
      ((fun (_ : Unit)=>ForInStep.yield PUnit.unit) <$> (if yes then action else pure ())) =
        (if yes then (fun (_ : Unit)=>ForInStep.yield PUnit.unit) <$> action
        else pure (ForInStep.yield PUnit.unit)) := by
    cases yes <;> simp
  simp [RequestOrder.keyStage,deviceKeyWith,keyCollisionSource, keyCollisionSourceWith,keyInstallSource, keyInstallSourceWith,
    keyPeerLoopSourceWith,keyPeerSourceWith,bind_assoc,bind_cond,map_cond]
  congr 1
  funext has
  cases has <;> simp
  cases h : attrs.privateKey with
  | none => simp
  | some key =>
    simp only
    congr 1
    funext d
    congr 1
    funext unchanged
    cases unchanged <;> simp
    congr 1
    funext pair
    obtain ⟨pub,ok⟩ := pair
    congr 1
    funext generated
    cases generated <;> simp
    cases pub <;> simp [bind_assoc,bind_cond]

end Leanux.Proofs.WG.Config.KeyStage
