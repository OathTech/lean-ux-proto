import Leanux.Proofs.WG.Config.KeyInstallEffects

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def publicResult (key : Key) : Option Key × Bool :=
  if key == nullPoint then (none, false)
  else (some (curve25519 key basePoint).1, (curve25519 key basePoint).2)

theorem generatePublic_return (key : Key) (d : Device) :
    Returns (generatePublic key) (fun w => w.k.wg = some d)
      (fun result w => result = publicResult key ∧ w.k.wg = some d) := by
  rw [returns_iff]
  mvcgen [generatePublic, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [publicResult]

theorem publicResult_valid (key : Key) (ok : (publicResult key).2 = true) :
    ∃ pub, (publicResult key).1 = some pub := by
  unfold publicResult at *
  split at * <;> simp_all

def keyCollisionSource (key : Key) : M Unit := do
  let (pub, ok) ← generatePublic key
  if ← branch .setDevGenPublic ok then
    let some pub := pub | invariant "a generated public key without a write"
    let peer ← pubkeyLookup pub
    if ← branch .setDevOldPeer peer.isSome then
      peerPut peer
      peerRemove peer

def devicePrivateSource (a : DeviceAttrs) : M Int := do
  if ← WG.andM (branch .setDevHasPrivateKey a.privateKey.isSome) (branch .setDevPrivateKeyLen true) then
    let some key := a.privateKey | invariant "unreachable"
    if !(← branch .setDevKeyUnchanged ((← getDev).staticIdentity.staticPrivate == key)) then
      keyCollisionSource key
      keyInstallSource key
  devicePeersSource a

theorem devicePrivate_source (a : DeviceAttrs) : devicePrivateSource a = deviceKeySource a := by
  rw [← deviceKey_loop_factor]
  simp only [devicePrivateSource, deviceKeyFactoredSource, keyCollisionSource, bind_assoc]
  congr 1
  funext hasKey
  cases hasKey <;> simp
  cases hk : a.privateKey with
  | none => simp
  | some key =>
    simp only
    congr 1
    funext dev
    congr 1
    funext unchanged
    cases unchanged <;> simp
    congr 1
    funext result
    obtain ⟨pub, ok⟩ := result
    congr 1
    funext generated
    cases generated <;> simp
    cases pub with
    | none => simp
    | some pub =>
      simp only [bind_assoc]
      congr 1
      funext peer
      congr 1
      funext present
      cases present <;> simp [bind_assoc]

def noKeyCollision (d : Device) (key : Key) : Prop :=
  ∀ pub, (publicResult key).1 = some pub → (publicResult key).2 = true →
    d.peerHashtable.find? (·.1 == pub) = none

theorem keyCollision_absent (d : Device) (key : Key) (absent : noKeyCollision d key) :
    Returns (keyCollisionSource key) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some d) := by
  have hg := (returns_iff _ _ _).mp (generatePublic_return key d)
  have hl (pub : Key) :
      ⦃fun w => ⌜w.k.wg = some d ∧ d.peerHashtable.find? (·.1 == pub) = none⌝⦄ pubkeyLookup pub
      ⦃⇓ ret w => ⌜ret = none ∧ w.k.wg = some d⌝⦄ := by
    mvcgen [pubkeyLookup, peerGetMaybeZero, getDev, getK, branch, invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [-List.find?_eq_none]
  rw [returns_iff]
  mvcgen [keyCollisionSource, branch, invariant, hg, hl]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [noKeyCollision]
  all_goals grind only [publicResult_valid]

end Leanux.Proofs.WG.Config
