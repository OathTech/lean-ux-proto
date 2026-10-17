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
    Returns (generatePublic key) (fun w => w.dev = some d)
      (fun result w => result = publicResult key ∧ w.dev = some d) := by
  intro g ambient device
  let after := {ambient with steps := ambient.steps.push {decision := .genPublicNullSecret, outcome := key == nullPoint, netRx := ambient.netRxSection}}
  refine ⟨publicResult key, g, after, ?_, rfl, device⟩
  by_cases isNull : key == nullPoint
  all_goals simp [generatePublic, publicResult, branch, AmbientM.branch, isNull, after]
  all_goals rfl

theorem publicResult_valid (key : Key) (ok : (publicResult key).2 = true) :
    ∃ pub, (publicResult key).1 = some pub := by
  unfold publicResult at *
  split at * <;> simp_all

def keyCollisionSource (key : Key) : WG.M Unit := do
  let (pub, ok) ← generatePublic key
  if ← branch .setDevGenPublic ok then
    let some pub := pub | invariant "a generated public key without a write"
    let peer ← pubkeyLookup pub
    if ← branch .setDevOldPeer peer.isSome then
      peerPut peer
      peerRemove peer

def devicePrivateSource (a : DeviceAttrs) : WG.M Int := do
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
    Returns (keyCollisionSource key) (fun w => w.dev = some d)
      (fun _ w => w.dev = some d) := by
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let generated := mark ambient .genPublicNullSecret (key == nullPoint)
  let checked := mark generated .setDevGenPublic (publicResult key).2
  let after := if (publicResult key).2 then
    mark (mark (mark checked .pubkeyLookupMatch false) .peerGetMaybeZeroNull true) .setDevOldPeer false
    else checked
  refine ⟨(), g, after, ?_, device⟩
  by_cases isNull : key == nullPoint
  · simp [keyCollisionSource, generatePublic, publicResult, branch, AmbientM.branch,
      isNull, after, checked, generated, mark]
    rfl
  · cases valid : (curve25519 key basePoint).2 with
    | false =>
      simp [keyCollisionSource, generatePublic, publicResult, branch, AmbientM.branch,
        isNull, valid, after, checked, generated, mark]
      rfl
    | true =>
      have missing := absent (curve25519 key basePoint).1
        (by simp [publicResult, isNull]) (by simp [publicResult, isNull, valid])
      simp [keyCollisionSource, generatePublic, publicResult, branch, AmbientM.branch,
        isNull, valid, after, checked, generated, mark, pubkeyLookup, peerGetMaybeZero,
        getDev, device, missing]
      rfl

end Leanux.Proofs.WG.Config
