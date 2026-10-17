import Leanux.Proofs.WG.Config.KeyReadbackFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

/-- The one actual peer-list step gives the exact rotation effect. Its expiry
clock is derived from the checked execution relation, with no supplied clock. -/
theorem setDevice_rotation_exact (d : Device) (key : Key) (pid : PeerId) (p : Peer)
    (sock : NlSock) (fixtures : FixtureDevices)
    (established : d.staticIdentity.hasIdentity = true)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key)
    (members : d.peerList = [pid]) (resident : d.peers[pid]? = some p) :
    Ensures (wgSetDevice (privateKeyAttrs d key))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures ∧ selectsDevice g d)
      (fun ret g => ret = 0 ∧ readbackFrame g sock fixtures ∧
        ∃ now, g.dev = some (keyReadbackDevice d key pid p now)) := by
  intro g ambient value final after pre run
  have framed := setDevice_rotation_readbackFrame d key sock fixtures established changed absent
    g ambient value final after pre run
  obtain ⟨code, done, observations, device, effect⟩ := setDevice_private_changed_no_collision d key changed absent
    g ambient value final after ⟨pre.1, pre.2.2⟩ run
  change final.dev = some done at device
  have quiet : requestsStagedSend d key = false := by simp [requestsStagedSend, established]
  rw [quiet, members] at effect
  refine ⟨code, framed, ?_⟩
  cases effect with
  | cons _ _ old observation step next _ _ _ found effect stepDevice tail =>
    cases tail
    have oldEq : old = p := by simpa [installedDevice, requestGeneration, cookieKeysAfter, resident] using found.symm
    subst old
    obtain ⟨now, effect⟩ := effect
    simp only [Bool.false_eq_true, ↓reduceIte] at effect
    have same : done = peerUpdatedDevice (installedDevice (requestGeneration d) key) pid p now :=
      Option.some.inj (stepDevice.symm.trans effect.2)
    refine ⟨now, ?_⟩
    change final.dev = some (peerUpdatedDevice (installedDevice (requestGeneration d) key) pid p now)
    rw [← same]
    exact device

end Leanux.Proofs.WG.Config
