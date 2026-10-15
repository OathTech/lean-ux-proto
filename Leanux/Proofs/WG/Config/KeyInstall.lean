import Leanux.Proofs.WG.Config.KeyPeerLoop

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def installedDevice (d : Device) (key : Key) : Device :=
  cookieKeysAfter { d with staticIdentity := identityAfter key d.staticIdentity }

def requestsStagedSend (d : Device) (key : Key) : Bool :=
  (!d.staticIdentity.hasIdentity && d.running) && (identityAfter key d.staticIdentity).hasIdentity

/-- The baseline is the device after optional self-peer removal, and before
identity installation. Later peer attributes are outside this block. -/
theorem keyInstall_quiet (d : Device) (key : Key)
    (quiet : requestsStagedSend d key = false) :
    Ensures (keyInstallSource key) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        KeyPeerUpdates (installedDevice d key) d.peerList final) := by
  have hi := (returns_iff _ _ _).mp (setStaticIdentity_returns key d)
  have hc := (returns_iff _ _ _).mp
    (cookiePrecompute_returns { d with staticIdentity := identityAfter key d.staticIdentity })
  have hl := (ensures_iff _ _ _).mp (keyPeerLoop_quiet d.peerList (installedDevice d key))
  rw [ensures_iff]
  simp [keyInstallSource, WG.andM, branch, bind_assoc]
  mvcgen [getDev, getK, invariant, hi, hc, hl]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [requestsStagedSend, installedDevice, cookieKeysAfter]
  all_goals exact hl _ (by assumption)

end Leanux.Proofs.WG.Config
