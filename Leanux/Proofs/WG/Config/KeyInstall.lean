import Leanux.Proofs.WG.Config.KeyPeerLoop

set_option pp.structureInstances false

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
    Ensures (keyInstallSource key) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧
        KeyPeerUpdates (installedDevice d key) d.peerList final) := by
  intro g ambient result final after device run
  let mark (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let first := mark ambient .setDevSendStagedNoIdentity (!d.staticIdentity.hasIdentity)
  let before := if !d.staticIdentity.hasIdentity then mark first .setDevSendStagedRunning d.running else first
  let requested := !d.staticIdentity.hasIdentity && d.running
  obtain ⟨u, identityState, identityAmbient, identityRun, identityDevice⟩ :=
    setStaticIdentity_returns key d g before device
  cases u
  let kept := mark identityAmbient .setDevSendStagedKept requested
  let middle := if requested then mark kept .setDevSendStagedHasIdentity
    (identityAfter key d.staticIdentity).hasIdentity else kept
  obtain ⟨u, cookieState, cookieAmbient, cookieRun, cookieDevice⟩ :=
    cookiePrecompute_returns {d with staticIdentity := identityAfter key d.staticIdentity}
      identityState middle identityDevice
  cases u
  have source : ((keyInstallSource key).run g).run ambient =
      (((keyPeerLoopSource d.peerList false).run cookieState).run cookieAmbient >>= fun ((_, current), tail) =>
        .ok (((), current), mark tail .setDevKeyPeerIter false)) := by
    cases old : d.staticIdentity.hasIdentity <;> cases running : d.running <;>
      cases new : (identityAfter key d.staticIdentity).hasIdentity
    all_goals simp [requestsStagedSend, old, running, new] at quiet
    all_goals simp [before, first, requested, middle, kept, mark, old, running, new] at identityRun cookieRun
    all_goals simp [keyInstallSource, keyInstallSourceWith, WG.andM, getDev, device, branch, AmbientM.branch, old, running]
    all_goals rw [identityRun]
    all_goals dsimp only [bind, Except.bind]
    all_goals simp [identityDevice, new, pure, StateT.pure, StateT.run, Except.pure]
    all_goals dsimp only [StateT.run] at cookieRun
    all_goals rw [cookieRun]
    all_goals dsimp only [bind, Except.bind]
    all_goals simp [cookieDevice, cookieKeysAfter, pure, StateT.pure, Except.pure]
    all_goals rfl
  rw [source] at run
  cases loopRun : ((keyPeerLoopSource d.peerList false).run cookieState).run cookieAmbient with
  | error error => rw [loopRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨u, current⟩, tail⟩ := pair
    rw [loopRun] at run
    cases run
    exact keyPeerLoop_quiet d.peerList (installedDevice d key)
      cookieState cookieAmbient u final tail cookieDevice loopRun

end Leanux.Proofs.WG.Config
