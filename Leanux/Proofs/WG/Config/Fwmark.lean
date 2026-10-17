import Leanux.Proofs.WG.Config.OperationFrames
import Leanux.Proofs.WG.Config.Model
import Leanux.Proofs.WG.Config.EndpointSources
import Leanux.Proofs.WG.Config.DeviceScalars

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def fwmarkAttrs (d : Device) (mark : Nat) : DeviceAttrs :=
  { device := byIndex d, fwmark := some mark }

theorem setDevice_fwmark_frame (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun g => g.dev = some d ∧ selectsDevice g d)
      (fun ret g => ret = 0 ∧ g.dev.map withoutPeers = some
        (withoutPeers {d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1})) := by
  let updated := {d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1}
  let Q : WGWorld → Prop := fun g => g.dev.map withoutPeers = some (withoutPeers updated)
  let body := fun (pid : PeerId) (_ : Unit) => do
    _ ← branch .setDevFwmarkPeerIter true
    clearPeerEndpointSrc pid
    pure (ForInStep.yield ())
  have loop (pids : List PeerId) : Ensures (forIn pids () body) Q (fun _ => Q) := by
    induction pids with
    | nil =>
      intro g ambient result final after pre run
      cases run
      exact pre
    | cons pid rest ih =>
      simp only [List.forIn_cons, body, bind_assoc]
      refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
      · exact (ensures_iff _ _ _).mpr
          (hoare_liftAmbient_variant (AmbientM.branch .setDevFwmarkPeerIter true) Q)
      · intro _
        refine ensures_bind (Q := fun _ => Q) _ _
          ((ensures_iff _ _ _).mpr (clearEndpointSource_device_frame pid _)) ?_
        intro _
        exact ih
  let tail : WG.M Int := do
    let _ ← forIn d.peerList () body
    _ ← branch .setDevFwmarkPeerIter false
    _ ← branch .setDevPort false
    _ ← branch .setDevReplacePeers false
    _ ← branch .setDevHasPrivateKey false
    _ ← branch .setDevHasPeers false
    _ ← branch .setDevZeroKey false
    pure 0
  have contract : Ensures tail Q (fun ret g => ret = 0 ∧ Q g) := by
    unfold tail
    refine ensures_bind _ _ (loop _) ?_
    intro _ g ambient result final after pre run
    simp [branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, pre⟩
  intro g ambient result final after pre run
  obtain ⟨value, middle, next, lookupRun, lookupValue, device⟩ :=
    (returns_iff _ _ _).mpr (lookupInterface_index d) g ambient pre
  subst value
  let logged (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let before := logged (logged (logged (logged (logged (logged (logged (logged (logged next
    .setDevLookupErr false) .setDevHasFlags false) .setDevBadFlags false)
    .setDevHasPort false) .setDevHasFwmark true) .setDevNoNet false)
    .setDevNotCapable false) .setDevPermErr false) .setDevFwmark true
  have source : ((wgSetDevice (fwmarkAttrs d mark)).run g).run ambient =
      (tail.run {middle with dev := some updated}).run before := by
    rw [← wgSetDevice_source]
    simp [wgSetDeviceSource, fwmarkAttrs, WG.orM, branch, AmbientM.branch,
      WGDEVICE_F_ALL]
    rw [show ((lookupInterface (byIndex d)).run g).run ambient =
      .ok ((.ok (), middle), next) from lookupRun]
    dsimp only [bind, Except.bind]
    simp [deviceUpdateSource, deviceKeySource, devicePeersSource,
      WG.andM, branch, AmbientM.branch, getDev, device, net, modifyDev,
      WGDEVICE_F_REPLACE_PEERS, tail, body, updated, before, logged, StateT.run, StateT.bind, StateT.lift,
      StateT.pure, Except.bind, Except.pure, liftM, monadLift, pure, bind, get, modify, modifyGet, MonadLift.monadLift,
      MonadStateOf.modifyGet, getThe, StateT.modifyGet, MonadStateOf.get, StateT.get, Functor.map, StateT.map]
  exact contract _ before result final after (by simp [Q]) (source.symm.trans run)

end Leanux.Proofs.WG.Config
