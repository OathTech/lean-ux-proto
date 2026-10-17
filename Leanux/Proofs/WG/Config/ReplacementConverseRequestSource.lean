import Leanux.Proofs.WG.Config.RequestModel
import Leanux.Proofs.WG.Config.ReplacementConverseSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem setDevice_replace_effect_pairs (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Ensures (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.dev = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ ∃ removed,
        RemovalEffect (withPeer (requestGeneration d) pid { p with refcount := p.refcount + 1 })
          p.allowedipsList removed ∧
        w.dev = some (generalReplacementDevice removed pid p)) := by
  let updated := requestGeneration d
  let P : Int → WGWorld → Prop := fun ret g => ret = 0 ∧ ∃ removed,
    RemovalEffect (withPeer updated pid {p with refcount := p.refcount + 1}) p.allowedipsList removed ∧
    g.dev = some (generalReplacementDevice removed pid p)
  let mark (site : Decision) (value : Bool) : WG.M Unit :=
    monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
      decision := site, outcome := value, netRx := a.netRxSection}} : AmbientM Unit)
  have branchSource (site : Decision) (value : Bool) :
      (branch site value : WG.M Bool) = (do mark site value; pure value) := rfl
  have hm (site : Decision) (value : Bool) (entry : Device) :
      Ensures (mark site value) (fun g => g.dev = some entry)
        (fun _ g => g.dev = some entry) := by
    intro g ambient result final after device run
    cases run
    exact device
  have peers : Ensures (devicePeersSource (replaceAllowedipsDeviceAttrs d key))
      (fun g => g.dev = some updated) P := by
    let finish : Int → WG.M Int := fun ret => do
      if ← branch .setDevSetPeerErr (ret < 0) then
        _ ← branch .setDevZeroKey false
        return ret
      _ ← branch .setDevPeersIter false
      _ ← branch .setDevZeroKey false
      pure 0
    have suffix (ret : Int) : Ensures (finish ret) (P ret) P := by
      intro g ambient result final after pre run
      obtain ⟨zero, effect⟩ := pre
      subst ret
      simp [finish, branch, AmbientM.branch] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, effect⟩
    have body : Ensures (do
        mark .setDevHasPeers true
        mark .setDevPeersIter true
        mark .setDevParseErr false
        let ret ← setPeerCmd (replaceAllowedipsAttrs key)
        finish ret)
        (fun g => g.dev = some updated) P := by
      refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
      refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
      refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
      exact ensures_bind _ _ (setPeer_replace_effect_pairs key pid updated p
        found resident pairs live bounded down) suffix
    have source : devicePeersSource (replaceAllowedipsDeviceAttrs d key) = (do
        mark .setDevHasPeers true
        mark .setDevPeersIter true
        mark .setDevParseErr false
        let ret ← setPeerCmd (replaceAllowedipsAttrs key)
        finish ret) := by
      simp [devicePeersSource, replaceAllowedipsDeviceAttrs, List.forIn_cons,
        List.forIn_nil, branchSource, finish, bind_assoc]
      congr 1
      funext _
      congr 1
      funext _
      congr 1
      funext _
      congr 1
      funext ret
      congr 1
      funext _
      by_cases failed : ret < 0 <;>
        simp [failed, map_eq_pure_bind, bind_assoc, -bind_pure_comp]
    rw [source]
    exact body
  have hu : Ensures (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1})
      (fun g => g.dev = some d) (fun _ g => g.dev = some updated) := by
    intro g ambient result final after device run
    cases run
    simp [device, updated, requestGeneration]
  have tail : Ensures (do
      mark .setDevLookupErr false
      mark .setDevHasFlags false
      mark .setDevBadFlags false
      mark .setDevHasPort false
      mark .setDevHasFwmark false
      modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}
      mark .setDevFwmark false
      mark .setDevPort false
      mark .setDevReplacePeers false
      mark .setDevHasPrivateKey false
      devicePeersSource (replaceAllowedipsDeviceAttrs d key))
      (fun g => g.dev = some d) P := by
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ hu (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    exact peers
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource
  refine ensures_bind _ _ (removal_returns_ensures_native
    ((returns_iff _ _ _).mpr (lookupInterface_index d))) ?_
  intro ret g ambient result final after pre run
  obtain ⟨rfl, device⟩ := pre
  apply tail g ambient result final after device
  simpa [replaceAllowedipsDeviceAttrs, deviceUpdateSource, deviceKeySource, WG.orM, WG.andM,
    branchSource, bind_assoc, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS] using run

end Leanux.Proofs.WG.Config
