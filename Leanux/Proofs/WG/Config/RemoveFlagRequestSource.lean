import Leanux.Proofs.WG.Config.RemoveFlagSource
import Leanux.Proofs.WG.Config.RequestModel
import Leanux.Proofs.WG.Config.DeviceScalars
import Leanux.Proofs.WG.Config.ClaimView

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- One peer command, selected by device index, without other device updates. -/
def singlePeerAttrs (d : Device) (a : PeerAttrs) : DeviceAttrs :=
  { device := byIndex d, peers := some [.attrs a] }

theorem setDevice_remove_flag (a : PeerAttrs) (key : Key) (flags : UInt32)
    (pid : PeerId) (d : Device) (p : Peer)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31)
    (count : 0 < d.numPeers) (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Campaign2.Ensures (wgSetDevice (singlePeerAttrs d a))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ ∃ final, w.wg.device = some final ∧
        RemoveFlagEffect pid (requestGeneration d) p final) := by
  let updated := requestGeneration d
  let P : Int → WGWorld → Prop := fun ret g => ret = 0 ∧ ∃ final,
    g.dev = some final ∧ RemoveFlagEffect pid updated p final
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
  have peers : Ensures (devicePeersSource (singlePeerAttrs d a))
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
        let ret ← setPeerCmd a
        finish ret)
        (fun g => g.dev = some updated) P := by
      refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
      refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
      refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
      exact ensures_bind _ _ (setPeer_remove_flag a key flags pid updated p pubkey flagattr valid protocol
        remove found resident pairs live bounded count send clear) suffix
    have source : devicePeersSource (singlePeerAttrs d a) = (do
        mark .setDevHasPeers true
        mark .setDevPeersIter true
        mark .setDevParseErr false
        let ret ← setPeerCmd a
        finish ret) := by
      simp [devicePeersSource, singlePeerAttrs, List.forIn_cons,
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
      devicePeersSource (singlePeerAttrs d a))
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
  change Ensures _ (fun g => g.dev = some d ∧ selectsDevice g d) P
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource
  refine ensures_bind _ _ (removal_returns_ensures_native
    ((returns_iff _ _ _).mpr (lookupInterface_index d))) ?_
  intro ret g ambient result final after pre run
  obtain ⟨rfl, device⟩ := pre
  apply tail g ambient result final after device
  simpa [singlePeerAttrs, deviceUpdateSource, deviceKeySource, WG.orM, WG.andM,
    branchSource, bind_assoc, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS] using run


end Leanux.Proofs.WG.Config
