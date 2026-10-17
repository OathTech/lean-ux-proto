import Leanux.Proofs.WG.Config.MultiPeerScalarEffects
import Leanux.Proofs.WG.Config.MultiPeerGetterClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Actual scalar setter followed by the actual fitting multi-peer getter.
The request may fail on its malformed second peer after applying its first
peer's fields. The whole finite peer list is dumped, retaining duplicate visits
and arbitrary endpoints without any new callback or lifecycle premise. -/
theorem scalar_fitting_peers_get_after_set (d : Device) (peers : PeerId → Peer)
    (key psk : Key) (interval : Nat) (bad : Bool) (pid : PeerId) (sock : NlSock)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount + 1 < 2 ^ 31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (emptyIps : ∀ q ∈ d.peerList, (peers q).allowedipsList = [])
    (room : devicePrefixSpace d + 168 * d.peerList.length + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    Campaign2.Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        let updated := scalarRequestDevice d pid (peers pid) psk interval
        result = ((if bad then -EINVAL else 0),.ok
          (multiPeerJson updated (scalarPeerView peers pid psk interval))) ∧
        s.wg.device = some updated ∧ s.wg.nlSock7 = socketReadbackFinal sock updated) := by
  intro initial ambient pre
  obtain ⟨device,socket,selected⟩ := pre
  obtain ⟨ret,afterSet,setAmbient,setRun,retEq,setDevice,framed⟩ :=
    setDevice_scalars_framed d key psk interval bad pid (peers pid) sock initial.fixtureNetDevices
      found resident live bounded down initial ambient ⟨device,⟨socket,rfl⟩,selected⟩
  let updated := scalarRequestDevice d pid (peers pid) psk interval
  let configured := scalarPeerView peers pid psk interval
  obtain ⟨sameList,sameName,sameIndex,sameSpace,currentResidents,currentEmpty⟩ :=
    scalarRequestDevice_dump_effect d peers pid psk interval residents emptyIps
  have currentRoom : devicePrefixSpace updated + 168 * updated.peerList.length + 20 ≤ NLMSG_GOODSIZE := by
    change devicePrefixSpace (scalarRequestDevice d pid (peers pid) psk interval) +
      168 * (scalarRequestDevice d pid (peers pid) psk interval).peerList.length + 20 ≤ NLMSG_GOODSIZE
    rw [sameList,sameSpace]
    exact room
  have selection : selectsDevice afterSet updated := by
    change selectsDevice initial d at selected
    simpa only [selectsDevice,updated,sameName,sameIndex,framed.2] using selected
  obtain ⟨dump,final,after,getRun,dumpEq,finalDevice,finalSocket⟩ :=
    fitting_peers_getter_returns updated configured sock currentResidents currentEmpty currentRoom
      idle emptyQueue afterSet setAmbient ⟨setDevice,framed.1,selection⟩
  refine ⟨(ret,dump),final,after,?_,?_,finalDevice,finalSocket⟩
  · change (((wgSetDevice (scalarDeviceAttrs d key psk interval bad)).run initial).run ambient >>= _) = _
    rw [setRun]
    change (((wgGetDevice (byIndex d)).run afterSet).run setAmbient >>= _) = _
    have selector : byIndex d = byIndex updated := by
      simp only [byIndex,updated,sameIndex]
    rw [selector,getRun]
    rfl
  · simp [retEq,dumpEq,updated,configured]

end Leanux.Proofs.WG.Config
