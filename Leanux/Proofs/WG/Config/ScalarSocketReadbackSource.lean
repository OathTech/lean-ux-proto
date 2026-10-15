import Leanux.Proofs.WG.Config.ScalarGetter
import Leanux.Proofs.WG.Config.SocketReadbackClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Compose the original scalar setter and actual two-chunk socket getter.
The existing setter frame carries the original socket and selector fixtures
through both successful and partially failing configuration requests. -/
theorem scalarSocketReadback_source (d : Device) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) (tail : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid])
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (listed : p.allowedipsList = front ++ b :: tail) (nonempty : front ≠ [])
    (absent : b ∉ front) (readable : Ipv4Residents d nodes (front ++ b :: tail))
    (endpoint : p.endpoint = none)
    (firstFits : devicePrefixSpace d + 140 + 28 * front.length ≤ NLMSG_GOODSIZE)
    (firstFull : NLMSG_GOODSIZE < devicePrefixSpace d + 140 + 28 * (front.length + 1))
    (lastFits : devicePrefixSpace d + 44 + 28 * (b :: tail).length + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = sock ∧ selectsDevice w d)
      (fun result w =>
        let updated := scalarRequestDevice d pid p psk interval
        let configured := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        result = ((if bad then -EINVAL else 0),
          .ok (suffixJson updated configured nodes (front ++ b :: tail))) ∧
        w.k.wg = some updated ∧ w.k.nlSock7 = socketReadbackFinal sock updated) := by
  intro initial h
  obtain ⟨hd, hs, selected⟩ := h
  obtain ⟨ret, afterSet, setRun, hret, hdev, hframe⟩ :=
    setDevice_scalars_framed d key psk interval bad pid p sock initial.fixtureNetDevices
      found resident live bounded down initial ⟨hd, ⟨hs, rfl⟩, selected⟩
  let updated := scalarRequestDevice d pid p psk interval
  let configured := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
  have hg := socketReadback_returns pid updated configured nodes front b tail sock
    (by simpa [updated, scalarRequestDevice, scalarDevice, withPeer] using peers)
    (by simp [updated, configured, scalarRequestDevice, scalarDevice, withPeer])
    (by simpa [configured] using listed) nonempty absent
    (by simpa [Ipv4Residents, updated, scalarRequestDevice, scalarDevice, withPeer] using readable)
    (by simpa [configured] using endpoint)
    (by simpa [updated, scalarRequestDevice, scalarDevice, withPeer, devicePrefixSpace] using firstFits)
    (by simpa [updated, scalarRequestDevice, scalarDevice, withPeer, devicePrefixSpace] using firstFull)
    (by simpa [updated, scalarRequestDevice, scalarDevice, withPeer, devicePrefixSpace] using lastFits)
    idle empty
  have selected' : selectsDevice afterSet updated := by
    simpa [selectsDevice, updated, scalarRequestDevice, scalarDevice, withPeer, hframe.2] using selected
  obtain ⟨dump, final, getRun, hresult, hfinal, hsocket⟩ :=
    hg afterSet ⟨hdev, hframe.1, selected'⟩
  refine ⟨(ret, dump), final, ?_, ?_⟩
  · change (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump)).run initial = .ok ((ret, dump), final)
    rw [StateT.run_bind, setRun]
    change (do let dump ← wgGetDevice (byIndex d); pure (ret, dump)).run afterSet = _
    have selector : byIndex d = byIndex updated := rfl
    rw [selector, StateT.run_bind, getRun]
    rfl
  · exact ⟨by simp [hret, hresult, updated, configured], hfinal, hsocket⟩

end Leanux.Proofs.WG.Config
