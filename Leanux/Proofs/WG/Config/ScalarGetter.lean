import Leanux.Proofs.WG.Config.ScalarGetterSource
import Leanux.Proofs.WG.Config.ClaimView

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem scalar_outer_get_after_set (d : Device) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid])
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (noIps : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun w => w.wg.device = some d ∧ w.wg.nlSock7 = sock ∧ ClaimView.selectsDevice w d)
      (fun result w =>
        let updated := scalarRequestDevice d pid p psk interval
        let configured := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        result = ((if bad then -EINVAL else 0), .ok (singlePeerJson updated configured)) ∧ w.wg.device = some updated ∧
          w.wg.nlSock7 = { completedSock sock updated configured with queue := [] }) := by
  intro initial ambient h
  obtain ⟨hd, hs, selected⟩ := h
  obtain ⟨ret, afterSet, setAmbient, setRun, hret, hdev, hframe⟩ :=
    setDevice_scalars_framed d key psk interval bad pid p sock initial.fixtureNetDevices
      found resident live bounded down initial ambient ⟨hd, ⟨hs, rfl⟩, selected⟩
  let updated := scalarRequestDevice d pid p psk interval
  let configured := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
  have hg := wgGetDevice_single pid updated configured sock
    (by simpa [updated, scalarRequestDevice, scalarDevice, withPeer] using peers)
    (by simp [updated, configured, scalarRequestDevice, scalarDevice, withPeer])
    (by simpa [configured] using noIps)
    (by simpa [updated, scalarRequestDevice, scalarDevice, withPeer, devicePrefixSpace] using room)
    idle empty
  have selected' : selectsDevice afterSet updated := by
    change selectsDevice initial d at selected
    simpa [selectsDevice, updated, scalarRequestDevice, scalarDevice, withPeer, hframe.2] using selected
  obtain ⟨dump, final, finalAmbient, getRun, hresult, hfinal, hsocket⟩ :=
    hg afterSet setAmbient ⟨hdev, hframe.1, selected'⟩
  refine ⟨(ret, dump), final, finalAmbient, ?_, ?_⟩
  · change (((wgSetDevice (scalarDeviceAttrs d key psk interval bad)).run initial).run ambient >>= _) = _
    rw [setRun]
    change (((wgGetDevice (byIndex d)).run afterSet).run setAmbient >>= _) = _
    have selector : byIndex d = byIndex updated := rfl
    rw [selector, getRun]
    rfl
  · exact ⟨by simp [hret, hresult, updated, configured], hfinal, hsocket⟩

end Leanux.Proofs.WG.Config
