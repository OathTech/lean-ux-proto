import Leanux.Proofs.WG.Config.ReadbackFrames

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

def scalarDeviceAttrs (d : Device) (key psk : Key) (interval : Nat) (bad : Bool) : DeviceAttrs :=
  { device := byIndex d, peers := some ([.attrs (scalarAttrs key psk interval)] ++
      if bad then [.malformed] else []) }

def scalarRequestDevice (d : Device) (pid : PeerId) (p : Peer) (psk : Key) (interval : Nat) : Device :=
  scalarDevice { d with deviceUpdateGen := d.deviceUpdateGen + 1 } pid p psk interval

theorem lookupInterface_index_framed (d : Device) (sock : NlSock) (fixtures : FixtureDevices) :
    ⦃fun w => ⌜w.k.wg = some d ∧ readbackFrame w sock fixtures ∧ selectsDevice w d⌝⦄
      lookupInterface (byIndex d)
    ⦃⇓ ret w => ⌜ret = .ok () ∧ w.k.wg = some d ∧ readbackFrame w sock fixtures⌝⦄ := by
  have frame : Ensures (lookupInterface (byIndex d))
      (fun w => readbackFrame w sock fixtures) (fun _ w => readbackFrame w sock fixtures) := by
    rw [ensures_iff]
    mvcgen [lookupInterface, byIndex, netDevices, getK, branch, WG.orM, invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [readbackFrame]
  rw [← returns_iff]
  intro w h
  obtain ⟨ret, final, run, hret, hd⟩ := (returns_iff _ _ _).mpr
    (lookupInterface_index d) w ⟨h.1, h.2.2⟩
  exact ⟨ret, final, run, hret, hd, frame w ret final h.2.1 run⟩

theorem devicePeers_scalars_framed (selector d : Device) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (p : Peer) (sock : NlSock) (fixtures : FixtureDevices)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    ⦃fun w => ⌜w.k.wg = some d ∧ readbackFrame w sock fixtures⌝⦄
      devicePeersSource (scalarDeviceAttrs selector key psk interval bad)
    ⦃⇓ ret w => ⌜ret = (if bad then -EINVAL else 0) ∧ w.k.wg = some (scalarDevice d pid p psk interval) ∧
      readbackFrame w sock fixtures⌝⦄ := by
  have hp := (returns_iff _ _ _).mp
    (setPeer_scalars_down_returns_framed sock fixtures key psk interval pid d p
      found resident live bounded down)
  cases bad <;> simp [devicePeersSource, scalarDeviceAttrs, List.forIn_cons, List.forIn_nil]
  all_goals mvcgen [branch, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [readbackFrame]

theorem setDevice_scalars_framed (d : Device) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (p : Peer) (sock : NlSock) (fixtures : FixtureDevices)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Returns (wgSetDevice (scalarDeviceAttrs d key psk interval bad))
      (fun w => w.k.wg = some d ∧ readbackFrame w sock fixtures ∧ selectsDevice w d)
      (fun ret w => ret = (if bad then -EINVAL else 0) ∧ w.k.wg = some (scalarRequestDevice d pid p psk interval) ∧
        readbackFrame w sock fixtures) := by
  let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
  have hl := lookupInterface_index_framed d sock fixtures
  have hp := devicePeers_scalars_framed d updated key psk interval bad pid p sock fixtures
    found resident live bounded down
  rw [← wgSetDevice_source, returns_iff]
  simp only [wgSetDeviceSource, deviceUpdateSource, deviceKeySource,
    scalarDeviceAttrs]
  mvcgen [WG.orM, WG.andM, branch, modifyDev, modifyK, invariant, hl, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [updated, scalarRequestDevice, readbackFrame,
    WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  all_goals subst_vars
  all_goals first | exact hp _ (by simp_all [updated, readbackFrame]) | grind only

theorem scalar_outer_get_after_set (d : Device) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid])
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (noIps : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = sock ∧ selectsDevice w d)
      (fun result w =>
        let updated := scalarRequestDevice d pid p psk interval
        let configured := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        result = ((if bad then -EINVAL else 0), .ok (singlePeerJson updated configured)) ∧ w.k.wg = some updated ∧
          w.k.nlSock7 = { completedSock sock updated configured with queue := [] }) := by
  intro initial h
  obtain ⟨hd, hs, selected⟩ := h
  obtain ⟨ret, afterSet, setRun, hret, hdev, hframe⟩ :=
    setDevice_scalars_framed d key psk interval bad pid p sock initial.fixtureNetDevices
      found resident live bounded down initial ⟨hd, ⟨hs, rfl⟩, selected⟩
  let updated := scalarRequestDevice d pid p psk interval
  let configured := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
  have hg := wgGetDevice_single pid updated configured sock
    (by simpa [updated, scalarRequestDevice, scalarDevice, withPeer] using peers)
    (by simp [updated, configured, scalarRequestDevice, scalarDevice, withPeer])
    (by simpa [configured] using noIps)
    (by simpa [updated, scalarRequestDevice, scalarDevice, withPeer, devicePrefixSpace] using room)
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
