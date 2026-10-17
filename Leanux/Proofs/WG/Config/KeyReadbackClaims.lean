import Leanux.Proofs.WG.Config.KeyReadbackSource
import Leanux.Proofs.WG.Config.Getter

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

/-- Full setter/getter on the actual established-identity, no-collision path.
The supplied key is read back through effective identityAfter/clamping and the
model's JSON convention; a null key removes the serialized identity fields.
No missing-clock, NULL-owner or missing-keypair failure is assumed away. -/
theorem rotation_get_after_set (d : Device) (key : Key) (pid : PeerId) (p : Peer) (sock : NlSock)
    (established : d.staticIdentity.hasIdentity = true)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key)
    (members : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (noIps : p.allowedipsList = [])
    (room : devicePrefixSpace (keyReadbackBase d key) + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (privateKeyAttrs d key)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = (0, .ok (singlePeerJson (keyReadbackBase d key) p)) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        ∃ now, s.wg.device = some (keyReadbackDevice d key pid p now)) := by
  intro entry ambient result final after pre run
  change (((wgSetDevice (privateKeyAttrs d key)).run entry).run ambient >>= fun ((ret, middle), next) =>
    ((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump, out), rest) =>
      Except.ok (((ret, dump), out), rest)) = _ at run
  cases setRun : ((wgSetDevice (privateKeyAttrs d key)).run entry).run ambient with
  | error stop => rw [setRun] at run; cases run
  | ok out =>
    obtain ⟨⟨ret, middle⟩, next⟩ := out
    obtain ⟨code, framed, now, device⟩ := setDevice_rotation_exact d key pid p sock
      entry.fixtureNetDevices established changed absent members resident
      entry ambient ret middle next ⟨pre.1, ⟨pre.2.1, rfl⟩, pre.2.2⟩ setRun
    let current := keyReadbackDevice d key pid p now
    let peer := updatedPeer (keyReadbackBase d key) p now
    have fields := keyReadbackDevice_otherFields d key pid p now
    have currentMembers : current.peerList = [pid] := by
      have h := congrArg Device.peerList fields
      exact h.trans members
    have prefixSpace : devicePrefixSpace current = devicePrefixSpace (keyReadbackBase d key) := by
      have h := congrArg devicePrefixSpace fields
      exact h
    have index : current.ifindex = d.ifindex := by
      have h := congrArg Device.ifindex fields
      exact h
    have name : current.ifname = d.ifname := by
      have h := congrArg Device.ifname fields
      exact h
    have generation : current.deviceUpdateGen = d.deviceUpdateGen + 1 := by
      have h := congrArg Device.deviceUpdateGen fields
      exact h
    have selected : current.peers[pid]? = some peer :=
      peerUpdatedDevice_peer (keyReadbackBase d key) pid p now
    have selection : selectsDevice middle current := by
      have original : selectsDevice entry d := pre.2.2
      simpa [selectsDevice, framed.2, index, name] using original
    obtain ⟨dump, out, rest, getRun, dumped, retained, socket⟩ := wgGetDevice_single pid current peer sock
      currentMembers selected noIps (by simpa [prefixSpace] using room) idle empty
      middle next ⟨device, framed.1, selection⟩
    have selector : byIndex d = byIndex current := by simp [byIndex, index]
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump, out), rest) =>
      Except.ok (((ret, dump), out), rest)) = _ at run
    rw [selector, getRun] at run
    cases run
    have attrs : deviceFixedAttrs current = deviceFixedAttrs (keyReadbackBase d key) := by
      have h := congrArg deviceFixedAttrs fields
      exact h
    have peerAttrs : peerFixedAttrs peer = peerFixedAttrs p := by
      rfl
    have json : singlePeerJson current peer = singlePeerJson (keyReadbackBase d key) p := by
      simp only [singlePeerJson, attrs, peerAttrs]
    refine ⟨?_, ?_, now, retained⟩
    · simp [code, dumped, json]
    · change final.nlSock7 = _
      simpa [completedSock, generation] using socket

end Leanux.Proofs.WG.Config
