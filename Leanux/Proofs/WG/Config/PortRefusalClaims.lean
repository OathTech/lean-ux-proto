import Leanux.Proofs.WG.Config.PortRefusalSource
import Leanux.Proofs.WG.Config.Getter
import Leanux.Proofs.WG.Config.ClaimView

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

/-- A normal mixed request that reaches a nonzero port collision retains its
earlier mark/generation and source-cache writes, while all later attributes are
bypassed. No reset-record or listed-peer readiness is assumed. -/
theorem mixed_port_refusal (d : Device) (mark port : Nat)
    (flags : Option UInt32) (key : Option Key) (peers : Option (List PeerEntry))
    (bound : Nat → Bool) (supported : flags.getD 0 &&& ~~~WGDEVICE_F_ALL = 0)
    (net : d.creatingNet = true) (running : d.running = true)
    (nonzero : port ≠ 0) (changed : d.incomingPort ≠ port)
    (collision : (bound port || d.sock4 == some port || d.sock6 == some port) = true) :
    Campaign2.Ensures (wgSetDevice (portRefusalAttrs d mark port flags key peers))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧ s.wg.portBound = bound)
      (fun ret s => ret = -EADDRINUSE ∧
        s.wg.device.map withoutPeers = some (withoutPeers (portRefusalBase d mark)) ∧
        ClaimView.clearedPeers d s.wg.toCore d.peerList) := by
  intro g ambient value final after pre run
  have post := setDevice_mixed_port_refused d mark port flags key peers bound
    g.nlSock7 g.fixtureNetDevices supported net running nonzero changed collision
    g ambient value final after ⟨pre.1, pre.2.1, pre.2.2, rfl, rfl⟩ run
  exact ⟨post.1, post.2.2⟩

/-- The actual getter observes the retained prefix of a failed mixed request.
This finite dump domain allows a running device and arbitrary later attributes;
hidden reset Stops prevent the sequence rather than becoming normal refusals.
The equality concerns the mirror's JSON, not byte-level attribute encoding. -/
theorem mixed_port_refusal_get_after_set (d : Device) (mark port : Nat)
    (flags : Option UInt32) (key : Option Key) (peers : Option (List PeerEntry))
    (bound : Nat → Bool) (pid : PeerId) (p : Peer) (sock : NlSock)
    (supported : flags.getD 0 &&& ~~~WGDEVICE_F_ALL = 0)
    (net : d.creatingNet = true) (running : d.running = true)
    (nonzero : port ≠ 0) (changed : d.incomingPort ≠ port)
    (collision : (bound port || d.sock4 == some port || d.sock6 == some port) = true)
    (members : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (noIps : p.allowedipsList = [])
    (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (portRefusalAttrs d mark port flags key peers)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.portBound = bound ∧ s.wg.nlSock7 = sock)
      (fun result s =>
        result = (-EADDRINUSE, .ok (singlePeerJson (portRefusalBase d mark) p)) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        s.wg.device.map withoutPeers = some (withoutPeers (portRefusalBase d mark)) ∧
        ClaimView.clearedPeers d s.wg.toCore d.peerList) := by
  intro entry ambient result final after pre run
  change (((wgSetDevice (portRefusalAttrs d mark port flags key peers)).run entry).run ambient >>= fun ((ret, middle), next) =>
    ((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump, out), rest) =>
      Except.ok (((ret, dump), out), rest)) = _ at run
  cases setRun : ((wgSetDevice (portRefusalAttrs d mark port flags key peers)).run entry).run ambient with
  | error stop => rw [setRun] at run; cases run
  | ok out =>
    obtain ⟨⟨ret, middle⟩, next⟩ := out
    obtain ⟨code, framed, outer, clears⟩ := setDevice_mixed_port_refused d mark port flags key peers
      bound sock entry.fixtureNetDevices supported net running nonzero changed collision
      entry ambient ret middle next ⟨pre.1, pre.2.1, pre.2.2.1, pre.2.2.2, rfl⟩ setRun
    obtain ⟨current, device, same⟩ := Option.map_eq_some_iff.mp outer
    obtain ⟨old, reset, oldResident, cleared⟩ :=
      (show ∃ old reset, d.peers[pid]? = some old ∧
        (middle.dev.bind fun d => d.peers[pid]?) = some (clearedSource old reset) by
        simpa [clearedPeers, members] using clears pid)
    rw [resident] at oldResident
    cases oldResident
    have selected : current.peers[pid]? = some (clearedSource p reset) := by
      simpa [device] using cleared
    have currentMembers : current.peerList = [pid] := by
      have h := congrArg Device.peerList same
      exact h.trans members
    have prefixSpace : devicePrefixSpace current = devicePrefixSpace d := by
      have h := congrArg devicePrefixSpace same
      exact h
    have index : current.ifindex = d.ifindex := by
      simpa [withoutPeers, portRefusalBase] using congrArg Device.ifindex same
    have name : current.ifname = d.ifname := by
      simpa [withoutPeers, portRefusalBase] using congrArg Device.ifname same
    have generation : current.deviceUpdateGen = d.deviceUpdateGen + 1 := congrArg Device.deviceUpdateGen same
    have selection : selectsDevice middle current := by
      have original : selectsDevice entry d := pre.2.1
      simpa [selectsDevice, framed.2, index, name] using original
    obtain ⟨dump, out, rest, getRun, dumped, retained, socket⟩ := wgGetDevice_single pid current
      (clearedSource p reset) sock currentMembers selected noIps
      (by simpa [prefixSpace] using room) idle empty middle next ⟨device, framed.1, selection⟩
    have selector : byIndex d = byIndex current := by simp [byIndex, index]
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump, out), rest) =>
      Except.ok (((ret, dump), out), rest)) = _ at run
    rw [selector, getRun] at run
    cases run
    have attrs : deviceFixedAttrs current = deviceFixedAttrs (portRefusalBase d mark) :=
      by
        have h := congrArg deviceFixedAttrs same
        exact h
    have peerAttrs : peerFixedAttrs (clearedSource p reset) = peerFixedAttrs p := by
      cases endpoint : p.endpoint <;> simp [peerFixedAttrs, clearedSource, endpoint]
    have json : singlePeerJson current (clearedSource p reset) =
        singlePeerJson (portRefusalBase d mark) p := by simp only [singlePeerJson, attrs, peerAttrs]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [code, dumped, json]
    · change final.nlSock7 = _
      simpa [completedSock, generation] using socket
    · change final.dev.map withoutPeers = _
      simpa [retained] using congrArg some same
    · change clearedPeers d final d.peerList
      simpa only [clearedPeers, retained, device] using clears

end Leanux.Proofs.WG.Config
