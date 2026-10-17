import Leanux.Proofs.WG.Config.MixedAttributeSource
import Leanux.Proofs.WG.Config.ClaimView

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

/-- Actual mixed-attribute set/get on the finite single-peer getter domain.
A malformed second peer returns EINVAL after committing fwmark and scalars.
This normal-return claim includes arbitrary reset-record inputs: an actual
prefix Stop prevents the getter. Values here are the mirror's JSON values. -/
theorem mixed_fwmark_scalar_get_after_set (d : Device) (mark : Nat) (key psk : Key)
    (interval : Nat) (bad : Bool) (pid : PeerId) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid]) (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (noIps : p.allowedipsList = [])
    (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0), .ok
          (singlePeerJson (mixedFwmarkBase d mark)
            {p with presharedKey := psk, persistentKeepaliveInterval := interval})) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        ∃ current reset, s.wg.device = some current ∧
          MixedFwmarkEffect d mark pid p psk interval reset current) := by
  intro entry ambient result final after pre run
  change (((wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)).run entry).run ambient >>=
    fun ((ret, middle), next) => ((wgGetDevice (byIndex d)).run middle).run next >>=
      fun ((dump, out), rest) => Except.ok (((ret, dump), out), rest)) = _ at run
  cases setRun : ((wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)).run entry).run ambient with
  | error stop => rw [setRun] at run; cases run
  | ok out =>
    obtain ⟨⟨ret, middle⟩, next⟩ := out
    have effects := setDevice_mixed_fwmark_scalars d mark key psk interval bad pid p
      sock entry.fixtureNetDevices peers net found resident live bounded down
      entry ambient ret middle next ⟨pre.1, ⟨pre.2.1, rfl⟩, pre.2.2⟩ setRun
    obtain ⟨code, framed, current, reset, device, effect⟩ := effects
    have members : current.peerList = [pid] := by
      have h := congrArg Device.peerList effect.1
      change current.peerList = d.peerList at h
      exact h.trans peers
    have prefixSpace : devicePrefixSpace current = devicePrefixSpace d := by
      have h := congrArg devicePrefixSpace effect.1
      exact h
    have index : current.ifindex = d.ifindex := by
      have h := congrArg Device.ifindex effect.1
      exact h
    have name : current.ifname = d.ifname := by
      have h := congrArg Device.ifname effect.1
      exact h
    have generation : current.deviceUpdateGen = d.deviceUpdateGen + 1 :=
      congrArg Device.deviceUpdateGen effect.1
    have selection : selectsDevice middle current := by
      have selected : selectsDevice entry d := pre.2.2
      simpa [selectsDevice, framed.2, index, name] using selected
    obtain ⟨dump, out, rest, getRun, dumped, retained, socket⟩ :=
      wgGetDevice_single pid current (mixedFwmarkPeer p psk interval reset) sock
        members effect.2.1 noIps (by simpa [prefixSpace] using room) idle empty
        middle next ⟨device, framed.1, selection⟩
    have selector : byIndex d = byIndex current := by simp [byIndex, index]
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>=
      fun ((dump, out), rest) => Except.ok (((ret, dump), out), rest)) = _ at run
    rw [selector, getRun] at run
    cases run
    have attrs : deviceFixedAttrs current = deviceFixedAttrs (mixedFwmarkBase d mark) := by
      have h := congrArg deviceFixedAttrs effect.1
      exact h
    have peerAttrs : peerFixedAttrs (mixedFwmarkPeer p psk interval reset) =
        peerFixedAttrs {p with presharedKey := psk, persistentKeepaliveInterval := interval} := by
      cases endpoint : p.endpoint <;> simp [peerFixedAttrs, mixedFwmarkPeer, clearedSource, endpoint]
    have json : singlePeerJson current (mixedFwmarkPeer p psk interval reset) =
        singlePeerJson (mixedFwmarkBase d mark)
          {p with presharedKey := psk, persistentKeepaliveInterval := interval} := by
      simp only [singlePeerJson, attrs, peerAttrs]
    refine ⟨?_, ?_, current, reset, retained, effect⟩
    · simp [code, dumped, json]
    · change final.nlSock7 = _
      simpa [completedSock, generation] using socket

end Leanux.Proofs.WG.Config
