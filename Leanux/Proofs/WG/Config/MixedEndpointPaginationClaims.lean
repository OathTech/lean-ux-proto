import Leanux.Proofs.WG.Config.EndpointPaginationCapacityFrames
import Leanux.Proofs.WG.Config.EndpointPaginationClaims
import Leanux.Proofs.WG.Config.MixedAttributeSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual mixed fwmark/scalar request followed by the actual finite
endpoint-aware IPv4 getter. The Device effect includes source-address clearing
and cache invalidation; JSON uses the actual peerFixedAttrs serializer. A
malformed second peer returns -EINVAL after committing the mark and selected
peer's scalar fields. Every reset-record Stop
remains a Stop; the reset timestamp is derived only from a normal setter run.
No callback-success, cache-reset or reference-readiness premise is added. -/
theorem mixed_fwmark_scalar_endpoint_pagination_get_after_set (d : Device) (mark : Nat) (key psk : Key)
    (interval : Nat) (bad : Bool) (pid : PeerId) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (listed : p.allowedipsList = ids) (fresh : endpointPaginationFresh d p ids)
    (readable : Ipv4Residents d nodes ids)
    (room : devicePrefixSpace d + max 168 (peerFixedSpace p + 32) ≤ NLMSG_GOODSIZE)
    (enough : endpointPaginationReceiveCount d p ids ≤ 4096)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0), .ok
          (suffixJson (mixedFwmarkBase d mark)
            {p with presharedKey := psk, persistentKeepaliveInterval := interval} nodes ids)) ∧
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
    have peerSpace : peerFixedSpace (mixedFwmarkPeer p psk interval reset) = peerFixedSpace p := by
      cases endpoint : p.endpoint <;> simp [peerFixedSpace,mixedFwmarkPeer,clearedSource,endpoint]
    have transferred := endpointPagination_spaces current d (mixedFwmarkPeer p psk interval reset) p
      prefixSpace peerSpace ids
    have currentReadable : Ipv4Residents current nodes ids := by
      have nodeMap : current.nodes = d.nodes := by
        have h := congrArg Device.nodes effect.1
        exact h
      intro id member
      simpa only [nodeMap] using readable id member
    obtain ⟨dump, out, rest, getRun, dumped, retained, socket⟩ :=
      endpointIpv4Pagination_returns pid current (mixedFwmarkPeer p psk interval reset) nodes ids sock
        members effect.2.1 listed (transferred.1.mpr fresh) currentReadable
        (by simpa only [prefixSpace,peerSpace] using room) idle empty
        (by simpa only [transferred.2] using enough)
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
      cases endpoint : p.endpoint <;> simp [peerFixedAttrs,mixedFwmarkPeer,clearedSource,endpoint]
    have json : suffixJson current (mixedFwmarkPeer p psk interval reset) nodes ids =
        suffixJson (mixedFwmarkBase d mark)
          {p with presharedKey := psk, persistentKeepaliveInterval := interval} nodes ids := by
      simp only [suffixJson, attrs, peerAttrs]
    refine ⟨?_, ?_, current, reset, retained, effect⟩
    · simp [code, dumped, json]
    · change final.nlSock7 = _
      change final.nlSock7 = socketReadbackFinal sock current at socket
      simpa [socketReadbackFinal, generation] using socket

end Leanux.Proofs.WG.Config
