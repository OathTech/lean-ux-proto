import Leanux.Proofs.WG.Config.EndpointRequestSource
import Leanux.Proofs.WG.Config.EndpointSetEffects
import Leanux.Proofs.WG.Config.WeightedPaginationCapacityFrames
import Leanux.Proofs.WG.Config.WeightedGetterClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise

/-- Actual endpoint set followed by the whole weighted getter. The effective
endpoint, rather than the supplied flowinfo unconditionally, determines the
serialized peer and all first-page capacities. Numeric later-peer rejection
retains the update; hidden reset-record Stops are not turned into returns. -/
theorem endpoint_weighted_get_after_set (d : Device) (key : Key) (a : EndpointAttr)
    (updateOnly bad : Bool) (pid : PeerId) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid])
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (nest : ids ≠ [] → devicePrefixSpace d + (peerFixedSpace (endpointApplied p a) + 4) ≤ NLMSG_GOODSIZE)
    (fresh : weightedGetterFresh d (endpointApplied p a) nodes ids)
    (within : weightedGetterReceives d (endpointApplied p a) nodes ids ≤ 4096)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (endpointDeviceAttrs d key a updateOnly bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0), .ok (jsonPaginationResult d (endpointApplied p a)
          (ids.map (fun id => dumpNodeJson (nodes id))))) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        ∃ reset, s.wg.device = some
          (endpointSetterDevice {d with deviceUpdateGen := d.deviceUpdateGen + 1} pid p a reset)) := by
  intro entry ambient result final after pre run
  change (((wgSetDevice (endpointDeviceAttrs d key a updateOnly bad)).run entry).run ambient >>=
    fun ((ret, middle), next) => ((wgGetDevice (byIndex d)).run middle).run next >>=
      fun ((dump, out), rest) => Except.ok (((ret, dump), out), rest)) = _ at run
  cases setRun : ((wgSetDevice (endpointDeviceAttrs d key a updateOnly bad)).run entry).run ambient with
  | error stop => rw [setRun] at run; cases run
  | ok output =>
    obtain ⟨⟨ret, middle⟩, next⟩ := output
    obtain ⟨code, reset, device, frame⟩ := setDevice_endpoint d key a updateOnly bad pid p sock
      entry.fixtureNetDevices found resident live bounded down entry ambient ret middle next
      ⟨pre.1, ⟨pre.2.1, rfl⟩, pre.2.2⟩ setRun
    let current := endpointSetterDevice {d with deviceUpdateGen := d.deviceUpdateGen + 1} pid p a reset
    let configured := endpointAttributePeer p a reset
    have fields := endpointSetter_fields {d with deviceUpdateGen := d.deviceUpdateGen + 1} pid p a reset
    have members : current.peerList = [pid] := (congrArg Device.peerList fields.1).trans peers
    have prefixSpace : devicePrefixSpace current = devicePrefixSpace d := by
      have h := congrArg devicePrefixSpace fields.1
      exact h
    have index : current.ifindex = d.ifindex := by
      have h := congrArg Device.ifindex fields.1
      exact h
    have name : current.ifname = d.ifname := by
      have h := congrArg Device.ifname fields.1
      exact h
    have generation : current.deviceUpdateGen = d.deviceUpdateGen + 1 := congrArg Device.deviceUpdateGen fields.1
    have nodeMap : current.nodes = d.nodes := by
      have h := congrArg Device.nodes fields.1
      exact h
    have attrs : deviceFixedAttrs current = deviceFixedAttrs d := by
      have h := congrArg deviceFixedAttrs fields.1
      exact h
    have peerAttrs : peerFixedAttrs configured = peerFixedAttrs (endpointApplied p a) := fields.2.2.2.1
    have peerSpace : peerFixedSpace configured = peerFixedSpace (endpointApplied p a) := fields.2.2.2.2
    have selection : selectsDevice middle current := by
      have selected : selectsDevice entry d := pre.2.2
      simpa [selectsDevice, frame.2, index, name] using selected
    have transferred := weightedPagination_spaces current d configured (endpointApplied p a)
      prefixSpace peerSpace nodes ids
    obtain ⟨dump, out, rest, getRun, dumped, retained, socket⟩ :=
      mixed_weighted_getter pid current configured nodes ids sock members fields.2.1
        (fields.2.2.1.trans listed) (by simpa only [nodeMap] using readable)
        (by simpa only [prefixSpace] using header)
        (by simpa only [prefixSpace, peerSpace] using nest)
        (transferred.1.mpr fresh) idle empty
        (by simpa only [transferred.2] using within)
        middle next ⟨device, frame.1, selection⟩
    have selector : byIndex d = byIndex current := by simp [byIndex, index]
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>=
      fun ((dump, out), rest) => Except.ok (((ret, dump), out), rest)) = _ at run
    rw [selector, getRun] at run
    cases run
    refine ⟨?_, ?_, reset, retained⟩
    · simp only [code, dumped, jsonPaginationResult, attrs, peerAttrs]
    · change final.nlSock7 = _
      change final.nlSock7 = socketReadbackFinal sock current at socket
      simpa [socketReadbackFinal, generation] using socket

end Leanux.Proofs.WG.Config
