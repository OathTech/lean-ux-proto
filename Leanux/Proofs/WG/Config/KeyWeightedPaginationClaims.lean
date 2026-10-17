import Leanux.Proofs.WG.Config.WeightedPaginationCapacityFrames
import Leanux.Proofs.WG.Config.WeightedGetterClaims
import Leanux.Proofs.WG.Config.KeyReadbackSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Actual established-identity rotation followed by finite mixed-width
weighted pagination. The effective installed identity determines capacities and serialized keys,
including clamping and the absence of identity attributes for a null key.
Expiry time and final ordered peer/keypair writes come from the actual setter;
clock and key-reference Stops remain outside this normal-return contract. -/
theorem rotation_weighted_pagination_get_after_set (d : Device) (key : Key) (pid : PeerId) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (established : d.staticIdentity.hasIdentity = true)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key)
    (members : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids)
    (fresh : weightedGetterFresh (keyReadbackBase d key) p nodes ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace (keyReadbackBase d key) + 168 ≤ NLMSG_GOODSIZE)
    (nest : ids ≠ [] → devicePrefixSpace (keyReadbackBase d key) + (peerFixedSpace p + 4) ≤ NLMSG_GOODSIZE)
    (enough : weightedGetterReceives (keyReadbackBase d key) p nodes ids ≤ 4096)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (privateKeyAttrs d key)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = (0, .ok (jsonPaginationResult (keyReadbackBase d key) p (ids.map (fun id => dumpNodeJson (nodes id))))) ∧
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
    have peerSpace : peerFixedSpace peer = peerFixedSpace p := rfl
    have transferred := weightedPagination_spaces current (keyReadbackBase d key) peer p
      prefixSpace peerSpace nodes ids
    have currentReadable : ∀ id ∈ ids, current.nodes[id]? = some (nodes id) := by
      have nodeMap : current.nodes = d.nodes := by
        have h := congrArg Device.nodes fields
        exact h
      intro id member
      simpa only [nodeMap] using readable id member
    obtain ⟨dump, out, rest, getRun, dumped, retained, socket⟩ :=
      mixed_weighted_getter pid current peer nodes ids sock currentMembers selected listed
        currentReadable (by simpa only [prefixSpace] using header)
        (by simpa only [prefixSpace,peerSpace] using nest)
        (transferred.1.mpr fresh) idle empty
        (by simpa only [transferred.2] using enough)
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
    have json : jsonPaginationResult current peer (ids.map (fun id => dumpNodeJson (nodes id))) = jsonPaginationResult (keyReadbackBase d key) p (ids.map (fun id => dumpNodeJson (nodes id))) := by
      simp only [jsonPaginationResult, attrs, peerAttrs]
    refine ⟨?_, ?_, now, retained⟩
    · simp [code, dumped, json]
    · change final.nlSock7 = _
      change final.nlSock7 = socketReadbackFinal sock current at socket
      simpa [socketReadbackFinal, generation] using socket

end Leanux.Proofs.WG.Config
