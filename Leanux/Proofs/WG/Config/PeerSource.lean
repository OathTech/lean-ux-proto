import Leanux.WG.Netlink

/-! Local copy of the source factors reviewed on campaign 1 at c4ef635.
Kept here until its landing; no existing shared declaration is changed.

Low-dependency source factors for complete peer configuration. These are
literal original stages at the acquired-peer and attribute-update boundaries;
the whole source equation is definitional and preserves every return and Stop.
No lifetime or routing invariant enters this operational factor. -/
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

def peerConfigTailSource (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) : M Int := do
  let out (peer : Option PeerId) (ret : Int) : M Int := do
    peerPut peer
    _ ← (branch .peerZeroPsk a.presharedKey.isSome)
    return ret
  let mut ret : Int := 0
  if ← (branch .peerHasAips a.allowedIps.isSome) then
    for entry in a.allowedIps.getD [] do
      _ ← (branch .peerAipsIter true)
      match entry with
      | .malformed =>
        _ ← (branch .peerAipParseErr true)
        return ← out peer (-EINVAL)
      | .attrs ip =>
        _ ← (branch .peerAipParseErr false)
        ret ← setAllowedip pid ip
        if ← (branch .peerAipErr (ret < 0)) then return ← out peer ret
    _ ← (branch .peerAipsIter false)
  let running := (← getDev).running
  if ← (branch .peerHasKeepalive a.keepalive.isSome) then
    let interval := a.keepalive.getD 0
    let p ← getPeer pid
    let send ← WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running))
    setPeer pid {p with persistentKeepaliveInterval := interval}
    if ← branch .peerSendKeepalive send then sendKeepalive pid
  if ← (branch .peerRunning running) then sendStagedPackets pid
  out peer ret

def peerConfigUpdateSource (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) : M Int := do
  let out (peer : Option PeerId) (ret : Int) : M Int := do
    peerPut peer
    _ ← (branch .peerZeroPsk a.presharedKey.isSome)
    return ret
  if ← (branch .peerRemoveMe (flags &&& WGPEER_F_REMOVE_ME != 0)) then
    peerRemove peer
    return ← out peer 0
  if ← (branch .peerSetPsk psk.isSome) then
    setPeer pid { (← getPeer pid) with presharedKey := psk.getD [] }
  if ← (branch .peerHasEndpoint a.endpoint.isSome) then
    let some e := a.endpoint | (invariant "unreachable")
    if ← (WG.andM (branch .peerEndpointV4Len (e.len == 16)) (branch .peerEndpointV4Family (e.family == AF_INET))) then
      setPeerEndpoint pid {family := e.family, addr := e.addr, port := e.port}
    else if ← (WG.andM (branch .peerEndpointV6Len (e.len == 28)) (branch .peerEndpointV6Family (e.family == AF_INET6))) then
      setPeerEndpoint pid {family := e.family, addr := e.addr, port := e.port, scope := e.scope, flowinfo := e.flowinfo}
  if ← (branch .peerReplaceAips (flags &&& WGPEER_F_REPLACE_ALLOWEDIPS != 0)) then removeByPeer pid
  peerConfigTailSource a peer pid

def setPeerCmdSource (a : PeerAttrs) : M Int := do
  let out (peer : Option PeerId) (ret : Int) : M Int := do
    peerPut peer
    _ ← (branch .peerZeroPsk a.presharedKey.isSome)
    return ret
  if !(← (WG.andM (branch .peerHasPubkey a.publicKey.isSome) (branch .peerPubkeyLen true))) then
    return ← out none (-EINVAL)
  let some publicKey := a.publicKey | (invariant "unreachable")
  let psk ← do
    if ← (WG.andM (branch .peerHasPsk a.presharedKey.isSome) (branch .peerPskLen true)) then pure a.presharedKey
    else pure none
  let mut flags : UInt32 := 0
  if ← (branch .peerHasFlags a.flags.isSome) then flags := a.flags.getD 0
  if ← (branch .peerBadFlags (flags &&& ~~~WGPEER_F_ALL != 0)) then return ← out none (-EOPNOTSUPP)
  if ← (branch .peerHasProtocol a.protocolVersion.isSome) then
    if ← (branch .peerBadProtocol (a.protocolVersion != some 1)) then return ← out none (-EPFNOSUPPORT)
  let mut peer ← pubkeyLookup publicKey
  if ← (branch .peerNotFound peer.isNone) then
    if ← (branch .peerNewRemoveOrUpdate (flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) != 0)) then
      return ← out none 0
    flags := flags &&& ~~~WGPEER_F_REPLACE_ALLOWEDIPS
    let id := (← getDev).staticIdentity
    if ← (WG.andM (branch .peerSelfHasIdentity id.hasIdentity) (branch .peerSelfKeyMatch (publicKey == id.staticPublic))) then
      return ← out none 0
    match ← peerCreate publicKey psk with
    | .error e =>
      _ ← (branch .peerCreateErr true)
      return ← out none e
    | .ok pid =>
      _ ← (branch .peerCreateErr false)
      peerGet pid
      peer := some pid
  let some pid := peer | (invariant "set_peer without a peer")
  peerConfigUpdateSource a peer flags psk pid

theorem setPeerCmd_source (a : PeerAttrs) : setPeerCmdSource a = setPeerCmd a := by
  rfl

end Leanux.Proofs.WG.Config
