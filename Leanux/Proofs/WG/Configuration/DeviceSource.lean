import Leanux.WG.Netlink

/-! Original-only cuts at the device private-key and peer-list continuations.
The whole-source equation is unconditional, including malformed attributes and
missing devices. No proof observer or routing representation is imported. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG
set_option maxHeartbeats 1000000

def devicePeersSource (a : DeviceAttrs) : WG.M Int := do
  let zero (ret : Int) : WG.M Int := do
    _ ← branch .setDevZeroKey a.privateKey.isSome   -- memzero_explicit
    return ret
  if ← branch .setDevHasPeers a.peers.isSome then
    for entry in a.peers.getD [] do
      _ ← branch .setDevPeersIter true
      match entry with
      | .malformed =>   -- nla_parse_nested: NLA_F_NESTED missing, -EINVAL
        _ ← branch .setDevParseErr true
        return ← zero (-EINVAL)
      | .attrs p =>
        _ ← branch .setDevParseErr false
        let ret ← setPeerCmd p
        if ← branch .setDevSetPeerErr (ret < 0) then return ← zero ret
    _ ← branch .setDevPeersIter false
  zero 0

def deviceKeySource (a : DeviceAttrs) : WG.M Int := do
  if ← WG.andM (branch .setDevHasPrivateKey a.privateKey.isSome) (branch .setDevPrivateKeyLen true) then
    let some key := a.privateKey | invariant "unreachable"
    -- `!crypto_memneq(static_private, private_key)`: the stored key is clamped
    if !(← branch .setDevKeyUnchanged ((← getDev).staticIdentity.staticPrivate == key)) then
      -- remove the peer whose public key the device is about to take
      let (pub, ok) ← generatePublic key
      if ← branch .setDevGenPublic ok then
        let some pub := pub | invariant "a generated public key without a write"
        let peer ← pubkeyLookup pub
        if ← branch .setDevOldPeer peer.isSome then
          peerPut peer
          peerRemove peer
      let d ← getDev
      let sendStaged ← WG.andM (branch .setDevSendStagedNoIdentity !d.staticIdentity.hasIdentity)
        (branch .setDevSendStagedRunning d.running)
      setStaticIdentityPrivateKey key
      let hasIdentity := (← getDev).staticIdentity.hasIdentity
      let sendStaged ← WG.andM (branch .setDevSendStagedKept sendStaged) (branch .setDevSendStagedHasIdentity hasIdentity)
      cookiePrecomputeDeviceKeys
      for pid in (← getDev).peerList do
        _ ← branch .setDevKeyPeerIter true
        precomputeStaticStatic pid
        expireCurrentPeerKeypairs pid
        if ← branch .setDevSendStagedPeer sendStaged then sendStagedPackets pid
      _ ← branch .setDevKeyPeerIter false
  devicePeersSource a

def deviceUpdateSource (a : DeviceAttrs) (flags : UInt32) : WG.M Int := do
  let zero (ret : Int) : WG.M Int := do
    _ ← branch .setDevZeroKey a.privateKey.isSome   -- memzero_explicit
    return ret
  modifyDev fun d => { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
  if ← branch .setDevFwmark a.fwmark.isSome then
    modifyDev fun d => { d with fwmark := a.fwmark.getD 0 }
    for pid in (← getDev).peerList do
      _ ← branch .setDevFwmarkPeerIter true
      clearPeerEndpointSrc pid
    _ ← branch .setDevFwmarkPeerIter false
  if ← branch .setDevPort a.listenPort.isSome then
    let ret ← setPort (a.listenPort.getD 0)
    if ← branch .setDevPortErr (ret != 0) then return ← zero ret
  if ← branch .setDevReplacePeers (flags &&& WGDEVICE_F_REPLACE_PEERS != 0) then peerRemoveAll
  deviceKeySource a

def wgSetDeviceSource (a : DeviceAttrs) : WG.M Int := do
  let zero (ret : Int) : WG.M Int := do
    _ ← branch .setDevZeroKey a.privateKey.isSome   -- memzero_explicit
    return ret
  let wg ← lookupInterface a.device
  if ← branch .setDevLookupErr (wg matches .error _) then
    let .error e := wg | invariant "unreachable"
    return ← zero e
  let mut flags : UInt32 := 0
  if ← branch .setDevHasFlags a.flags.isSome then flags := a.flags.getD 0
  if ← branch .setDevBadFlags (flags &&& ~~~WGDEVICE_F_ALL != 0) then return ← zero (-EOPNOTSUPP)
  if ← WG.orM (branch .setDevHasPort a.listenPort.isSome) (branch .setDevHasFwmark a.fwmark.isSome) then
    -- W8: `!net` once the creating namespace exited (netlink.c:517); the
    -- capability half is constant true on this config (section 2.2)
    let denied ← WG.orM (branch .setDevNoNet !(← getDev).creatingNet) (branch .setDevNotCapable false)
    if ← branch .setDevPermErr denied then return ← zero (-EPERM)
  deviceUpdateSource a flags

theorem wgSetDevice_source (a : DeviceAttrs) : wgSetDeviceSource a = wgSetDevice a := rfl

end Leanux.Proofs.WG.Configuration
