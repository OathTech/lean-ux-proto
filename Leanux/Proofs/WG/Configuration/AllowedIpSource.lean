import Leanux.Proofs.WG.Configuration.PeerSource

/-! Literal tail cut at the end of the allowed-IP loop. Early error cleanup
stays inside the loop; the continuation is reached only after normal exhaustion. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG

def peerAllowedIpsSource (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (next : Int → M Int) : M Int := do
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
  next ret

def peerTailFinishSource (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) : M Int := do
  let out (peer : Option PeerId) (ret : Int) : M Int := do
    peerPut peer
    _ ← branch .peerZeroPsk a.presharedKey.isSome
    return ret
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


theorem peerConfigTailSource_factor (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    peerConfigTailSource a peer pid =
      peerAllowedIpsSource a peer pid (peerTailFinishSource a peer pid) := by
  rfl

end Leanux.Proofs.WG.Configuration
