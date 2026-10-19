import Leanux.Proofs.WG.Progress.AllowedFiniteSource
import Leanux.Proofs.WG.Progress.KeepaliveFiniteSource
import Leanux.Proofs.WG.Configuration.AllowedIpSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.ConfigurationFinite
open Leanux Leanux.WG

/-- Exact attribute validation and insertion call sites, without a trie copy. -/
def allowedWith (insert : Nat → Nat → Nat → PeerId → WG.M Int)
    (pid : PeerId) (ip : AllowedIpAttrs) : WG.M Int := do
  if ← WG.orM (branch .aipNoFamily ip.family.isNone) (WG.orM (branch .aipNoAddr ip.addr.isNone) (branch .aipNoCidr ip.cidr.isNone)) then
    return -EINVAL
  let family := ip.family.getD 0
  let addr := ip.addr.getD 0
  let cidr := ip.cidr.getD 0
  if ← WG.andM (branch .aipV4Family (family == AF_INET))
      (WG.andM (branch .aipV4Cidr (cidr ≤ 32)) (branch .aipV4Len (ip.addrLen == 4))) then
    return ← insert 4 addr cidr pid
  if ← WG.andM (branch .aipV6Family (family == AF_INET6))
      (WG.andM (branch .aipV6Cidr (cidr ≤ 128)) (branch .aipV6Len (ip.addrLen == 16))) then
    return ← insert 6 addr cidr pid
  return -EINVAL

theorem allowed_factor (pid : PeerId) (ip : AllowedIpAttrs) :
    WG.setAllowedip pid ip = allowedWith WG.insert pid ip := rfl

def allowed (pid : PeerId) (ip : AllowedIpAttrs) : WG.M Int :=
  allowedWith AllowedFinite.insert pid ip

theorem allowed_source (pid : PeerId) (ip : AllowedIpAttrs) :
    WG.setAllowedip pid ip = allowed pid ip := by
  rw [allowed_factor]
  unfold allowed
  rw [funext fun family => funext fun addr => funext fun cidr =>
    funext (AllowedFinite.insert_source family addr cidr)]

/-- Only the concrete keepalive call is abstracted; all scalar writes, staging
and caller-reference payment retain their original order and failures. -/
def finishWith (keepalive : PeerId → WG.M Unit)
    (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) : WG.M Int := do
  let out (peer : Option PeerId) (ret : Int) : WG.M Int := do
    peerPut peer
    _ ← branch .peerZeroPsk a.presharedKey.isSome
    return ret
  let running := (← getDev).running
  if ← branch .peerHasKeepalive a.keepalive.isSome then
    let interval := a.keepalive.getD 0
    let p ← getPeer pid
    let send ← WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running))
    setPeer pid {p with persistentKeepaliveInterval := interval}
    if ← branch .peerSendKeepalive send then keepalive pid
  if ← branch .peerRunning running then sendStagedPackets pid
  out peer ret

theorem finish_factor (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Configuration.peerTailFinishSource a peer pid ret = finishWith WG.sendKeepalive a peer pid ret := rfl

def finish (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) : WG.M Int :=
  finishWith HandshakeFinite.keepalive a peer pid ret

theorem finish_source (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Configuration.peerTailFinishSource a peer pid ret = finish a peer pid ret := by
  rw [finish_factor]
  unfold finish
  rw [funext HandshakeFinite.keepalive_source]

end Leanux.Proofs.WG.Progress.ConfigurationFinite
