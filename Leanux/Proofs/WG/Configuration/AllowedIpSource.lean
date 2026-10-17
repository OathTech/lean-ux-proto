import Leanux.Proofs.WG.Configuration.PeerSource

/-! Literal tail cut at the end of the allowed-IP loop. Early error cleanup
stays inside the loop; the continuation is reached only after normal exhaustion. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG
universe u

/-- The original loop with its recorded decision, mutation, cleanup and final
continuation supplied by the caller. Early errno returns still run cleanup;
a Stop from any supplied operation skips the remaining continuation. -/
def peerAllowedIpsWith {m : Type → Type u} [Monad m]
    (record : Decision → Bool → m Bool) (allowed : AllowedIpAttrs → m Int)
    (out : Int → m Int) (a : PeerAttrs) (next : Int → m Int) : m Int := do
  let mut ret : Int := 0
  if ← record .peerHasAips a.allowedIps.isSome then
    for entry in a.allowedIps.getD [] do
      _ ← record .peerAipsIter true
      match entry with
      | .malformed =>
        _ ← record .peerAipParseErr true
        return ← out (-EINVAL)
      | .attrs ip =>
        _ ← record .peerAipParseErr false
        ret ← allowed ip
        if ← record .peerAipErr (ret < 0) then return ← out ret
    _ ← record .peerAipsIter false
  next ret

def peerAllowedIpsSource [Monad m] [MonadLiftT WG.M m] [MonadLiftT AmbientM m]
    (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (next : Int → m Int) : m Int :=
  peerAllowedIpsWith (fun d b => branch d b) (fun ip => liftM (setAllowedip pid ip))
    (fun ret => do
      peerPut peer
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure ret) a next

def peerTailFinishSource (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) : WG.M Int := do
  let out (peer : Option PeerId) (ret : Int) : WG.M Int := do
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
